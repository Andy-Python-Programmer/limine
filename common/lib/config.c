#include <stddef.h>
#include <stdbool.h>
#include <lib/config.h>
#include <lib/libc.h>
#include <lib/misc.h>
#include <lib/readline.h>
#include <mm/pmm.h>
#include <fs/file.h>
#include <lib/print.h>
#include <pxe/tftp.h>
#include <crypt/blake2b.h>
#include <sys/cpu.h>

#define CONFIG_B2SUM_SIGNATURE "++CONFIG_B2SUM_SIGNATURE++"
#define CONFIG_B2SUM_EMPTY "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"

const char *config_b2sum = CONFIG_B2SUM_SIGNATURE CONFIG_B2SUM_EMPTY;

static bool config_get_entry_name(char *ret, size_t index, size_t limit);
static char *config_get_entry(size_t *size, size_t index);

#define SEPARATOR '\n'

bool config_ready = false;
no_unwind bool bad_config = false;

static char *config_addr;

int init_config_disk(struct volume *part) {
    struct file_handle *f;

    bool old_cif = case_insensitive_fopen;
    case_insensitive_fopen = true;
    if ((f = fopen(part, "/limine.cfg")) == NULL
     && (f = fopen(part, "/limine/limine.cfg")) == NULL
     && (f = fopen(part, "/boot/limine.cfg")) == NULL
     && (f = fopen(part, "/boot/limine/limine.cfg")) == NULL
     && (f = fopen(part, "/EFI/BOOT/limine.cfg")) == NULL) {
        case_insensitive_fopen = old_cif;
        return -1;
    }
    case_insensitive_fopen = old_cif;

    size_t config_size = f->size + 2;
    config_addr = ext_mem_alloc(config_size);

    fread(f, config_addr, 0, f->size);

    fclose(f);

    return init_config(config_size);
}

#define NOT_CHILD      (-1)
#define DIRECT_CHILD   0
#define INDIRECT_CHILD 1

static int is_child(char *buf, size_t limit,
                    size_t current_depth, size_t index) {
    if (!config_get_entry_name(buf, index, limit))
        return NOT_CHILD;
    if (strlen(buf) < current_depth + 1)
        return NOT_CHILD;
    for (size_t j = 0; j < current_depth; j++)
        if (buf[j] != ':')
            return NOT_CHILD;
    if (buf[current_depth] == ':')
        return INDIRECT_CHILD;
    return DIRECT_CHILD;
}

static bool is_directory(char *buf, size_t limit,
                         size_t current_depth, size_t index) {
    switch (is_child(buf, limit, current_depth + 1, index + 1)) {
        default:
        case NOT_CHILD:
            return false;
        case INDIRECT_CHILD:
            bad_config = true;
            panic(true, "config: Malformed config file. Parentless child.");
        case DIRECT_CHILD:
            return true;
    }
}

static struct menu_entry *create_menu_tree(struct menu_entry *parent,
                                           size_t current_depth, size_t index) {
    struct menu_entry *root = NULL, *prev = NULL;

    for (size_t i = index; ; i++) {
        static char name[64];

        switch (is_child(name, 64, current_depth, i)) {
            case NOT_CHILD:
                return root;
            case INDIRECT_CHILD:
                continue;
            case DIRECT_CHILD:
                break;
        }

        struct menu_entry *entry = ext_mem_alloc(sizeof(struct menu_entry));

        if (root == NULL)
            root = entry;

        config_get_entry_name(name, i, 64);

        bool default_expanded = name[current_depth] == '+';

        strcpy(entry->name, name + current_depth + default_expanded);
        entry->parent = parent;

        size_t entry_size;
        char *config_entry = config_get_entry(&entry_size, i);
        entry->body = ext_mem_alloc(entry_size + 1);
        memcpy(entry->body, config_entry, entry_size);
        entry->body[entry_size] = 0;

        if (is_directory(name, 64, current_depth, i)) {
            entry->sub = create_menu_tree(entry, current_depth + 1, i + 1);
            entry->expanded = default_expanded;
        }

        char *comment = config_get_value(entry->body, 0, "COMMENT");
        if (comment != NULL) {
            entry->comment = comment;
        }

        if (prev != NULL)
            prev->next = entry;
        prev = entry;
    }
}

struct menu_entry *menu_tree = NULL;

bool isalpha(char c) {
	return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z');
}

bool isdigit(char c) {
	return (c >= '0' && c <= '9');
}

bool isalnum(char c) {
    return isalpha(c) || isdigit(c);
}

char *strchr(const char *string, int c) {
    do {
        if (*string == c) return (char *)string;
    } while (*string++);

    return NULL;
}

char *string_new() {
    char *ret = (char *)ext_mem_alloc(sizeof(char));
    *ret = 0;
    return ret;
}

void string_push(char **self, char *value) {
    size_t old_len = strlen(*self);
    size_t value_len = strlen(value);
    
    char *ret = (char*)ext_mem_alloc(old_len + value_len + 1);

    memcpy(ret, *self, old_len);
    memcpy(ret + old_len, value, value_len);
    ret[old_len + value_len] = 0;

    *self = ret;
}

struct macro {
    char name[4096];
    char value[4096];
    struct macro *next;
};

struct preprocessor_state {
    char *target;
    char *result;
    struct macro *macros;
};

bool preprocess_eat(struct preprocessor_state *state, char token) {
    do {
        char tok = *state->target;
        char c[] = { tok, 0 };

        if (tok == token) {
            state->target++;
            return true;
        }

        string_push(&state->result, c);
    } while (*(state->target)++);

    return false;
}

char *preprocess_ident(struct preprocessor_state *state) {
    char *ident = state->target;
    while (state->target[0]) {
        char token = state->target[0];
        if (isalnum(token) || (token & 0x80) || token == '_' || token == '$' || token == '/' || token == ':' || token == '.') {
            state->target++;
            continue;
        }

        break;
    }

    size_t ident_len = state->target - ident;
    if (ident_len == 0) {
        return NULL;
    }

    char *ident_str = (char *)ext_mem_alloc(ident_len + 1);
    memcpy(ident_str, ident, ident_len);
    ident_str[ident_len] = 0;

    return ident_str;
}

/// The caller is responsible for deallocating the returned string (via `pmm_free`).
char *preprocess(char *target) {
    size_t target_len = strlen(target);
    struct preprocessor_state state = {
        .target = target,
        .result = string_new(),
        .macros = ext_mem_alloc(sizeof(struct macro))
    };

    strcpy(state.macros->name, "ARCH");
    strcpy(state.macros->value, "x86_64");
    state.macros->next = NULL;

    struct macro *current_macro = state.macros;

    do {
        if (!preprocess_eat(&state, '$')) {
            continue;
        }

        char *macro_name = preprocess_ident(&state);
        if (macro_name) {
            preprocess_eat(&state, '(');
            char *macro_arg = preprocess_ident(&state);
            preprocess_eat(&state, ')');

            if (!strcmp(macro_name, "INCLUDE")) {
                
            } else {
                panic(true, "config: Unknown macro: %s\n", macro_name);
            }
        } else {
            preprocess_eat(&state, '{');
            char *macro_name = preprocess_ident(&state);
            preprocess_eat(&state, '}');

            if (state.target[0] == '=') {
                // We are defining a macro.
                preprocess_eat(&state, '=');
                char *macro_value = preprocess_ident(&state);
                struct macro *macro = ext_mem_alloc(sizeof(struct macro));

                strcpy(macro->name, macro_name);
                strcpy(macro->value, macro_value);
                macro->next = NULL;

                current_macro->next = macro;
                current_macro = macro;
            } else {
                // We are using a macro.
                struct macro *macro = state.macros;
                while (macro) {
                    if (!strcmp(macro->name, macro_name)) {
                        string_push(&state.result, macro->value);
                        break;
                    }

                    macro = macro->next;
                }
            }
        }
    } while (*state.target);

    return state.result;
}

int init_config(size_t config_size) {
    config_b2sum += sizeof(CONFIG_B2SUM_SIGNATURE) - 1;

    if (memcmp((void *)config_b2sum, CONFIG_B2SUM_EMPTY, 128) != 0) {
        uint8_t out_buf[BLAKE2B_OUT_BYTES];
        blake2b(out_buf, config_addr, config_size - 2);
        uint8_t hash_buf[BLAKE2B_OUT_BYTES];

        for (size_t i = 0; i < BLAKE2B_OUT_BYTES; i++) {
            hash_buf[i] = digit_to_int(config_b2sum[i * 2]) << 4 | digit_to_int(config_b2sum[i * 2 + 1]);
        }

        if (memcmp(hash_buf, out_buf, BLAKE2B_OUT_BYTES) != 0) {
            panic(false, "!!! CHECKSUM MISMATCH FOR CONFIG FILE !!!");
        }
    }

    // add trailing newline if not present
    config_addr[config_size - 2] = '\n';

    // remove windows carriage returns and spaces at the start of lines, if any
    for (size_t i = 0; i < config_size; i++) {
        size_t skip = 0;
        while ((config_addr[i + skip] == '\r')
            || ((!i || config_addr[i - 1] == '\n')
             && (config_addr[i + skip] == ' ' || config_addr[i + skip] == '\t'))) {
            skip++;
        }
        if (skip) {
            for (size_t j = i; j < config_size - skip; j++)
                config_addr[j] = config_addr[j + skip];
            config_size -= skip;
        }
    }

    char *new_config = preprocess(config_addr);
    config_addr = new_config;
    config_size = strlen(config_addr);

    config_ready = true;

    menu_tree = create_menu_tree(NULL, 1, 0);

    size_t s;
    char *c = config_get_entry(&s, 0);
    while (*c != ':') {
        c--;
    }
    if (c > config_addr) {
        c[-1] = 0;
    }

    return 0;
}

static bool config_get_entry_name(char *ret, size_t index, size_t limit) {
    if (!config_ready)
        return false;

    char *p = config_addr;

    for (size_t i = 0; i <= index; i++) {
        while (*p != ':') {
            if (!*p)
                return false;
            p++;
        }
        p++;
        if ((p - 1) != config_addr && *(p - 2) != '\n')
            i--;
    }

    p--;

    size_t i;
    for (i = 0; i < (limit - 1); i++) {
        if (p[i] == SEPARATOR)
            break;
        ret[i] = p[i];
    }

    ret[i] = 0;
    return true;
}

static char *config_get_entry(size_t *size, size_t index) {
    if (!config_ready)
        return NULL;

    char *ret;
    char *p = config_addr;

    for (size_t i = 0; i <= index; i++) {
        while (*p != ':') {
            if (!*p)
                return NULL;
            p++;
        }
        p++;
        if ((p - 1) != config_addr && *(p - 2) != '\n')
            i--;
    }

    do {
        p++;
    } while (*p != '\n');

    ret = p;

cont:
    while (*p != ':' && *p)
        p++;

    if (*p && *(p - 1) != '\n') {
        p++;
        goto cont;
    }

    *size = p - ret;

    return ret;
}

static const char *lastkey;

struct conf_tuple config_get_tuple(const char *config, size_t index,
                                   const char *key1, const char *key2) {
    struct conf_tuple conf_tuple;

    conf_tuple.value1 = config_get_value(config, index, key1);
    if (conf_tuple.value1 == NULL) {
        return (struct conf_tuple){0};
    }

    conf_tuple.value2 = config_get_value(lastkey, 0, key2);

    const char *lk1 = lastkey;

    const char *next_value1 = config_get_value(config, index + 1, key1);

    const char *lk2 = lastkey;

    if (conf_tuple.value2 != NULL && next_value1 != NULL) {
        if ((uintptr_t)lk1 > (uintptr_t)lk2) {
            conf_tuple.value2 = NULL;
        }
    }

    return conf_tuple;
}

char *config_get_value(const char *config, size_t index, const char *key) {
    if (!key || !config_ready)
        return NULL;

    if (config == NULL)
        config = config_addr;

    size_t key_len = strlen(key);

    for (size_t i = 0; config[i]; i++) {
        if (!strncmp(&config[i], key, key_len) && config[i + key_len] == '=') {
            if (i && config[i - 1] != SEPARATOR)
                continue;
            if (index--)
                continue;
            i += key_len + 1;
            size_t value_len;
            for (value_len = 0;
                 config[i + value_len] != SEPARATOR && config[i + value_len];
                 value_len++);
            char *buf = ext_mem_alloc(value_len + 1);
            memcpy(buf, config + i, value_len);
            lastkey = config + i;
            return buf;
        }
    }

    return NULL;
}
