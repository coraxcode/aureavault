/*
 * AureaVault - A universal life catalog in one pure C file.
 *
 * Build:
 *   gcc -std=c99 -Wall -Wextra -Werror -pedantic -O2 -D_FORTIFY_SOURCE=2 Aureavault.c -o Aureavault
 *
 * Run:
 *   ./aureavault
 *
 * Database:
 *   aureavault.csv
 *
 * Goals:
 *   - One single C file.
 *   - No ncurses and no external dependencies.
 *   - Linux/POSIX terminal UI using ANSI escape codes only.
 *   - One normalized CSV database file.
 *   - Fully custom categories and fields.
 *   - Add, list, view, search, edit, delete and statistics.
 *   - Dialog-like aligned interface with a cyberpunk/golden-ratio feel.
 *
 * Version: 3.0 UI-aligned build.
 */

#define _POSIX_C_SOURCE 200809L

#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <termios.h>

#define APP_NAME        "AureaVault"
#define APP_TAGLINE     "A golden-ratio life catalog for everything you keep."
#define DB_FILE         "aureavault.csv"
#define DB_TEMP_FILE    "aureavault.csv.tmp"

#define PHI             1.61803398875
#define INV_PHI         0.61803398875

#define MAX_CATEGORIES  64
#define MAX_FIELDS      32
#define MAX_ITEMS       4096
#define MAX_NAME        64
#define MAX_VALUE       1024
#define MAX_CELLS       8
#define CSV_LINE        8192
#define SCREEN_MIN_WIDTH 76
#define SCREEN_MAX_WIDTH 116
#define PAGE_LINES      12

/* Colors are chosen at runtime. When g_color is 0 every color macro becomes
   an empty string "", so the program prints clean plain text with no escape
   codes. This keeps it readable on terminals that do not support ANSI. */
#define COLOR_RESET     (g_color ? "\033[0m"        : "")
#define COLOR_BOLD      (g_color ? "\033[1m"        : "")
#define COLOR_DIM       (g_color ? "\033[2m"        : "")
#define COLOR_CYAN      (g_color ? "\033[36m"       : "")
#define COLOR_GREEN     (g_color ? "\033[32m"       : "")
#define COLOR_YELLOW    (g_color ? "\033[33m"       : "")
#define COLOR_MAGENTA   (g_color ? "\033[35m"       : "")
#define COLOR_RED       (g_color ? "\033[31m"       : "")
#define COLOR_BLUE      (g_color ? "\033[34m"       : "")
#define COLOR_TITLE     (g_color ? "\033[1m\033[36m" : "")

#define UI_TOP_LEFT     '+'
#define UI_TOP_RIGHT    '+'
#define UI_BOTTOM_LEFT  '+'
#define UI_BOTTOM_RIGHT '+'
#define UI_HORIZONTAL   '-'
#define UI_VERTICAL     '|'

#define KEY_WIDTH       24
#define MENU_NUMBER_W   4

typedef struct {
    char name[MAX_NAME];
} Field;

typedef struct {
    char name[MAX_NAME];
    int field_count;
    Field fields[MAX_FIELDS];
} Category;

typedef struct {
    int used;
    int id;
    char category[MAX_NAME];
    char created[32];                 /* ISO 8601 timestamp, e.g. 2026-05-29T20:17:08 */
    char values[MAX_FIELDS][MAX_VALUE];
} Item;

typedef struct {
    Category categories[MAX_CATEGORIES];
    int category_count;
    Item items[MAX_ITEMS];
    int item_count;
    int next_id;
    int dirty;
} Database;

typedef struct {
    int cols;
    int rows;
    int width;
    int left;
    int inner;
    int key_width;
    int value_width;
} Layout;

static Database g_db;
static int g_color = 1;   /* 1 = colors on, 0 = plain text (no escapes) */
static int g_load_truncated = 0; /* set if the file held more data than fits in memory */
static int g_input_canceled = 0; /* set when the user presses ESC to cancel/go back */

static void clear_screen(void);
static int terminal_is_ansi(void);
static void pause_enter(void);
static int load_database(Database *db);
static int save_database(Database *db);
static void main_menu(Database *db);
static int read_line_raw(char *buffer, size_t buffer_size);
static void export_text_report(Database *db);

static int safe_copy(char *dst, size_t dst_size, const char *src) {
    size_t n;

    if (dst == NULL || dst_size == 0) return 0;
    if (src == NULL) src = "";

    n = strlen(src);
    if (n >= dst_size) n = dst_size - 1;

    memcpy(dst, src, n);
    dst[n] = '\0';

    return src[n] == '\0';
}

static void iso8601_now(char *out, size_t out_size) {
    time_t now;
    struct tm tmv;

    if (out == NULL || out_size == 0) return;
    out[0] = '\0';

    now = time(NULL);
    if (now == (time_t)-1) return;

    /* localtime_r is reentrant and safe; fall back gracefully if it fails. */
    if (localtime_r(&now, &tmv) == NULL) return;

    /* strftime writes the standard ISO 8601 date and time: YYYY-MM-DDTHH:MM:SS */
    if (strftime(out, out_size, "%Y-%m-%dT%H:%M:%S", &tmv) == 0) {
        out[0] = '\0';
    }
}

static void trim_in_place(char *s) {
    char *p;
    size_t len;

    if (s == NULL) return;

    p = s;
    while (*p && isspace((unsigned char)*p)) p++;
    if (p != s) memmove(s, p, strlen(p) + 1);

    len = strlen(s);
    while (len > 0 && isspace((unsigned char)s[len - 1])) {
        s[len - 1] = '\0';
        len--;
    }
}

static int is_blank(const char *s) {
    if (s == NULL) return 1;
    while (*s) {
        if (!isspace((unsigned char)*s)) return 0;
        s++;
    }
    return 1;
}

static int strings_equal_ci(const char *a, const char *b) {
    unsigned char ca;
    unsigned char cb;

    if (a == NULL || b == NULL) return 0;

    while (*a && *b) {
        ca = (unsigned char)tolower((unsigned char)*a);
        cb = (unsigned char)tolower((unsigned char)*b);
        if (ca != cb) return 0;
        a++;
        b++;
    }

    return *a == '\0' && *b == '\0';
}

static int contains_ci(const char *haystack, const char *needle) {
    size_t nlen;
    const char *h;

    if (haystack == NULL || needle == NULL) return 0;
    if (*needle == '\0') return 1;

    nlen = strlen(needle);

    for (h = haystack; *h; h++) {
        size_t i;
        for (i = 0; i < nlen; i++) {
            if (h[i] == '\0') return 0;
            if (tolower((unsigned char)h[i]) !=
                tolower((unsigned char)needle[i])) {
                break;
            }
        }
        if (i == nlen) return 1;
    }

    return 0;
}

static int parse_int_strict(const char *s, int min_value, int max_value, int *out) {
    char *endptr;
    long value;

    if (s == NULL || out == NULL || *s == '\0') return 0;

    errno = 0;
    value = strtol(s, &endptr, 10);

    if (errno != 0 || *endptr != '\0') return 0;
    if (value < min_value || value > max_value) return 0;

    *out = (int)value;
    return 1;
}

static void clear_screen(void) {
    /* Clearing the screen is a cursor control, not a color, so it must work in
       plain-text mode too. We only skip it on terminals that do not understand
       ANSI escapes at all (TERM=dumb), to avoid printing garbage there. */
    if (terminal_is_ansi()) printf("\033[2J\033[H");
    fflush(stdout);
}

static int terminal_is_ansi(void) {
    const char *term = getenv("TERM");
    if (term == NULL) return 1;
    if (strings_equal_ci(term, "dumb")) return 0;
    return 1;
}

static Layout get_layout(void) {
    struct winsize ws;
    Layout lay;
    int golden_width;
    int max_by_cols;

    lay.cols = 100;
    lay.rows = 30;

    if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == 0) {
        if (ws.ws_col > 0) lay.cols = ws.ws_col;
        if (ws.ws_row > 0) lay.rows = ws.ws_row;
    }

    max_by_cols = lay.cols - 4;
    if (max_by_cols < 40) max_by_cols = lay.cols;

    golden_width = (int)((double)lay.cols * INV_PHI);
    if (golden_width < SCREEN_MIN_WIDTH) golden_width = SCREEN_MIN_WIDTH;
    if (golden_width > SCREEN_MAX_WIDTH) golden_width = SCREEN_MAX_WIDTH;
    if (golden_width > max_by_cols) golden_width = max_by_cols;
    if (golden_width < 40) golden_width = 40;

    lay.width = golden_width;
    lay.left = (lay.cols - lay.width) / 2;
    if (lay.left < 0) lay.left = 0;

    lay.inner = lay.width - 4;
    lay.key_width = (int)((double)lay.inner / PHI) - 10;
    if (lay.key_width < 16) lay.key_width = 16;
    if (lay.key_width > KEY_WIDTH) lay.key_width = KEY_WIDTH;
    lay.value_width = lay.inner - lay.key_width - 3;
    if (lay.value_width < 20) lay.value_width = 20;

    return lay;
}

static void print_indent(int spaces) {
    int i;
    for (i = 0; i < spaces; i++) putchar(' ');
}

static void crop_text(const char *src, char *dst, size_t dst_size, int width) {
    size_t src_len;
    size_t copy_len;

    if (dst == NULL || dst_size == 0) return;
    if (src == NULL) src = "";
    if (width < 0) width = 0;

    src_len = strlen(src);

    if ((int)src_len <= width) {
        safe_copy(dst, dst_size, src);
        return;
    }

    if (width <= 0) {
        dst[0] = '\0';
        return;
    }

    if (width <= 3) {
        copy_len = (size_t)width;
        if (copy_len >= dst_size) copy_len = dst_size - 1;
        memcpy(dst, src, copy_len);
        dst[copy_len] = '\0';
        return;
    }

    /* Need room for the text plus "..." plus the terminating NUL. If the buffer
       is too small to hold even "...\0", fall back to a plain truncation so we
       never write past the end of dst. */
    if (dst_size < 5) {
        copy_len = dst_size - 1;
        memcpy(dst, src, copy_len);
        dst[copy_len] = '\0';
        return;
    }

    copy_len = (size_t)(width - 3);
    if (copy_len + 4 > dst_size) copy_len = dst_size - 4;
    memcpy(dst, src, copy_len);
    dst[copy_len] = '.';
    dst[copy_len + 1] = '.';
    dst[copy_len + 2] = '.';
    dst[copy_len + 3] = '\0';
}


static void append_raw(char *dst, size_t dst_size, const char *text) {
    size_t used;
    size_t left;

    if (dst == NULL || dst_size == 0 || text == NULL) return;

    used = strlen(dst);
    if (used >= dst_size - 1) return;

    left = dst_size - used - 1;
    strncat(dst, text, left);
}

static void append_padded(char *dst, size_t dst_size, const char *text, int width) {
    int i;
    int len;
    char local[512];

    if (dst == NULL || dst_size == 0) return;
    if (text == NULL) text = "";
    if (width < 0) width = 0;

    crop_text(text, local, sizeof(local), width);
    append_raw(dst, dst_size, local);

    len = (int)strlen(local);
    for (i = len; i < width; i++) append_raw(dst, dst_size, " ");
}

static void ui_rule(Layout lay, char left, char fill, char right) {
    int i;

    print_indent(lay.left);
    putchar(left);
    for (i = 0; i < lay.width - 2; i++) putchar(fill);
    putchar(right);
    putchar('\n');
}

static void ui_line(Layout lay, const char *text, const char *color) {
    char local[512];
    int len;
    int usable;

    usable = lay.inner;
    crop_text(text, local, sizeof(local), usable);
    len = (int)strlen(local);

    print_indent(lay.left);
    printf("%c ", UI_VERTICAL);
    if (color != NULL) printf("%s", color);
    printf("%s", local);
    if (color != NULL) printf("%s", COLOR_RESET);
    while (len < usable) {
        putchar(' ');
        len++;
    }
    printf(" %c\n", UI_VERTICAL);
}

static void ui_center_line(Layout lay, const char *text, const char *color) {
    char local[512];
    int len;
    int left_pad;
    int right_pad;

    crop_text(text, local, sizeof(local), lay.inner);
    len = (int)strlen(local);
    left_pad = (lay.inner - len) / 2;
    right_pad = lay.inner - len - left_pad;

    print_indent(lay.left);
    printf("%c ", UI_VERTICAL);
    while (left_pad-- > 0) putchar(' ');
    if (color != NULL) printf("%s", color);
    printf("%s", local);
    if (color != NULL) printf("%s", COLOR_RESET);
    while (right_pad-- > 0) putchar(' ');
    printf(" %c\n", UI_VERTICAL);
}

static void ui_blank_line(Layout lay) {
    ui_line(lay, "", NULL);
}

static void ui_header(const char *title, const char *subtitle) {
    Layout lay;

    lay = get_layout();
    if (terminal_is_ansi()) clear_screen();

    ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
    ui_center_line(lay, APP_NAME, COLOR_TITLE);
    ui_center_line(lay, title != NULL ? title : APP_TAGLINE, COLOR_MAGENTA);
    if (subtitle != NULL && *subtitle) {
        ui_center_line(lay, subtitle, COLOR_DIM);
    }
    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
    putchar('\n');
}

static void ui_status_box(const char *title, const char *left_text, const char *right_text) {
    Layout lay;
    char line[512];
    int left_width;
    int right_width;
    char left_crop[256];
    char right_crop[256];

    lay = get_layout();
    left_width = (int)((double)lay.inner * INV_PHI) - 1;
    right_width = lay.inner - left_width - 3;
    if (left_width < 20) left_width = 20;
    if (right_width < 16) right_width = 16;

    crop_text(left_text, left_crop, sizeof(left_crop), left_width);
    crop_text(right_text, right_crop, sizeof(right_crop), right_width);
    line[0] = '\0';
    append_padded(line, sizeof(line), left_crop, left_width);
    append_raw(line, sizeof(line), " | ");
    append_padded(line, sizeof(line), right_crop, right_width);

    ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
    ui_center_line(lay, title, COLOR_GREEN);
    ui_line(lay, line, NULL);
    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
}

static void ui_menu_item(Layout lay, int number, const char *label, const char *hint) {
    char num[16];
    char label_crop[256];
    char hint_crop[256];
    char line[512];
    int label_width;
    int hint_width;

    label_width = (int)((double)lay.inner * INV_PHI) - MENU_NUMBER_W - 4;
    if (label_width < 24) label_width = 24;
    hint_width = lay.inner - MENU_NUMBER_W - label_width - 5;
    if (hint_width < 12) hint_width = 12;

    if (number >= 0) snprintf(num, sizeof(num), "%d)", number);
    else safe_copy(num, sizeof(num), "");

    crop_text(label, label_crop, sizeof(label_crop), label_width);
    crop_text(hint, hint_crop, sizeof(hint_crop), hint_width);

    line[0] = '\0';
    append_padded(line, sizeof(line), num, MENU_NUMBER_W);
    append_raw(line, sizeof(line), "  ");
    append_padded(line, sizeof(line), label_crop, label_width);
    append_raw(line, sizeof(line), "  ");
    append_padded(line, sizeof(line), hint_crop, hint_width);

    ui_line(lay, line, NULL);
}

static void ui_menu_box(const char *title,
                        const char *subtitle,
                        const char *items[][2],
                        const int *numbers,
                        int count) {
    int i;
    Layout lay;

    lay = get_layout();
    ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
    ui_center_line(lay, title, COLOR_GREEN);
    if (subtitle != NULL && *subtitle) ui_center_line(lay, subtitle, COLOR_DIM);
    ui_blank_line(lay);

    for (i = 0; i < count; i++) {
        ui_menu_item(lay, numbers != NULL ? numbers[i] : i + 1, items[i][0], items[i][1]);
    }

    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
}

static void ui_key_value(const char *key, const char *value) {
    Layout lay;
    char k[MAX_NAME];
    char v[MAX_VALUE];
    char line[1400];

    lay = get_layout();
    crop_text(key, k, sizeof(k), lay.key_width);
    crop_text(value != NULL && *value ? value : "empty", v, sizeof(v), lay.value_width);

    snprintf(line,
             sizeof(line),
             "%-*s : %-*s",
             lay.key_width,
             k,
             lay.value_width,
             v);

    ui_line(lay, line, value != NULL && *value ? NULL : COLOR_DIM);
}

static int ends_with_prompt_mark(const char *text) {
    size_t len;

    if (text == NULL) return 0;
    len = strlen(text);
    if (len == 0) return 0;

    return text[len - 1] == ':' || text[len - 1] == '?' || text[len - 1] == ']';
}

static void ui_prompt(const char *label) {
    Layout lay;
    char local[192];
    const char *text;
    int max_prompt_width;

    lay = get_layout();
    text = label != NULL && *label ? label : "Input";
    max_prompt_width = lay.inner - 8;
    if (max_prompt_width < 12) max_prompt_width = 12;
    if (max_prompt_width > 48) max_prompt_width = 48;

    crop_text(text, local, sizeof(local), max_prompt_width);

    print_indent(lay.left);
    printf("%s" "%s" "%s", COLOR_CYAN, local, COLOR_RESET);
    if (!ends_with_prompt_mark(local)) printf(":");
    printf(" ");
    fflush(stdout);
}

static int read_line_aligned(const char *label, int label_width, char *out, size_t out_size) {
    Layout lay;
    char buffer[MAX_VALUE];
    char local[192];
    const char *text;

    if (out == NULL || out_size == 0) return 0;

    lay = get_layout();
    text = label != NULL && *label ? label : "Input";

    if (label_width < 4) label_width = 4;
    if (label_width > 28) label_width = 28;
    if (label_width > lay.inner - 8) label_width = lay.inner - 8;
    if (label_width < 4) label_width = 4;

    crop_text(text, local, sizeof(local), label_width);

    print_indent(lay.left);
    printf("%s" "%-*s" "%s" " : ", COLOR_CYAN, label_width, local, COLOR_RESET);
    fflush(stdout);

    if (!read_line_raw(buffer, sizeof(buffer))) {
        out[0] = '\0';
        return 0;
    }

    safe_copy(out, out_size, buffer);
    trim_in_place(out);
    return 1;
}

static int category_input_label_width(const Category *cat) {
    int width = 4;
    int i;

    if (cat == NULL) return width;

    for (i = 0; i < cat->field_count; i++) {
        int len = (int)strlen(cat->fields[i].name);
        if (len > width) width = len;
    }

    if (width > 22) width = 22;
    if (width < 4) width = 4;
    return width;
}

static void ui_message_box(const char *message, const char *color) {
    Layout lay;

    lay = get_layout();
    ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
    ui_center_line(lay, message != NULL ? message : "Done.", color);
    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
}

static int read_line_fallback(char *buffer, size_t buffer_size) {
    size_t len;

    if (fgets(buffer, buffer_size, stdin) == NULL) {
        buffer[0] = '\0';
        return 0;
    }

    len = strlen(buffer);
    if (len > 0 && buffer[len - 1] == '\n') {
        buffer[len - 1] = '\0';
    } else {
        int ch;
        while ((ch = getchar()) != '\n' && ch != EOF) {
        }
    }

    return 1;
}

/* Reads one line from the user. On an interactive terminal it reads key by key
   so the ESC key can cancel immediately: ESC sets g_input_canceled and returns 0.
   Arrow keys (ESC [ ...) are detected and ignored, so they never cancel.
   When input is not a terminal (a pipe or a file), it falls back to a simple
   and reliable line reader, keeping scripts and automated use working. */
static int read_line_raw(char *buffer, size_t buffer_size) {
    struct termios oldt;
    struct termios rawt;
    size_t len = 0;

    if (buffer == NULL || buffer_size == 0) return 0;
    buffer[0] = '\0';
    g_input_canceled = 0;

    if (!isatty(STDIN_FILENO) || tcgetattr(STDIN_FILENO, &oldt) != 0) {
        return read_line_fallback(buffer, buffer_size);
    }

    rawt = oldt;
    rawt.c_lflag = (tcflag_t)(rawt.c_lflag & ~(ICANON | ECHO));
    rawt.c_cc[VMIN] = 1;
    rawt.c_cc[VTIME] = 0;
    if (tcsetattr(STDIN_FILENO, TCSANOW, &rawt) != 0) {
        return read_line_fallback(buffer, buffer_size);
    }

    for (;;) {
        unsigned char c;
        ssize_t r = read(STDIN_FILENO, &c, 1);

        if (r <= 0) {                       /* end of input or read error */
            tcsetattr(STDIN_FILENO, TCSANOW, &oldt);
            putchar('\n');                     /* end the prompt line cleanly */
            fflush(stdout);
            buffer[len] = '\0';
            return len > 0 ? 1 : 0;
        }

        if (c == 27) {                      /* ESC: maybe a lone key, maybe a sequence */
            struct termios peekt = rawt;
            unsigned char seq;
            ssize_t r2;

            peekt.c_cc[VMIN] = 0;
            peekt.c_cc[VTIME] = 1;          /* wait up to 0.1s for more bytes */
            tcsetattr(STDIN_FILENO, TCSANOW, &peekt);
            r2 = read(STDIN_FILENO, &seq, 1);

            if (r2 > 0) {                   /* it is a sequence (e.g. an arrow key) */
                if (seq == '[' || seq == 'O') {
                    unsigned char t;
                    while (read(STDIN_FILENO, &t, 1) == 1) {
                        if ((t >= 'A' && t <= 'Z') || (t >= 'a' && t <= 'z') || t == '~') break;
                    }
                }
                tcsetattr(STDIN_FILENO, TCSANOW, &rawt);
                continue;                   /* ignore the sequence, keep typing */
            }

            tcsetattr(STDIN_FILENO, TCSANOW, &oldt);   /* lone ESC: cancel */
            putchar('\n');                            /* end the prompt line cleanly */
            fflush(stdout);
            buffer[0] = '\0';
            g_input_canceled = 1;
            return 0;
        }

        if (c == '\n' || c == '\r') {       /* ENTER: finish the line */
            putchar('\n');
            fflush(stdout);
            tcsetattr(STDIN_FILENO, TCSANOW, &oldt);
            buffer[len] = '\0';
            return 1;
        }

        if (c == 127 || c == 8) {           /* BACKSPACE (also erases full UTF-8 chars) */
            if (len > 0) {
                do {
                    len--;
                } while (len > 0 &&
                         (unsigned char)buffer[len] >= 0x80 &&
                         (unsigned char)buffer[len] < 0xC0);
                printf("\b \b");
                fflush(stdout);
            }
            continue;
        }

        if (c >= 32) {                      /* printable byte (includes UTF-8 bytes) */
            if (len + 1 < buffer_size) {
                buffer[len++] = (char)c;
                putchar((char)c);
                fflush(stdout);
            }
        }
        /* other control characters are ignored */
    }
}

static int read_line(const char *prompt, char *out, size_t out_size) {
    char buffer[MAX_VALUE];

    if (out == NULL || out_size == 0) return 0;

    if (prompt != NULL && *prompt) {
        ui_prompt(prompt);
    }

    if (!read_line_raw(buffer, sizeof(buffer))) {
        out[0] = '\0';
        return 0;
    }

    safe_copy(out, out_size, buffer);
    trim_in_place(out);
    return 1;
}

static int read_required_line(const char *prompt, char *out, size_t out_size) {
    for (;;) {
        if (!read_line(prompt, out, out_size)) return 0;
        if (!is_blank(out)) return 1;
        print_indent(get_layout().left);
        printf("%s" "This field cannot be empty.\n" "%s", COLOR_YELLOW, COLOR_RESET);
    }
}

/* read_int_range returns the chosen number, or INPUT_CANCEL when the user
   pressed ESC (g_input_canceled is set) or the input ended. Callers treat
   INPUT_CANCEL as "go back / cancel this action". */
#define INPUT_CANCEL INT_MIN

static int read_int_range(const char *prompt, int min_value, int max_value) {
    char line[64];
    int value;

    for (;;) {
        if (!read_line(prompt, line, sizeof(line))) return INPUT_CANCEL;
        if (parse_int_strict(line, min_value, max_value, &value)) return value;

        print_indent(get_layout().left);
        printf("%s" "Type a number from %d to %d.\n" "%s",
               COLOR_YELLOW,
               min_value,
               max_value,
               COLOR_RESET);
    }
}

static int confirm_action(const char *question) {
    char answer[16];
    Layout lay;

    lay = get_layout();
    print_indent(lay.left);
    printf("%s" "%s" "%s" " [y/N]: ", COLOR_YELLOW, question != NULL ? question : "Confirm?", COLOR_RESET);
    fflush(stdout);

    if (!read_line_raw(answer, sizeof(answer))) return 0;
    trim_in_place(answer);

    return answer[0] == 'y' || answer[0] == 'Y';
}

static void pause_enter(void) {
    char tmp[16];
    Layout lay;

    lay = get_layout();
    putchar('\n');
    print_indent(lay.left);
    printf("%s" "Press ENTER to continue..." "%s", COLOR_DIM, COLOR_RESET);
    fflush(stdout);

    if (!read_line_raw(tmp, sizeof(tmp))) {
        clearerr(stdin);
    }
}

static int find_category(const Database *db, const char *name) {
    int i;

    if (db == NULL || name == NULL) return -1;

    for (i = 0; i < db->category_count; i++) {
        if (strings_equal_ci(db->categories[i].name, name)) return i;
    }

    return -1;
}

static int find_field(const Category *cat, const char *name) {
    int i;

    if (cat == NULL || name == NULL) return -1;

    for (i = 0; i < cat->field_count; i++) {
        if (strings_equal_ci(cat->fields[i].name, name)) return i;
    }

    return -1;
}

static int add_category_internal(Database *db, const char *name) {
    int idx;

    if (db == NULL || is_blank(name)) return -1;
    if (db->category_count >= MAX_CATEGORIES) return -1;
    if (find_category(db, name) >= 0) return -2;

    idx = db->category_count;
    db->category_count++;

    memset(&db->categories[idx], 0, sizeof(db->categories[idx]));
    safe_copy(db->categories[idx].name, sizeof(db->categories[idx].name), name);
    db->dirty = 1;

    return idx;
}

static int ensure_category(Database *db, const char *name) {
    int idx;

    idx = find_category(db, name);
    if (idx >= 0) return idx;

    return add_category_internal(db, name);
}

static int add_field_internal(Database *db, int category_index, const char *name) {
    Category *cat;
    int fi;
    int i;

    if (db == NULL || category_index < 0 || category_index >= db->category_count) return -1;
    if (is_blank(name)) return -1;

    cat = &db->categories[category_index];
    if (cat->field_count >= MAX_FIELDS) return -1;
    if (find_field(cat, name) >= 0) return -2;

    fi = cat->field_count;
    cat->field_count++;

    memset(&cat->fields[fi], 0, sizeof(cat->fields[fi]));
    safe_copy(cat->fields[fi].name, sizeof(cat->fields[fi].name), name);

    for (i = 0; i < MAX_ITEMS; i++) {
        if (db->items[i].used && strings_equal_ci(db->items[i].category, cat->name)) {
            db->items[i].values[fi][0] = '\0';
        }
    }

    db->dirty = 1;
    return fi;
}

static int ensure_field(Database *db, int category_index, const char *name) {
    int fi;

    if (db == NULL || category_index < 0 || category_index >= db->category_count) return -1;

    fi = find_field(&db->categories[category_index], name);
    if (fi >= 0) return fi;

    return add_field_internal(db, category_index, name);
}

static int count_items_in_category(const Database *db, const char *category) {
    int i;
    int count = 0;

    if (db == NULL || category == NULL) return 0;

    for (i = 0; i < MAX_ITEMS; i++) {
        if (db->items[i].used && strings_equal_ci(db->items[i].category, category)) {
            count++;
        }
    }

    return count;
}

/* Fills "out" with the slot indices of every item in "category", ordered by the
   item's current ID (ascending). Returns how many slots were written. */
static int collect_sorted_slots(const Database *db, const char *category,
                                int *out, int out_max) {
    int i;
    int j;
    int n = 0;

    if (db == NULL || category == NULL || out == NULL) return 0;

    for (i = 0; i < MAX_ITEMS && n < out_max; i++) {
        if (db->items[i].used && strings_equal_ci(db->items[i].category, category)) {
            out[n++] = i;
        }
    }

    /* Insertion sort by current ID: small, stable and safe for our sizes. */
    for (i = 1; i < n; i++) {
        int key = out[i];
        int key_id = db->items[key].id;
        j = i - 1;
        while (j >= 0 && db->items[out[j]].id > key_id) {
            out[j + 1] = out[j];
            j--;
        }
        out[j + 1] = key;
    }

    return n;
}

/* Reassigns sequential IDs 1..N to the items of a category, keeping their order,
   so the list never shows gaps after a deletion. */
static void renumber_category(Database *db, const char *category) {
    int order[MAX_ITEMS];
    int n;
    int i;

    if (db == NULL || category == NULL) return;

    n = collect_sorted_slots(db, category, order, MAX_ITEMS);
    for (i = 0; i < n; i++) {
        db->items[order[i]].id = i + 1;
    }
}

/* Renumbers every category. Used right after loading so old files with gaps
   (or items added across categories) always start clean and sequential. */
static void renumber_all(Database *db) {
    int c;
    if (db == NULL) return;
    for (c = 0; c < db->category_count; c++) {
        renumber_category(db, db->categories[c].name);
    }
}

static int find_item_slot_by_id(const Database *db, const char *category, int id) {
    int i;

    if (db == NULL || category == NULL) return -1;

    for (i = 0; i < MAX_ITEMS; i++) {
        if (db->items[i].used &&
            db->items[i].id == id &&
            strings_equal_ci(db->items[i].category, category)) {
            return i;
        }
    }

    return -1;
}

static int allocate_item(Database *db, const char *category, int id) {
    int i;

    if (db == NULL || category == NULL || id <= 0) return -1;

    for (i = 0; i < MAX_ITEMS; i++) {
        if (!db->items[i].used) {
            memset(&db->items[i], 0, sizeof(db->items[i]));
            db->items[i].used = 1;
            db->items[i].id = id;
            safe_copy(db->items[i].category, sizeof(db->items[i].category), category);
            db->item_count++;
            if (id >= db->next_id) db->next_id = id + 1;
            db->dirty = 1;
            return i;
        }
    }

    return -1;
}

static void delete_item_slot(Database *db, int slot) {
    if (db == NULL) return;
    if (slot < 0 || slot >= MAX_ITEMS || !db->items[slot].used) return;

    memset(&db->items[slot], 0, sizeof(db->items[slot]));
    if (db->item_count > 0) db->item_count--;
    db->dirty = 1;
}

static void csv_write_field(FILE *fp, const char *s) {
    const char *p;
    int must_quote = 0;

    if (fp == NULL) return;
    if (s == NULL) s = "";

    for (p = s; *p; p++) {
        if (*p == ',' || *p == '"' || *p == '\n' || *p == '\r') {
            must_quote = 1;
            break;
        }
    }

    if (!must_quote) {
        fputs(s, fp);
        return;
    }

    fputc('"', fp);
    for (p = s; *p; p++) {
        if (*p == '"') fputc('"', fp);
        fputc(*p, fp);
    }
    fputc('"', fp);
}

static void csv_write_row5(FILE *fp,
                           const char *a,
                           const char *b,
                           const char *c,
                           const char *d,
                           const char *e) {
    csv_write_field(fp, a); fputc(',', fp);
    csv_write_field(fp, b); fputc(',', fp);
    csv_write_field(fp, c); fputc(',', fp);
    csv_write_field(fp, d); fputc(',', fp);
    csv_write_field(fp, e); fputc('\n', fp);
}

static int csv_read_row(FILE *fp, char cells[MAX_CELLS][MAX_VALUE], int max_cells) {
    char line[CSV_LINE];
    int cell;
    size_t out;
    char *p;
    int in_quotes;

    if (fp == NULL || cells == NULL || max_cells <= 0) return 0;
    if (fgets(line, sizeof(line), fp) == NULL) return 0;

    for (cell = 0; cell < max_cells; cell++) cells[cell][0] = '\0';

    cell = 0;
    out = 0;
    p = line;
    in_quotes = 0;

    while (*p != '\0') {
        char ch = *p++;

        if (ch == '\r' || ch == '\n') break;

        if (in_quotes) {
            if (ch == '"') {
                if (*p == '"') {
                    if (out + 1 < MAX_VALUE) cells[cell][out++] = '"';
                    p++;
                } else {
                    in_quotes = 0;
                }
            } else {
                if (out + 1 < MAX_VALUE) cells[cell][out++] = ch;
            }
        } else {
            if (ch == '"' && out == 0) {
                in_quotes = 1;
            } else if (ch == ',') {
                cells[cell][out] = '\0';
                trim_in_place(cells[cell]);
                cell++;
                if (cell >= max_cells) return 1;
                out = 0;
            } else {
                if (out + 1 < MAX_VALUE) cells[cell][out++] = ch;
            }
        }
    }

    if (cell < max_cells) {
        cells[cell][out] = '\0';
        trim_in_place(cells[cell]);
    }

    return 1;
}

static void init_database(Database *db) {
    if (db == NULL) return;
    memset(db, 0, sizeof(*db));
    db->next_id = 1;
}

static int load_database(Database *db) {
    FILE *fp;
    char cells[MAX_CELLS][MAX_VALUE];

    if (db == NULL) return 0;

    init_database(db);
    fp = fopen(DB_FILE, "r");
    if (fp == NULL) return 0;

    while (csv_read_row(fp, cells, MAX_CELLS)) {
        if (cells[0][0] == '\0') continue;

        if (strings_equal_ci(cells[0], "SCHEMA")) {
            int ci;
            if (is_blank(cells[1]) || is_blank(cells[3])) continue;
            ci = ensure_category(db, cells[1]);
            if (ci >= 0) (void)ensure_field(db, ci, cells[3]);
        } else if (strings_equal_ci(cells[0], "ITEM")) {
            int ci;
            int fi;
            int slot;
            int id;

            if (is_blank(cells[1]) || is_blank(cells[2]) || is_blank(cells[3])) continue;
            if (!parse_int_strict(cells[2], 1, INT_MAX, &id)) continue;

            ci = ensure_category(db, cells[1]);
            if (ci < 0) continue;

            fi = ensure_field(db, ci, cells[3]);
            if (fi < 0) continue;

            slot = find_item_slot_by_id(db, cells[1], id);
            if (slot < 0) {
                slot = allocate_item(db, cells[1], id);
                if (slot < 0) {
                    /* The file holds more items than fit in memory. Remember this
                       so we can warn the user and refuse to overwrite the file,
                       which protects the items we could not load. */
                    g_load_truncated = 1;
                }
            }
            if (slot >= 0) {
                safe_copy(db->items[slot].values[fi],
                          sizeof(db->items[slot].values[fi]),
                          cells[4]);
            }
        } else if (strings_equal_ci(cells[0], "CREATED")) {
            int slot;
            int id;

            if (is_blank(cells[1]) || is_blank(cells[2])) continue;
            if (!parse_int_strict(cells[2], 1, INT_MAX, &id)) continue;

            /* Create the item slot if it does not exist yet, so the timestamp
               loads correctly no matter where the CREATED row sits in the file. */
            if (ensure_category(db, cells[1]) < 0) continue;
            slot = find_item_slot_by_id(db, cells[1], id);
            if (slot < 0) {
                slot = allocate_item(db, cells[1], id);
                if (slot < 0) {
                    g_load_truncated = 1;
                }
            }
            if (slot >= 0) {
                safe_copy(db->items[slot].created,
                          sizeof(db->items[slot].created),
                          cells[3]);
            }
        }
    }

    fclose(fp);
    renumber_all(db);       /* guarantee clean 1..N IDs per category on open */
    db->dirty = 0;
    return 1;
}

static int save_database(Database *db) {
    FILE *fp;
    int c;
    int f;
    int i;
    char idbuf[32];

    if (db == NULL) return 0;

    if (g_load_truncated) {
        /* Safety guard: the file on disk has more data than this build can hold,
           so writing now would erase the items we did not load. Refuse to save
           and keep the original file untouched. */
        return 0;
    }

    fp = fopen(DB_TEMP_FILE, "w");
    if (fp == NULL) {
        perror("Could not write temporary database");
        return 0;
    }

    csv_write_row5(fp, "META", "APP", APP_NAME, "VERSION", "2");
    csv_write_row5(fp,
                   "META",
                   "FORMAT",
                   "normalized-csv",
                   "NOTE",
                   "Do not edit while the program is open");

    for (c = 0; c < db->category_count; c++) {
        for (f = 0; f < db->categories[c].field_count; f++) {
            csv_write_row5(fp,
                           "SCHEMA",
                           db->categories[c].name,
                           "",
                           db->categories[c].fields[f].name,
                           "");
        }
    }

    for (i = 0; i < MAX_ITEMS; i++) {
        int ci;
        if (!db->items[i].used) continue;

        ci = find_category(db, db->items[i].category);
        if (ci < 0) continue;

        snprintf(idbuf, sizeof(idbuf), "%d", db->items[i].id);

        /* Persist the creation timestamp on its own row. Old files simply have
           no CREATED rows, so this stays fully backward compatible. */
        if (db->items[i].created[0] != '\0') {
            csv_write_row5(fp,
                           "CREATED",
                           db->items[i].category,
                           idbuf,
                           db->items[i].created,
                           "");
        }

        for (f = 0; f < db->categories[ci].field_count; f++) {
            csv_write_row5(fp,
                           "ITEM",
                           db->items[i].category,
                           idbuf,
                           db->categories[ci].fields[f].name,
                           db->items[i].values[f]);
        }
    }

    if (fflush(fp) != 0) {
        perror("Could not flush temporary database");
        fclose(fp);
        return 0;
    }

    if (fsync(fileno(fp)) != 0) {
        perror("Could not sync temporary database");
        fclose(fp);
        return 0;
    }

    if (fclose(fp) != 0) {
        perror("Could not close temporary database");
        return 0;
    }

    if (rename(DB_TEMP_FILE, DB_FILE) != 0) {
        perror("Could not replace database");
        return 0;
    }

    db->dirty = 0;
    return 1;
}

static void build_item_preview(const Database *db, int slot, char *out, size_t out_size) {
    int ci;
    int f;
    int shown = 0;          /* how many fields we have added to the preview */

    if (out == NULL || out_size == 0) return;
    out[0] = '\0';

    if (db == NULL || slot < 0 || slot >= MAX_ITEMS || !db->items[slot].used) return;

    ci = find_category(db, db->items[slot].category);
    if (ci < 0) return;

    for (f = 0; f < db->categories[ci].field_count; f++) {
        if (db->items[slot].values[f][0] != '\0') {
            char piece[256];
            size_t used = strlen(out);
            int n;

            n = snprintf(piece,
                         sizeof(piece),
                         "%s%s: %.80s",
                         shown > 0 ? " | " : "",
                         db->categories[ci].fields[f].name,
                         db->items[slot].values[f]);
            if (n < 0) continue;

            /* Append only if it fits, leaving room for the terminating NUL. */
            if (used + (size_t)n + 1 < out_size) {
                memcpy(out + used, piece, (size_t)n + 1);
                shown++;
            }

            if (shown >= 2) break;   /* a two-field preview is enough */
        }
    }

    if (shown == 0) safe_copy(out, out_size, "empty item");
}

static void ui_table_header(const char *a, const char *b, const char *c, int aw, int bw, int cw) {
    Layout lay;
    char ac[128];
    char bc[128];
    char cc[128];
    char line[512];

    lay = get_layout();
    crop_text(a, ac, sizeof(ac), aw);
    crop_text(b, bc, sizeof(bc), bw);
    crop_text(c, cc, sizeof(cc), cw);

    line[0] = '\0';
    append_padded(line, sizeof(line), ac, aw);
    append_raw(line, sizeof(line), "  ");
    append_padded(line, sizeof(line), bc, bw);
    if (cw > 0) {
        append_raw(line, sizeof(line), "  ");
        append_padded(line, sizeof(line), cc, cw);
    }
    ui_line(lay, line, COLOR_TITLE);
}

static void ui_table_row(const char *a, const char *b, const char *c, int aw, int bw, int cw) {
    Layout lay;
    char ac[128];
    char bc[256];
    char cc[512];
    char line[900];

    lay = get_layout();
    crop_text(a, ac, sizeof(ac), aw);
    crop_text(b, bc, sizeof(bc), bw);
    crop_text(c, cc, sizeof(cc), cw);

    line[0] = '\0';
    append_padded(line, sizeof(line), ac, aw);
    append_raw(line, sizeof(line), "  ");
    append_padded(line, sizeof(line), bc, bw);
    if (cw > 0) {
        append_raw(line, sizeof(line), "  ");
        append_padded(line, sizeof(line), cc, cw);
    }
    ui_line(lay, line, NULL);
}

static void ui_items_table_begin(int *id_w, int *category_w, int *preview_w) {
    Layout lay;

    lay = get_layout();
    *id_w = 8;
    *category_w = (int)((double)lay.inner / PHI) - 14;
    if (*category_w < 18) *category_w = 18;
    if (*category_w > 28) *category_w = 28;
    *preview_w = lay.inner - *id_w - *category_w - 4;
    if (*preview_w < 24) *preview_w = 24;

    ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
    ui_table_header("ID", "CATEGORY", "PREVIEW", *id_w, *category_w, *preview_w);
    ui_rule(lay, '+', UI_HORIZONTAL, '+');
}

static void ui_items_table_end(void) {
    Layout lay;
    lay = get_layout();
    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
}

static void print_item_table_row(const Database *db, int slot, int id_w, int category_w, int preview_w) {
    char idbuf[32];
    char preview[512];

    if (db == NULL || slot < 0 || slot >= MAX_ITEMS || !db->items[slot].used) return;

    snprintf(idbuf, sizeof(idbuf), "%d", db->items[slot].id);
    build_item_preview(db, slot, preview, sizeof(preview));
    ui_table_row(idbuf, db->items[slot].category, preview, id_w, category_w, preview_w);
}

static void view_item(Database *db, int slot) {
    int ci;
    int f;
    char title[128];
    Layout lay;

    if (db == NULL || slot < 0 || slot >= MAX_ITEMS || !db->items[slot].used) return;

    ci = find_category(db, db->items[slot].category);
    snprintf(title, sizeof(title), "Viewing item ID %d", db->items[slot].id);
    ui_header(title, db->items[slot].category);

    lay = get_layout();
    ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);

    if (ci < 0) {
        ui_line(lay, "Category not found.", COLOR_RED);
    } else {
        if (db->items[slot].created[0] != '\0') {
            ui_key_value("Created", db->items[slot].created);
        }
        for (f = 0; f < db->categories[ci].field_count; f++) {
            ui_key_value(db->categories[ci].fields[f].name, db->items[slot].values[f]);
        }
    }

    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
    pause_enter();
}

static void list_items_in_category(Database *db, int ci) {
    int i;
    int shown = 0;
    int id_w;
    int category_w;
    int preview_w;
    int choice;
    Category *cat;

    if (db == NULL || ci < 0 || ci >= db->category_count) return;

    cat = &db->categories[ci];
    ui_header("List items", cat->name);

    ui_items_table_begin(&id_w, &category_w, &preview_w);

    {
        int order[MAX_ITEMS];
        int n;
        int k;

        n = collect_sorted_slots(db, cat->name, order, MAX_ITEMS);
        for (k = 0; k < n; k++) {
            i = order[k];
            print_item_table_row(db, i, id_w, category_w, preview_w);
            shown++;
            if (shown % PAGE_LINES == 0) {
                ui_items_table_end();
                pause_enter();
                ui_header("List items", cat->name);
                ui_items_table_begin(&id_w, &category_w, &preview_w);
            }
        }
    }

    if (shown == 0) {
        ui_table_row("-", cat->name, "No items registered yet.", id_w, category_w, preview_w);
    }

    ui_items_table_end();

    if (shown == 0) {
        pause_enter();
        return;
    }

    choice = read_int_range("Item ID to view, or 0:", 0, INT_MAX);
    if (choice != 0 && choice != INPUT_CANCEL) {
        int slot;
        slot = find_item_slot_by_id(db, cat->name, choice);
        if (slot >= 0) {
            view_item(db, slot);
        } else {
            print_indent(get_layout().left);
            printf("%s" "Item not found.\n" "%s", COLOR_YELLOW, COLOR_RESET);
            pause_enter();
        }
    }
}

static void add_item(Database *db, int ci) {
    int slot;
    int f;
    int id;
    int label_width;
    Category *cat;
    Layout lay;

    if (db == NULL || ci < 0 || ci >= db->category_count) return;
    cat = &db->categories[ci];

    ui_header("Add new item", cat->name);
    lay = get_layout();

    if (cat->field_count <= 0) {
        ui_message_box("This category has no fields. Add fields first.", COLOR_YELLOW);
        pause_enter();
        return;
    }

    if (db->item_count >= MAX_ITEMS) {
        ui_message_box("Item limit reached.", COLOR_RED);
        pause_enter();
        return;
    }

    ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
    ui_center_line(lay, "Fill the custom fields", COLOR_GREEN);
    ui_line(lay, "Leave optional fields empty if you want.", COLOR_DIM);
    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
    putchar('\n');

    /* Sequential per-category ID. Items stay numbered 1..N with no gaps. */
    id = count_items_in_category(db, cat->name) + 1;
    slot = allocate_item(db, cat->name, id);
    if (slot < 0) {
        ui_message_box("Could not allocate item.", COLOR_RED);
        pause_enter();
        return;
    }

    /* Stamp the creation time in ISO 8601 (e.g. 2026-05-29T20:17:08). */
    iso8601_now(db->items[slot].created, sizeof(db->items[slot].created));

    label_width = category_input_label_width(cat);

    for (f = 0; f < cat->field_count; f++) {
        if (!read_line_aligned(cat->fields[f].name,
                               label_width,
                               db->items[slot].values[f],
                               sizeof(db->items[slot].values[f]))) {
            delete_item_slot(db, slot);
            ui_message_box("Input canceled. Item was not saved.", COLOR_YELLOW);
            pause_enter();
            return;
        }
    }

    db->dirty = 1;
    if (save_database(db)) {
        char message[96];
        snprintf(message, sizeof(message), "Item saved with ID %d.", db->items[slot].id);
        putchar('\n');
        ui_message_box(message, COLOR_GREEN);
    } else {
        ui_message_box("Save failed. Check file permissions.", COLOR_RED);
    }
    pause_enter();
}

static void edit_item(Database *db, int ci) {
    int id;
    int slot;
    int f;
    int label_width;
    Category *cat;
    char title[128];
    Layout lay;

    if (db == NULL || ci < 0 || ci >= db->category_count) return;
    cat = &db->categories[ci];

    ui_header("Edit item", cat->name);
    id = read_int_range("Item ID:", 1, INT_MAX);
    if (id == INPUT_CANCEL) return;

    slot = find_item_slot_by_id(db, cat->name, id);
    if (slot < 0) {
        ui_message_box("Item not found.", COLOR_YELLOW);
        pause_enter();
        return;
    }

    snprintf(title, sizeof(title), "Editing item ID %d", id);
    ui_header(title, cat->name);
    lay = get_layout();

    ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
    ui_center_line(lay, "Current values", COLOR_GREEN);
    for (f = 0; f < cat->field_count; f++) {
        ui_key_value(cat->fields[f].name, db->items[slot].values[f]);
    }
    ui_blank_line(lay);
    ui_line(lay, "Press ENTER without text to keep the current value.", COLOR_DIM);
    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
    putchar('\n');

    label_width = category_input_label_width(cat);

    for (f = 0; f < cat->field_count; f++) {
        char line[MAX_VALUE];

        if (read_line_aligned(cat->fields[f].name, label_width, line, sizeof(line)) && line[0] != '\0') {
            safe_copy(db->items[slot].values[f], sizeof(db->items[slot].values[f]), line);
            db->dirty = 1;
        }
    }

    if (db->dirty && save_database(db)) {
        putchar('\n');
        ui_message_box("Item updated.", COLOR_GREEN);
    } else {
        putchar('\n');
        ui_message_box("No changes were saved.", COLOR_DIM);
    }
    pause_enter();
}

static void delete_item(Database *db, int ci) {
    int id;
    int slot;
    Category *cat;
    char question[160];

    if (db == NULL || ci < 0 || ci >= db->category_count) return;
    cat = &db->categories[ci];

    ui_header("Delete item", cat->name);
    id = read_int_range("Item ID:", 1, INT_MAX);
    if (id == INPUT_CANCEL) return;

    slot = find_item_slot_by_id(db, cat->name, id);
    if (slot < 0) {
        print_indent(get_layout().left);
        printf("%s" "Item not found.\n" "%s", COLOR_YELLOW, COLOR_RESET);
        pause_enter();
        return;
    }

    snprintf(question, sizeof(question), "Delete item ID %d permanently?", id);
    if (confirm_action(question)) {
        delete_item_slot(db, slot);
        renumber_category(db, cat->name);   /* close the gap: 1,2,3,... again */
        if (save_database(db)) {
            print_indent(get_layout().left);
            printf("%s" "Item deleted.\n" "%s", COLOR_GREEN, COLOR_RESET);
        }
    } else {
        print_indent(get_layout().left);
        printf("%s" "Canceled.\n" "%s", COLOR_DIM, COLOR_RESET);
    }

    pause_enter();
}

static int item_matches(const Database *db, int slot, int ci, const char *term) {
    int f;
    int real_ci;

    if (db == NULL || term == NULL) return 0;
    if (slot < 0 || slot >= MAX_ITEMS || !db->items[slot].used) return 0;

    if (ci >= 0) {
        if (!strings_equal_ci(db->items[slot].category, db->categories[ci].name)) return 0;
        real_ci = ci;
    } else {
        real_ci = find_category(db, db->items[slot].category);
        if (real_ci < 0) return 0;
    }

    if (contains_ci(db->items[slot].category, term)) return 1;

    for (f = 0; f < db->categories[real_ci].field_count; f++) {
        if (contains_ci(db->categories[real_ci].fields[f].name, term)) return 1;
        if (contains_ci(db->items[slot].values[f], term)) return 1;
    }

    return 0;
}

static void search_items(Database *db, int ci) {
    char term[MAX_VALUE];
    int i;
    int found = 0;
    int shown = 0;
    int id_w;
    int category_w;
    int preview_w;
    const char *subtitle;

    if (db == NULL) return;

    subtitle = ci >= 0 ? db->categories[ci].name : "All categories";
    ui_header("Search", subtitle);

    if (!read_required_line("Search text:", term, sizeof(term))) return;

    ui_header("Search results", term);
    ui_items_table_begin(&id_w, &category_w, &preview_w);

    for (i = 0; i < MAX_ITEMS; i++) {
        if (item_matches(db, i, ci, term)) {
            print_item_table_row(db, i, id_w, category_w, preview_w);
            found++;
            shown++;
            if (shown % PAGE_LINES == 0) {
                ui_items_table_end();
                pause_enter();
                ui_header("Search results", term);
                ui_items_table_begin(&id_w, &category_w, &preview_w);
            }
        }
    }

    if (found == 0) {
        ui_table_row("-", subtitle, "No matching items.", id_w, category_w, preview_w);
    }

    ui_items_table_end();
    putchar('\n');
    print_indent(get_layout().left);
    printf("%s" "%d result(s).\n" "%s", COLOR_GREEN, found, COLOR_RESET);
    pause_enter();
}

static void add_category_ui(Database *db) {
    char name[MAX_NAME];
    int ci;
    int n;
    int i;

    if (db == NULL) return;

    ui_header("Create category", "Examples: Movies, Books, Places, Goals, Home Items");

    if (!read_required_line("Category name:", name, sizeof(name))) return;

    ci = add_category_internal(db, name);
    if (ci == -2) {
        print_indent(get_layout().left);
        printf("%s" "A category with this name already exists.\n" "%s", COLOR_YELLOW, COLOR_RESET);
        pause_enter();
        return;
    }
    if (ci < 0) {
        print_indent(get_layout().left);
        printf("%s" "Category limit reached.\n" "%s", COLOR_RED, COLOR_RESET);
        pause_enter();
        return;
    }

    n = read_int_range("Custom fields:", 1, MAX_FIELDS);
    if (n == INPUT_CANCEL) {
        /* ESC at this point cancels the whole action. The category was created
           in memory a moment ago, so we undo it and save nothing. It is always
           the last category in the array, which makes removal simple and safe. */
        memset(&db->categories[ci], 0, sizeof(db->categories[ci]));
        if (db->category_count > 0) db->category_count--;
        db->dirty = 0;
        print_indent(get_layout().left);
        printf("%s" "Canceled. The category was not created.\n" "%s", COLOR_DIM, COLOR_RESET);
        pause_enter();
        return;
    }

    for (i = 0; i < n; i++) {
        char field[MAX_NAME];
        char prompt[64];
        int r;

        snprintf(prompt, sizeof(prompt), "Field %d name:", i + 1);
        if (!read_required_line(prompt, field, sizeof(field))) {
            /* ESC while typing field names: keep the fields already added. If
               none were added yet, cancel the whole category like above. */
            break;
        }

        r = add_field_internal(db, ci, field);
        if (r == -2) {
            print_indent(get_layout().left);
            printf("%s" "Duplicated field ignored. Try another name.\n" "%s", COLOR_YELLOW, COLOR_RESET);
            i--;
        }
    }

    if (db->categories[ci].field_count == 0) {
        /* A category with no fields cannot store anything, so do not keep it. */
        memset(&db->categories[ci], 0, sizeof(db->categories[ci]));
        if (db->category_count > 0) db->category_count--;
        db->dirty = 0;
        print_indent(get_layout().left);
        printf("%s" "Canceled. A category needs at least one field.\n" "%s", COLOR_DIM, COLOR_RESET);
        pause_enter();
        return;
    }

    if (save_database(db)) {
        putchar('\n');
        print_indent(get_layout().left);
        printf("%s" "Category created.\n" "%s", COLOR_GREEN, COLOR_RESET);
    }
    pause_enter();
}

static void list_categories_table(Database *db) {
    int i;
    int num_w;
    int name_w;
    int info_w;
    Layout lay;

    lay = get_layout();
    num_w = 5;
    name_w = (int)((double)lay.inner * INV_PHI) - 6;
    if (name_w < 24) name_w = 24;
    if (name_w > 42) name_w = 42;
    info_w = lay.inner - num_w - name_w - 4;
    if (info_w < 20) info_w = 20;

    ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
    ui_table_header("NO", "CATEGORY", "ITEMS / FIELDS", num_w, name_w, info_w);
    ui_rule(lay, '+', UI_HORIZONTAL, '+');

    if (db->category_count == 0) {
        ui_table_row("-", "No categories yet", "Create one first", num_w, name_w, info_w);
    } else {
        for (i = 0; i < db->category_count; i++) {
            char nbuf[16];
            char ibuf[80];
            snprintf(nbuf, sizeof(nbuf), "%d", i + 1);
            snprintf(ibuf,
                     sizeof(ibuf),
                     "%d item(s), %d field(s)",
                     count_items_in_category(db, db->categories[i].name),
                     db->categories[i].field_count);
            ui_table_row(nbuf, db->categories[i].name, ibuf, num_w, name_w, info_w);
        }
    }

    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
}

static void rename_category(Database *db, int ci) {
    char newname[MAX_NAME];
    char oldname[MAX_NAME];
    int i;

    if (db == NULL || ci < 0 || ci >= db->category_count) return;

    ui_header("Rename category", db->categories[ci].name);

    if (!read_required_line("New name:", newname, sizeof(newname))) return;

    if (strings_equal_ci(newname, db->categories[ci].name)) {
        print_indent(get_layout().left);
        printf("%s" "The name did not change.\n" "%s", COLOR_DIM, COLOR_RESET);
        pause_enter();
        return;
    }

    if (find_category(db, newname) >= 0) {
        print_indent(get_layout().left);
        printf("%s" "A category with this name already exists.\n" "%s", COLOR_YELLOW, COLOR_RESET);
        pause_enter();
        return;
    }

    safe_copy(oldname, sizeof(oldname), db->categories[ci].name);
    safe_copy(db->categories[ci].name, sizeof(db->categories[ci].name), newname);

    for (i = 0; i < MAX_ITEMS; i++) {
        if (db->items[i].used && strings_equal_ci(db->items[i].category, oldname)) {
            safe_copy(db->items[i].category, sizeof(db->items[i].category), newname);
        }
    }

    db->dirty = 1;
    if (save_database(db)) {
        print_indent(get_layout().left);
        printf("%s" "Category renamed.\n" "%s", COLOR_GREEN, COLOR_RESET);
    }
    pause_enter();
}

static void delete_category(Database *db, int ci) {
    char question[180];
    char catname[MAX_NAME];
    int i;

    if (db == NULL || ci < 0 || ci >= db->category_count) return;

    ui_header("Delete category", db->categories[ci].name);

    snprintf(question,
             sizeof(question),
             "Delete category '%s' and all its items?",
             db->categories[ci].name);

    if (!confirm_action(question)) {
        print_indent(get_layout().left);
        printf("%s" "Canceled.\n" "%s", COLOR_DIM, COLOR_RESET);
        pause_enter();
        return;
    }

    safe_copy(catname, sizeof(catname), db->categories[ci].name);

    for (i = 0; i < MAX_ITEMS; i++) {
        if (db->items[i].used && strings_equal_ci(db->items[i].category, catname)) {
            delete_item_slot(db, i);
        }
    }

    for (i = ci; i < db->category_count - 1; i++) {
        db->categories[i] = db->categories[i + 1];
    }

    if (db->category_count > 0) {
        memset(&db->categories[db->category_count - 1], 0, sizeof(db->categories[0]));
        db->category_count--;
    }

    db->dirty = 1;
    if (save_database(db)) {
        print_indent(get_layout().left);
        printf("%s" "Category deleted.\n" "%s", COLOR_GREEN, COLOR_RESET);
    }
    pause_enter();
}

static void manage_fields(Database *db, int ci) {
    int choice;
    Category *cat;

    if (db == NULL || ci < 0 || ci >= db->category_count) return;
    cat = &db->categories[ci];

    for (;;) {
        int i;
        int n_w;
        int field_w;
        int note_w;
        Layout lay;
        const char *items[][2] = {
            {"Add field", "Create a new custom column"},
            {"Rename field", "Keep all existing values"},
            {"Delete field", "Remove the column and values"},
            {"Back", "Return to category"}
        };
        const int nums[] = {1, 2, 3, 0};

        ui_header("Manage fields", cat->name);

        lay = get_layout();
        n_w = 5;
        field_w = (int)((double)lay.inner * INV_PHI) - 4;
        if (field_w < 28) field_w = 28;
        note_w = lay.inner - n_w - field_w - 4;
        if (note_w < 16) note_w = 16;

        ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
        ui_table_header("NO", "FIELD", "STATUS", n_w, field_w, note_w);
        ui_rule(lay, '+', UI_HORIZONTAL, '+');

        if (cat->field_count == 0) {
            ui_table_row("-", "No fields", "Add one first", n_w, field_w, note_w);
        } else {
            for (i = 0; i < cat->field_count; i++) {
                char num[16];
                snprintf(num, sizeof(num), "%d", i + 1);
                ui_table_row(num, cat->fields[i].name, "active", n_w, field_w, note_w);
            }
        }

        ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
        putchar('\n');
        ui_menu_box("Field Actions", "Schema editor", items, nums, 4);

        choice = read_int_range("Choice:", 0, 3);
        if (choice == 0 || choice == INPUT_CANCEL) return;

        if (choice == 1) {
            char field[MAX_NAME];
            int r;

            if (cat->field_count >= MAX_FIELDS) {
                print_indent(get_layout().left);
                printf("%s" "Field limit reached.\n" "%s", COLOR_YELLOW, COLOR_RESET);
                pause_enter();
                continue;
            }

            if (read_required_line("New field:", field, sizeof(field))) {
                r = add_field_internal(db, ci, field);
                if (r == -2) {
                    print_indent(get_layout().left);
                    printf("%s" "This field already exists.\n" "%s", COLOR_YELLOW, COLOR_RESET);
                } else if (r >= 0 && save_database(db)) {
                    print_indent(get_layout().left);
                    printf("%s" "Field added.\n" "%s", COLOR_GREEN, COLOR_RESET);
                }
                pause_enter();
            }
        } else if (choice == 2) {
            int fi;
            char field[MAX_NAME];

            if (cat->field_count == 0) {
                print_indent(get_layout().left);
                printf("%s" "No fields to rename.\n" "%s", COLOR_YELLOW, COLOR_RESET);
                pause_enter();
                continue;
            }

            fi = read_int_range("Field number:", 1, cat->field_count);
            if (fi == INPUT_CANCEL) continue;
            fi = fi - 1;
            if (read_required_line("New field:", field, sizeof(field))) {
                if (strings_equal_ci(field, cat->fields[fi].name)) {
                    print_indent(get_layout().left);
                    printf("%s" "The name did not change.\n" "%s", COLOR_DIM, COLOR_RESET);
                } else if (find_field(cat, field) >= 0) {
                    print_indent(get_layout().left);
                    printf("%s" "This field already exists.\n" "%s", COLOR_YELLOW, COLOR_RESET);
                } else {
                    safe_copy(cat->fields[fi].name, sizeof(cat->fields[fi].name), field);
                    db->dirty = 1;
                    if (save_database(db)) {
                        print_indent(get_layout().left);
                        printf("%s" "Field renamed.\n" "%s", COLOR_GREEN, COLOR_RESET);
                    }
                }
                pause_enter();
            }
        } else if (choice == 3) {
            int fi;
            char question[180];

            if (cat->field_count == 0) {
                print_indent(get_layout().left);
                printf("%s" "No fields to delete.\n" "%s", COLOR_YELLOW, COLOR_RESET);
                pause_enter();
                continue;
            }

            fi = read_int_range("Field number:", 1, cat->field_count);
            if (fi == INPUT_CANCEL) continue;
            fi = fi - 1;
            snprintf(question,
                     sizeof(question),
                     "Delete field '%s' and all its values?",
                     cat->fields[fi].name);

            if (confirm_action(question)) {
                int item;
                int v;

                for (i = fi; i < cat->field_count - 1; i++) {
                    cat->fields[i] = cat->fields[i + 1];
                }
                memset(&cat->fields[cat->field_count - 1], 0, sizeof(cat->fields[0]));

                for (item = 0; item < MAX_ITEMS; item++) {
                    if (db->items[item].used && strings_equal_ci(db->items[item].category, cat->name)) {
                        for (v = fi; v < MAX_FIELDS - 1; v++) {
                            safe_copy(db->items[item].values[v],
                                      sizeof(db->items[item].values[v]),
                                      db->items[item].values[v + 1]);
                        }
                        db->items[item].values[MAX_FIELDS - 1][0] = '\0';
                    }
                }

                cat->field_count--;
                db->dirty = 1;
                if (save_database(db)) {
                    print_indent(get_layout().left);
                    printf("%s" "Field deleted.\n" "%s", COLOR_GREEN, COLOR_RESET);
                }
            } else {
                print_indent(get_layout().left);
                printf("%s" "Canceled.\n" "%s", COLOR_DIM, COLOR_RESET);
            }
            pause_enter();
        }
    }
}

static void category_menu(Database *db, int ci) {
    int choice;

    if (db == NULL || ci < 0 || ci >= db->category_count) return;

    for (;;) {
        char subtitle[160];
        const char *items[][2] = {
            {"List items", "View everything in this category"},
            {"Add item", "Register a new catalog entry"},
            {"Search here", "Search in every custom field"},
            {"Edit item", "Change values by item ID"},
            {"Delete item", "Remove one item by ID"},
            {"Manage fields", "Add, rename or delete fields"},
            {"Rename category", "Change category name safely"},
            {"Delete category", "Remove category and items"},
            {"Back", "Return to main menu"}
        };
        const int nums[] = {1, 2, 3, 4, 5, 6, 7, 8, 0};

        if (ci >= db->category_count) return;

        snprintf(subtitle,
                 sizeof(subtitle),
                 "%d item(s), %d field(s)",
                 count_items_in_category(db, db->categories[ci].name),
                 db->categories[ci].field_count);

        ui_header(db->categories[ci].name, subtitle);
        ui_menu_box("Category Menu", "Choose an action  -  ESC = back", items, nums, 9);

        choice = read_int_range("Choice:", 0, 8);
        if (choice == 0 || choice == INPUT_CANCEL) return;
        if (choice == 1) list_items_in_category(db, ci);
        else if (choice == 2) add_item(db, ci);
        else if (choice == 3) search_items(db, ci);
        else if (choice == 4) edit_item(db, ci);
        else if (choice == 5) delete_item(db, ci);
        else if (choice == 6) manage_fields(db, ci);
        else if (choice == 7) rename_category(db, ci);
        else if (choice == 8) {
            delete_category(db, ci);
            return;
        }
    }
}

static void open_category(Database *db) {
    int choice;

    if (db == NULL) return;

    ui_header("Categories", "Choose a number to open a category");
    list_categories_table(db);

    if (db->category_count == 0) {
        pause_enter();
        return;
    }

    choice = read_int_range("Open number, or 0:", 0, db->category_count);
    if (choice != INPUT_CANCEL && choice > 0) category_menu(db, choice - 1);
}

static void show_stats(Database *db) {
    int i;
    int name_w;
    int info_w;
    Layout lay;
    char total_categories[32];
    char total_items[32];

    if (db == NULL) return;

    ui_header("Statistics", "Database overview");

    lay = get_layout();
    snprintf(total_categories, sizeof(total_categories), "%d", db->category_count);
    snprintf(total_items, sizeof(total_items), "%d", db->item_count);

    ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
    ui_center_line(lay, "Vault Summary", COLOR_GREEN);
    ui_key_value("Total categories", total_categories);
    ui_key_value("Total items", total_items);
    ui_key_value("CSV file", DB_FILE);
    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
    putchar('\n');

    name_w = (int)((double)lay.inner * INV_PHI) - 2;
    if (name_w < 30) name_w = 30;
    if (name_w > 46) name_w = 46;
    info_w = lay.inner - name_w - 4;
    if (info_w < 22) info_w = 22;

    ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
    ui_table_header("CATEGORY", "ITEMS / FIELDS", "", name_w, info_w, 0);
    ui_rule(lay, '+', UI_HORIZONTAL, '+');

    if (db->category_count == 0) {
        ui_table_row("No categories", "Create one first", "", name_w, info_w, 0);
    } else {
        for (i = 0; i < db->category_count; i++) {
            char info[80];
            snprintf(info,
                     sizeof(info),
                     "%d item(s), %d field(s)",
                     count_items_in_category(db, db->categories[i].name),
                     db->categories[i].field_count);
            ui_table_row(db->categories[i].name, info, "", name_w, info_w, 0);
        }
    }

    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
    pause_enter();
}

static void show_help(void) {
    Layout lay;

    ui_header("Help", "Simple, safe and universal");
    lay = get_layout();

    ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
    ui_center_line(lay, "How AureaVault works", COLOR_GREEN);
    ui_blank_line(lay);
    ui_line(lay, "1. Create a category for anything: movies, books, places, goals or tools.", NULL);
    ui_line(lay, "2. Define custom fields: Title, Date, Rating, Notes, Price, Status, etc.", NULL);
    ui_line(lay, "3. Add items and search across every field, including field names.", NULL);
    ui_line(lay, "4. Everything is saved in one normalized CSV file.", NULL);
    ui_blank_line(lay);
    ui_line(lay, "The program saves through a temporary file, then replaces the database safely.", COLOR_DIM);
    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);

    pause_enter();
}

static void create_demo_if_empty(Database *db) {
    if (db == NULL || db->category_count != 0) return;

    if (confirm_action("No database found. Create a small demo category?")) {
        int ci;
        ci = add_category_internal(db, "Movies");
        if (ci >= 0) {
            (void)add_field_internal(db, ci, "Title");
            (void)add_field_internal(db, ci, "Date");
            (void)add_field_internal(db, ci, "Rating");
            (void)add_field_internal(db, ci, "Notes");
            (void)save_database(db);
        }
    }
}

static void export_text_report(Database *db) {
    static const char *REPORT_FILE = "aureavault_report.txt";
    static const char *REPORT_TEMP = "aureavault_report.txt.tmp";
    FILE *fp;
    int c;
    int f;

    if (db == NULL) return;

    ui_header("Text Report", "Export a printer-friendly summary of your vault.");

    /* Write to a temporary file first, then rename. If anything fails, the
       previous report (if any) stays untouched. This is the same safe pattern
       the database uses. */
    fp = fopen(REPORT_TEMP, "w");
    if (fp == NULL) {
        print_indent(get_layout().left);
        printf("%s" "Could not create the report file.\n" "%s", COLOR_RED, COLOR_RESET);
        pause_enter();
        return;
    }

    {
        char stamp[32];
        iso8601_now(stamp, sizeof(stamp));
        fprintf(fp, "%s - Text Report\n", APP_NAME);
        fprintf(fp, "%s\n", APP_TAGLINE);
        fprintf(fp, "Generated: %s\n", stamp[0] != '\0' ? stamp : "unknown");
        fprintf(fp, "============================================================\n");
        fprintf(fp, "Categories: %d    Items: %d\n", db->category_count, db->item_count);
        fprintf(fp, "============================================================\n\n");
    }

    for (c = 0; c < db->category_count; c++) {
        const Category *cat = &db->categories[c];
        int shown = 0;

        fprintf(fp, "## %s\n", cat->name);
        fprintf(fp, "------------------------------------------------------------\n");

        {
            int order[MAX_ITEMS];
            int n;
            int k;

            n = collect_sorted_slots(db, cat->name, order, MAX_ITEMS);
            for (k = 0; k < n; k++) {
                const Item *it = &db->items[order[k]];

                shown++;
                fprintf(fp, "Item #%d\n", it->id);
                if (it->created[0] != '\0') {
                    fprintf(fp, "  Created: %s\n", it->created);
                }
                for (f = 0; f < cat->field_count; f++) {
                    fprintf(fp, "  %s: %s\n", cat->fields[f].name, it->values[f]);
                }
                fprintf(fp, "\n");
            }
        }

        if (shown == 0) {
            fprintf(fp, "(no items)\n\n");
        }
    }

    /* Make sure every byte reaches the disk before we replace the old file. */
    if (fflush(fp) != 0 || fsync(fileno(fp)) != 0) {
        fclose(fp);
        print_indent(get_layout().left);
        printf("%s" "Could not finish writing the report.\n" "%s", COLOR_RED, COLOR_RESET);
        pause_enter();
        return;
    }
    if (fclose(fp) != 0) {
        print_indent(get_layout().left);
        printf("%s" "Could not close the report file.\n" "%s", COLOR_RED, COLOR_RESET);
        pause_enter();
        return;
    }
    if (rename(REPORT_TEMP, REPORT_FILE) != 0) {
        print_indent(get_layout().left);
        printf("%s" "Could not save the report file.\n" "%s", COLOR_RED, COLOR_RESET);
        pause_enter();
        return;
    }

    putchar('\n');
    print_indent(get_layout().left);
    printf("%s" "Report saved to %s" "%s\n", COLOR_GREEN, REPORT_FILE, COLOR_RESET);
    print_indent(get_layout().left);
    printf("You can open or print it with any text editor.\n");
    pause_enter();
}

static void main_menu(Database *db) {
    int choice;

    if (db == NULL) return;

    for (;;) {
        char subtitle[180];
        char left[160];
        char right[160];
        const char *items[][2] = {
            {"Open categories", "Browse, view and edit items"},
            {"Create category", "Build a new custom catalog"},
            {"Search all", "Search in every category and field"},
            {"Statistics", "See totals and database overview"},
            {"Help", "Quick explanation"},
            {"Generate Text Report", "Export a printer-friendly .txt file"},
            {"Save and exit", "Close AureaVault safely"}
        };
        const int nums[] = {1, 2, 3, 4, 5, 6, 0};

        snprintf(subtitle,
                 sizeof(subtitle),
                 "%d categories | %d items | %s",
                 db->category_count,
                 db->item_count,
                 DB_FILE);
        snprintf(left, sizeof(left), "Categories: %d", db->category_count);
        snprintf(right, sizeof(right), "Items: %d", db->item_count);

        ui_header(APP_TAGLINE, subtitle);
        ui_status_box("Vault Status", left, right);
        putchar('\n');
        ui_menu_box("Main Menu", "Elegant catalog management  -  ESC = back", items, nums, 7);

        choice = read_int_range("Choice:", 0, 6);

        if (choice == INPUT_CANCEL) {
            /* At the top menu there is nowhere to go back to. A lone ESC just
               redraws the menu; an ended input (Ctrl+D) exits safely. */
            if (g_input_canceled) {
                g_input_canceled = 0;
                continue;
            }
            if (db->dirty) (void)save_database(db);
            ui_header("Goodbye", "Your life catalog is safe.");
            return;
        }

        if (choice == 0) {
            if (db->dirty) (void)save_database(db);
            ui_header("Goodbye", "Your life catalog is safe.");
            return;
        }
        if (choice == 1) open_category(db);
        else if (choice == 2) add_category_ui(db);
        else if (choice == 3) search_items(db, -1);
        else if (choice == 4) show_stats(db);
        else if (choice == 5) show_help();
        else if (choice == 6) export_text_report(db);
    }
}

static void choose_color_mode(void) {
    char line[16];
    int value;
    int invalid = 0;
    Layout lay;

    for (;;) {
        lay = get_layout();
        clear_screen();         /* start on a clean screen, like every other menu */

        putchar('\n');
        ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
        ui_center_line(lay, APP_NAME, NULL);
        ui_center_line(lay, "Choose how the screen should look", NULL);
        ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
        putchar('\n');

        ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
        ui_line(lay, "0)  Colors ON   - cyberpunk look (recommended)", NULL);
        ui_line(lay, "1)  Colors OFF  - plain text, safe on any terminal", NULL);
        ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
        putchar('\n');

        if (invalid) {
            print_indent(lay.left);
            printf("Please type 0 or 1.\n");
        }

        print_indent(lay.left);
        printf("Type 0 or 1: ");
        fflush(stdout);

        if (!read_line_raw(line, sizeof(line))) {
            g_color = 1;            /* default to colors if input ends (Ctrl+D) */
            return;
        }
        trim_in_place(line);

        if (parse_int_strict(line, 0, 1, &value)) {
            g_color = (value == 0) ? 1 : 0;
            return;
        }

        invalid = 1;
    }
}

int main(void) {
    int loaded;

    choose_color_mode();

    loaded = load_database(&g_db);
    if (g_load_truncated) {
        ui_header(APP_TAGLINE,
                  "WARNING: file too large - opened READ-ONLY, saving is blocked.");
    } else {
        ui_header(APP_TAGLINE, loaded ? "Database loaded." : "New database.");
    }

    if (!loaded) create_demo_if_empty(&g_db);
    main_menu(&g_db);

    return 0;
}
