/*
 * AureaVault - A universal life catalog in a single C file (SQLite-backed).
 *
 * Build (with the bundled SQLite amalgamation, no system libraries needed):
 *   gcc -std=c99 -O2 -D_FORTIFY_SOURCE=2 aureavault.c sqlite3.c -o aureavault -lpthread
 *
 * Run:
 *   ./aureavault
 *
 * Database:
 *   aureavault.db   (SQLite database file; scales to millions of items)
 *
 * Goals:
 *   - Single C program; data engine is SQLite (one extra .c file, public domain).
 *   - No ncurses; Linux/POSIX terminal UI using ANSI escape codes only.
 *   - Fully custom categories and fields.
 *   - Add, list, view, search, edit, delete, statistics, ISO 8601 timestamps.
 *   - ESC cancels/goes back anywhere. Colors are optional.
 *   - Durable: every change is an ACID transaction (safe on power loss).
 *
 * Version: 4.0 SQLite build.
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

#include "sqlite3.h"

#define APP_NAME        "AureaVault"
#define APP_TAGLINE     "A golden-ratio life catalog for everything you keep."
#define DB_FILE         "aureavault.db"

#define PHI             1.61803398875
#define INV_PHI         0.61803398875

/* These are UI/limits only; the database itself is not bounded by them. */
#define MAX_FIELDS      64        /* fields shown/handled per category in the UI */
#define MAX_NAME        128
#define MAX_VALUE       4096      /* max length of a single field value in the UI */
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
    int cols;
    int rows;
    int width;
    int left;
    int inner;
    int key_width;
    int value_width;
} Layout;

/* The whole database is a single SQLite connection. */
static sqlite3 *g_db = NULL;
static int g_color = 1;   /* 1 = colors on, 0 = plain text (no escapes) */

static int g_input_canceled = 0; /* set when the user presses ESC to cancel/go back */

static void clear_screen(void);
static int terminal_is_ansi(void);
static void pause_enter(void);
static void main_menu(void);
static int read_line_raw(char *buffer, size_t buffer_size);
static void export_text_report(void);

/* ---- UTF-8 display-width helpers --------------------------------------------
   The terminal shows characters, not bytes. A byte with the top bits "10" is a
   UTF-8 continuation byte and takes no column of its own. These helpers let the
   UI measure and cut text by visible width so borders always line up, even with
   accented text (a, e, i, o, u with marks, c-cedilla, etc.). This is a width
   approximation that is exact for the Latin text this program handles. */

static int utf8_is_continuation(unsigned char c) {
    return (c & 0xC0) == 0x80;
}

/* Number of visible characters (code points) in a UTF-8 string. */
static size_t utf8_width(const char *s) {
    size_t w = 0;
    if (s == NULL) return 0;
    while (*s) {
        if (!utf8_is_continuation((unsigned char)*s)) w++;
        s++;
    }
    return w;
}

/* Byte length of the first n visible characters of s (stops at the NUL). */
static size_t utf8_byte_len_for_width(const char *s, size_t n) {
    size_t bytes = 0;
    size_t seen = 0;
    if (s == NULL) return 0;
    while (s[bytes] != '\0' && seen < n) {
        bytes++;
        while (s[bytes] != '\0' && utf8_is_continuation((unsigned char)s[bytes])) {
            bytes++;
        }
        seen++;
    }
    return bytes;
}

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

/* Copies src into dst so that it occupies at most "width" visible columns.
   If src is wider, it is cut and an ellipsis "..." is added. Counting is by
   UTF-8 characters, never bytes, and a multi-byte character is never split,
   so the output always has a predictable display width and dst is never
   overflowed. */
static void crop_text(const char *src, char *dst, size_t dst_size, int width) {
    size_t src_width;
    size_t keep_chars;
    size_t copy_bytes;

    if (dst == NULL || dst_size == 0) return;
    if (src == NULL) src = "";
    if (width < 0) width = 0;

    src_width = utf8_width(src);

    /* Fits by display width AND fits in the byte buffer: copy verbatim. */
    if ((int)src_width <= width && strlen(src) < dst_size) {
        safe_copy(dst, dst_size, src);
        return;
    }
    /* Fits by display width but the byte buffer is too small (many multi-byte
       characters): copy as many WHOLE characters as fit, never splitting one. */
    if ((int)src_width <= width) {
        size_t limit = dst_size - 1;
        size_t pos = 0;
        for (;;) {
            size_t clen = 1;
            while (src[pos + clen] != '\0' &&
                   utf8_is_continuation((unsigned char)src[pos + clen])) {
                clen++;
            }
            if (src[pos] == '\0' || pos + clen > limit) break;
            pos += clen;
        }
        memcpy(dst, src, pos);
        dst[pos] = '\0';
        return;
    }

    if (width <= 0) {
        dst[0] = '\0';
        return;
    }

    /* Too narrow for an ellipsis: cut to "width" characters with no dots. */
    if (width <= 3) {
        keep_chars = (size_t)width;
        copy_bytes = utf8_byte_len_for_width(src, keep_chars);
        /* Shrink to fit the buffer, then back off to a character boundary so a
           multi-byte character is never cut in half. */
        while (copy_bytes + 1 > dst_size) copy_bytes--;
        while (copy_bytes > 0 && utf8_is_continuation((unsigned char)src[copy_bytes])) {
            copy_bytes--;
        }
        memcpy(dst, src, copy_bytes);
        dst[copy_bytes] = '\0';
        return;
    }

    /* Keep (width - 3) characters, then append "..." for a total of "width". */
    keep_chars = (size_t)(width - 3);
    copy_bytes = utf8_byte_len_for_width(src, keep_chars);

    /* Make sure the bytes plus "...\0" fit the destination buffer. */
    while (copy_bytes + 4 > dst_size && keep_chars > 0) {
        keep_chars--;
        copy_bytes = utf8_byte_len_for_width(src, keep_chars);
    }
    if (copy_bytes + 4 > dst_size) {            /* extreme: tiny buffer */
        /* No room for text plus "...". Copy as many WHOLE characters as fit in
           (dst_size - 1) bytes, so a multi-byte character is never split. */
        size_t limit = dst_size - 1;
        size_t pos = 0;
        for (;;) {
            size_t clen = 1;
            while (src[pos + clen] != '\0' &&
                   utf8_is_continuation((unsigned char)src[pos + clen])) {
                clen++;
            }
            if (src[pos] == '\0' || pos + clen > limit) break;
            pos += clen;
        }
        memcpy(dst, src, pos);
        dst[pos] = '\0';
        return;
    }

    memcpy(dst, src, copy_bytes);
    dst[copy_bytes] = '.';
    dst[copy_bytes + 1] = '.';
    dst[copy_bytes + 2] = '.';
    dst[copy_bytes + 3] = '\0';
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

    len = (int)utf8_width(local);   /* pad by visible width, not bytes */
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
    len = (int)utf8_width(local);   /* pad by visible width, not bytes */

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
    len = (int)utf8_width(local);   /* center by visible width, not bytes */
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
    char line[MAX_NAME + MAX_VALUE + 16];

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

static int label_width_from_names(char names[][MAX_NAME], int count) {
    int width = 4;
    int i;

    for (i = 0; i < count; i++) {
        int len = (int)strlen(names[i]);
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
/* ============================================================================
 *  Data layer - everything below talks to SQLite. The UI layer above never
 *  touches SQL directly; it calls these helpers. All queries use prepared
 *  statements with bound parameters, so user text can never be interpreted as
 *  SQL (no injection possible).
 *
 *  Schema:
 *    categories(id INTEGER PK, name TEXT UNIQUE, position INTEGER)
 *    fields(id INTEGER PK, category_id INTEGER, name TEXT, position INTEGER)
 *    items(id INTEGER PK, category_id INTEGER, seq INTEGER, created TEXT)
 *    values(item_id INTEGER, field_id INTEGER, value TEXT)
 *
 *  "seq" is the per-category 1..N number shown to the user. It is recomputed
 *  after deletes so the list never has gaps.
 * ========================================================================== */

/* Show a database error to the user without crashing. */
static void db_error(const char *what) {
    print_indent(get_layout().left);
    printf("%s" "Database error: %s" "%s\n",
           COLOR_RED,
           what != NULL ? what : "unknown",
           COLOR_RESET);
}

/* Run a simple SQL statement that returns no rows. Returns 1 on success. */
static int db_exec(const char *sql) {
    char *err = NULL;
    if (g_db == NULL) return 0;
    if (sqlite3_exec(g_db, sql, NULL, NULL, &err) != SQLITE_OK) {
        db_error(err);
        sqlite3_free(err);
        return 0;
    }
    return 1;
}

/* Open the database and make sure the schema exists. Returns 1 on success. */
static int db_open(void) {
    static const char *schema =
        "PRAGMA journal_mode=WAL;"          /* durable + fast, survives crashes */
        "PRAGMA synchronous=FULL;"          /* never lose a committed change */
        "PRAGMA foreign_keys=ON;"
        "CREATE TABLE IF NOT EXISTS categories("
        "  id INTEGER PRIMARY KEY,"
        "  name TEXT NOT NULL UNIQUE,"
        "  position INTEGER NOT NULL DEFAULT 0);"
        "CREATE TABLE IF NOT EXISTS fields("
        "  id INTEGER PRIMARY KEY,"
        "  category_id INTEGER NOT NULL REFERENCES categories(id) ON DELETE CASCADE,"
        "  name TEXT NOT NULL,"
        "  position INTEGER NOT NULL DEFAULT 0);"
        "CREATE TABLE IF NOT EXISTS items("
        "  id INTEGER PRIMARY KEY,"
        "  category_id INTEGER NOT NULL REFERENCES categories(id) ON DELETE CASCADE,"
        "  seq INTEGER NOT NULL,"
        "  created TEXT NOT NULL DEFAULT '');"
        "CREATE TABLE IF NOT EXISTS item_values("
        "  item_id INTEGER NOT NULL REFERENCES items(id) ON DELETE CASCADE,"
        "  field_id INTEGER NOT NULL REFERENCES fields(id) ON DELETE CASCADE,"
        "  value TEXT NOT NULL DEFAULT '',"
        "  PRIMARY KEY(item_id, field_id));"
        "CREATE INDEX IF NOT EXISTS idx_fields_cat ON fields(category_id, position);"
        "CREATE INDEX IF NOT EXISTS idx_items_cat ON items(category_id, seq);"
        "CREATE INDEX IF NOT EXISTS idx_values_item ON item_values(item_id);";

    if (sqlite3_open(DB_FILE, &g_db) != SQLITE_OK) {
        db_error(sqlite3_errmsg(g_db));
        return 0;
    }
    /* Wait up to 5s if the file is briefly locked instead of failing. */
    sqlite3_busy_timeout(g_db, 5000);
    return db_exec(schema);
}

static void db_close(void) {
    if (g_db != NULL) {
        sqlite3_close(g_db);
        g_db = NULL;
    }
}

/* ---- small query helpers ---- */

/* Returns a single integer from a query (e.g. COUNT). default_value on error. */
static long db_query_long(const char *sql, int bind_id, long default_value) {
    sqlite3_stmt *st = NULL;
    long result = default_value;

    if (sqlite3_prepare_v2(g_db, sql, -1, &st, NULL) != SQLITE_OK) return default_value;
    if (bind_id >= 0) sqlite3_bind_int(st, 1, bind_id);
    if (sqlite3_step(st) == SQLITE_ROW) result = (long)sqlite3_column_int64(st, 0);
    sqlite3_finalize(st);
    return result;
}

static int total_categories(void) {
    return (int)db_query_long("SELECT COUNT(*) FROM categories;", -1, 0);
}

static int total_items(void) {
    return (int)db_query_long("SELECT COUNT(*) FROM items;", -1, 0);
}

/* Looks up a category id by its position in the list (1-based). 0 if none. */
static sqlite3_int64 category_id_at(int list_index) {
    sqlite3_stmt *st = NULL;
    sqlite3_int64 id = 0;

    if (sqlite3_prepare_v2(g_db,
            "SELECT id FROM categories ORDER BY position, id LIMIT 1 OFFSET ?;",
            -1, &st, NULL) != SQLITE_OK) return 0;
    sqlite3_bind_int(st, 1, list_index);
    if (sqlite3_step(st) == SQLITE_ROW) id = sqlite3_column_int64(st, 0);
    sqlite3_finalize(st);
    return id;
}

/* Copies a category's name into out. Returns 1 if found. */
static int category_name(sqlite3_int64 cat_id, char *out, size_t out_size) {
    sqlite3_stmt *st = NULL;
    int found = 0;

    if (out == NULL || out_size == 0) return 0;
    out[0] = '\0';
    if (sqlite3_prepare_v2(g_db, "SELECT name FROM categories WHERE id=?;",
                           -1, &st, NULL) != SQLITE_OK) return 0;
    sqlite3_bind_int64(st, 1, cat_id);
    if (sqlite3_step(st) == SQLITE_ROW) {
        const unsigned char *txt = sqlite3_column_text(st, 0);
        safe_copy(out, out_size, (const char *)txt);
        found = 1;
    }
    sqlite3_finalize(st);
    return found;
}

/* Does a category with this name already exist? */
static int category_exists(const char *name) {
    sqlite3_stmt *st = NULL;
    int exists = 0;

    if (sqlite3_prepare_v2(g_db,
            "SELECT 1 FROM categories WHERE name=? COLLATE NOCASE LIMIT 1;",
            -1, &st, NULL) != SQLITE_OK) return 0;
    sqlite3_bind_text(st, 1, name, -1, SQLITE_TRANSIENT);
    if (sqlite3_step(st) == SQLITE_ROW) exists = 1;
    sqlite3_finalize(st);
    return exists;
}

/* Creates a category, returns its id, or 0 on failure. */
static sqlite3_int64 category_create(const char *name) {
    sqlite3_stmt *st = NULL;
    sqlite3_int64 id = 0;
    int next_pos = (int)db_query_long(
        "SELECT COALESCE(MAX(position)+1,0) FROM categories;", -1, 0);

    if (sqlite3_prepare_v2(g_db,
            "INSERT INTO categories(name, position) VALUES(?, ?);",
            -1, &st, NULL) != SQLITE_OK) return 0;
    sqlite3_bind_text(st, 1, name, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(st, 2, next_pos);
    if (sqlite3_step(st) == SQLITE_DONE) id = sqlite3_last_insert_rowid(g_db);
    sqlite3_finalize(st);
    return id;
}

/* Adds a field to a category. Returns 1 on success, 0 on failure,
   -2 if a field with the same name already exists (duplicate). */
static int field_add(sqlite3_int64 cat_id, const char *name) {
    sqlite3_stmt *st = NULL;
    int dup = 0;
    int next_pos;
    int ok = 0;

    if (sqlite3_prepare_v2(g_db,
            "SELECT 1 FROM fields WHERE category_id=? AND name=? COLLATE NOCASE;",
            -1, &st, NULL) != SQLITE_OK) return 0;
    sqlite3_bind_int64(st, 1, cat_id);
    sqlite3_bind_text(st, 2, name, -1, SQLITE_TRANSIENT);
    if (sqlite3_step(st) == SQLITE_ROW) dup = 1;
    sqlite3_finalize(st);
    if (dup) return -2;

    next_pos = (int)db_query_long(
        "SELECT COALESCE(MAX(position)+1,0) FROM fields WHERE category_id=?;",
        (int)cat_id, 0);

    if (sqlite3_prepare_v2(g_db,
            "INSERT INTO fields(category_id, name, position) VALUES(?, ?, ?);",
            -1, &st, NULL) != SQLITE_OK) return 0;
    sqlite3_bind_int64(st, 1, cat_id);
    sqlite3_bind_text(st, 2, name, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(st, 3, next_pos);
    if (sqlite3_step(st) == SQLITE_DONE) ok = 1;
    sqlite3_finalize(st);
    return ok;
}

static int field_count(sqlite3_int64 cat_id) {
    return (int)db_query_long(
        "SELECT COUNT(*) FROM fields WHERE category_id=?;", (int)cat_id, 0);
}

/* Loads a category's field names and ids (ordered). Returns the count, capped
   at max_fields. */
static int field_load(sqlite3_int64 cat_id,
                      char names[][MAX_NAME], sqlite3_int64 *ids, int max_fields) {
    sqlite3_stmt *st = NULL;
    int n = 0;

    if (sqlite3_prepare_v2(g_db,
            "SELECT id, name FROM fields WHERE category_id=? ORDER BY position, id;",
            -1, &st, NULL) != SQLITE_OK) return 0;
    sqlite3_bind_int64(st, 1, cat_id);
    while (n < max_fields && sqlite3_step(st) == SQLITE_ROW) {
        if (ids != NULL) ids[n] = sqlite3_column_int64(st, 0);
        safe_copy(names[n], MAX_NAME, (const char *)sqlite3_column_text(st, 1));
        n++;
    }
    sqlite3_finalize(st);
    return n;
}

static int count_items_in_category(sqlite3_int64 cat_id) {
    return (int)db_query_long(
        "SELECT COUNT(*) FROM items WHERE category_id=?;", (int)cat_id, 0);
}

/* Renumber a category's items to 1..N by current seq order, closing any gap. */
static int renumber_category(sqlite3_int64 cat_id) {
    /* Two-step to avoid UNIQUE clashes is not needed (seq is not unique), so a
       single correlated update suffices and runs inside the caller's
       transaction. */
    sqlite3_stmt *st = NULL;
    int ok = 0;

    if (sqlite3_prepare_v2(g_db,
            "WITH ordered AS ("
            "  SELECT id, ROW_NUMBER() OVER (ORDER BY seq, id) AS rn"
            "  FROM items WHERE category_id=?1)"
            "UPDATE items SET seq=(SELECT rn FROM ordered WHERE ordered.id=items.id)"
            "  WHERE category_id=?1;",
            -1, &st, NULL) != SQLITE_OK) {
        return 0;
    }
    sqlite3_bind_int64(st, 1, cat_id);
    if (sqlite3_step(st) == SQLITE_DONE) ok = 1;
    sqlite3_finalize(st);
    return ok;
}

/* Finds an item's row id from its per-category seq number. 0 if not found. */
static sqlite3_int64 item_id_by_seq(sqlite3_int64 cat_id, int seq) {
    sqlite3_stmt *st = NULL;
    sqlite3_int64 id = 0;

    if (sqlite3_prepare_v2(g_db,
            "SELECT id FROM items WHERE category_id=? AND seq=?;",
            -1, &st, NULL) != SQLITE_OK) return 0;
    sqlite3_bind_int64(st, 1, cat_id);
    sqlite3_bind_int(st, 2, seq);
    if (sqlite3_step(st) == SQLITE_ROW) id = sqlite3_column_int64(st, 0);
    sqlite3_finalize(st);
    return id;
}

/* Creates a new item in a category with a fresh sequential seq and ISO date,
   then stores its field values. Returns the new item id, or 0 on failure.
   values[] aligns with the fields returned by field_load. */
static sqlite3_int64 item_create(sqlite3_int64 cat_id,
                                 char values[][MAX_VALUE], int value_count) {
    sqlite3_stmt *st = NULL;
    sqlite3_int64 item_id = 0;
    sqlite3_int64 field_ids[MAX_FIELDS];
    char field_names[MAX_FIELDS][MAX_NAME];
    int nf;
    int i;
    int next_seq;
    char created[32];

    if (!db_exec("BEGIN IMMEDIATE;")) return 0;

    next_seq = count_items_in_category(cat_id) + 1;
    iso8601_now(created, sizeof(created));

    if (sqlite3_prepare_v2(g_db,
            "INSERT INTO items(category_id, seq, created) VALUES(?, ?, ?);",
            -1, &st, NULL) != SQLITE_OK) { db_exec("ROLLBACK;"); return 0; }
    sqlite3_bind_int64(st, 1, cat_id);
    sqlite3_bind_int(st, 2, next_seq);
    sqlite3_bind_text(st, 3, created, -1, SQLITE_TRANSIENT);
    if (sqlite3_step(st) != SQLITE_DONE) { sqlite3_finalize(st); db_exec("ROLLBACK;"); return 0; }
    sqlite3_finalize(st);
    item_id = sqlite3_last_insert_rowid(g_db);

    nf = field_load(cat_id, field_names, field_ids, MAX_FIELDS);
    for (i = 0; i < nf && i < value_count; i++) {
        if (sqlite3_prepare_v2(g_db,
                "INSERT INTO item_values(item_id, field_id, value) VALUES(?, ?, ?);",
                -1, &st, NULL) != SQLITE_OK) { db_exec("ROLLBACK;"); return 0; }
        sqlite3_bind_int64(st, 1, item_id);
        sqlite3_bind_int64(st, 2, field_ids[i]);
        sqlite3_bind_text(st, 3, values[i], -1, SQLITE_TRANSIENT);
        if (sqlite3_step(st) != SQLITE_DONE) { sqlite3_finalize(st); db_exec("ROLLBACK;"); return 0; }
        sqlite3_finalize(st);
    }

    if (!db_exec("COMMIT;")) { db_exec("ROLLBACK;"); return 0; }
    return item_id;
}

/* Reads the created timestamp of an item. */
static void item_created(sqlite3_int64 item_id, char *out, size_t out_size) {
    sqlite3_stmt *st = NULL;
    if (out == NULL || out_size == 0) return;
    out[0] = '\0';
    if (sqlite3_prepare_v2(g_db, "SELECT created FROM items WHERE id=?;",
                           -1, &st, NULL) != SQLITE_OK) return;
    sqlite3_bind_int64(st, 1, item_id);
    if (sqlite3_step(st) == SQLITE_ROW)
        safe_copy(out, out_size, (const char *)sqlite3_column_text(st, 0));
    sqlite3_finalize(st);
}

/* Reads one field value of an item by field id. */
static void item_value(sqlite3_int64 item_id, sqlite3_int64 field_id,
                       char *out, size_t out_size) {
    sqlite3_stmt *st = NULL;
    if (out == NULL || out_size == 0) return;
    out[0] = '\0';
    if (sqlite3_prepare_v2(g_db,
            "SELECT value FROM item_values WHERE item_id=? AND field_id=?;",
            -1, &st, NULL) != SQLITE_OK) return;
    sqlite3_bind_int64(st, 1, item_id);
    sqlite3_bind_int64(st, 2, field_id);
    if (sqlite3_step(st) == SQLITE_ROW)
        safe_copy(out, out_size, (const char *)sqlite3_column_text(st, 0));
    sqlite3_finalize(st);
}

/* Sets one field value of an item (insert or update). Returns 1 on success. */
static int item_value_set(sqlite3_int64 item_id, sqlite3_int64 field_id,
                          const char *value) {
    sqlite3_stmt *st = NULL;
    int ok = 0;
    if (sqlite3_prepare_v2(g_db,
            "INSERT INTO item_values(item_id, field_id, value) VALUES(?, ?, ?)"
            " ON CONFLICT(item_id, field_id) DO UPDATE SET value=excluded.value;",
            -1, &st, NULL) != SQLITE_OK) return 0;
    sqlite3_bind_int64(st, 1, item_id);
    sqlite3_bind_int64(st, 2, field_id);
    sqlite3_bind_text(st, 3, value, -1, SQLITE_TRANSIENT);
    if (sqlite3_step(st) == SQLITE_DONE) ok = 1;
    sqlite3_finalize(st);
    return ok;
}

/* Deletes an item and renumbers its category. Returns 1 on success. */
static int item_delete(sqlite3_int64 cat_id, sqlite3_int64 item_id) {
    sqlite3_stmt *st = NULL;
    int ok = 0;

    if (!db_exec("BEGIN IMMEDIATE;")) return 0;
    if (sqlite3_prepare_v2(g_db, "DELETE FROM items WHERE id=?;",
                           -1, &st, NULL) != SQLITE_OK) { db_exec("ROLLBACK;"); return 0; }
    sqlite3_bind_int64(st, 1, item_id);
    if (sqlite3_step(st) == SQLITE_DONE) ok = 1;
    sqlite3_finalize(st);
    if (ok) ok = renumber_category(cat_id);
    if (ok && db_exec("COMMIT;")) return 1;
    db_exec("ROLLBACK;");
    return 0;
}

static int category_delete(sqlite3_int64 cat_id) {
    sqlite3_stmt *st = NULL;
    int ok = 0;
    if (sqlite3_prepare_v2(g_db, "DELETE FROM categories WHERE id=?;",
                           -1, &st, NULL) != SQLITE_OK) return 0;
    sqlite3_bind_int64(st, 1, cat_id);
    if (sqlite3_step(st) == SQLITE_DONE) ok = 1;
    sqlite3_finalize(st);
    return ok;
}
/* ============================================================================
 *  Operations layer - the menu actions. Same look and behavior as before, but
 *  every action reads/writes through the SQLite data layer above.
 * ========================================================================== */

/* Builds a short "FieldA: x | FieldB: y" preview for an item (first 2 fields). */
static void build_item_preview(sqlite3_int64 item_id, sqlite3_int64 cat_id,
                               char *out, size_t out_size) {
    char names[MAX_FIELDS][MAX_NAME];
    sqlite3_int64 ids[MAX_FIELDS];
    int nf;
    int f;
    int shown = 0;

    if (out == NULL || out_size == 0) return;
    out[0] = '\0';

    nf = field_load(cat_id, names, ids, MAX_FIELDS);
    for (f = 0; f < nf; f++) {
        char value[MAX_VALUE];
        item_value(item_id, ids[f], value, sizeof(value));
        if (value[0] != '\0') {
            char piece[256];
            size_t used = strlen(out);
            int n = snprintf(piece, sizeof(piece), "%s%s: %.80s",
                             shown > 0 ? " | " : "", names[f], value);
            if (n < 0) continue;
            if (used + (size_t)n + 1 < out_size) {
                memcpy(out + used, piece, (size_t)n + 1);
                shown++;
            }
            if (shown >= 2) break;
        }
    }
    if (shown == 0) safe_copy(out, out_size, "empty item");
}

static void print_item_table_row(sqlite3_int64 item_id, sqlite3_int64 cat_id,
                                 int seq, const char *cat_name,
                                 int id_w, int category_w, int preview_w) {
    char idbuf[32];
    char preview[512];

    snprintf(idbuf, sizeof(idbuf), "%d", seq);
    build_item_preview(item_id, cat_id, preview, sizeof(preview));
    ui_table_row(idbuf, cat_name, preview, id_w, category_w, preview_w);
}

static void view_item(sqlite3_int64 cat_id, int seq) {
    sqlite3_int64 item_id;
    char cat[MAX_NAME];
    char created[32];
    char names[MAX_FIELDS][MAX_NAME];
    sqlite3_int64 ids[MAX_FIELDS];
    char title[160];
    int nf;
    int f;
    Layout lay;

    item_id = item_id_by_seq(cat_id, seq);
    if (item_id == 0) return;
    category_name(cat_id, cat, sizeof(cat));

    snprintf(title, sizeof(title), "Viewing item ID %d", seq);
    ui_header(title, cat);

    lay = get_layout();
    ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);

    item_created(item_id, created, sizeof(created));
    if (created[0] != '\0') ui_key_value("Created", created);

    nf = field_load(cat_id, names, ids, MAX_FIELDS);
    for (f = 0; f < nf; f++) {
        char value[MAX_VALUE];
        item_value(item_id, ids[f], value, sizeof(value));
        ui_key_value(names[f], value);
    }

    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
    pause_enter();
}

static void list_items_in_category(sqlite3_int64 cat_id) {
    char cat[MAX_NAME];
    sqlite3_stmt *st = NULL;
    int id_w;
    int category_w;
    int preview_w;
    int shown = 0;
    int choice;

    category_name(cat_id, cat, sizeof(cat));
    ui_header("List items", cat);
    ui_items_table_begin(&id_w, &category_w, &preview_w);

    if (sqlite3_prepare_v2(g_db,
            "SELECT id, seq FROM items WHERE category_id=? ORDER BY seq;",
            -1, &st, NULL) == SQLITE_OK) {
        sqlite3_bind_int64(st, 1, cat_id);
        while (sqlite3_step(st) == SQLITE_ROW) {
            sqlite3_int64 item_id = sqlite3_column_int64(st, 0);
            int seq = sqlite3_column_int(st, 1);
            print_item_table_row(item_id, cat_id, seq, cat, id_w, category_w, preview_w);
            shown++;
            if (shown % PAGE_LINES == 0) {
                ui_items_table_end();
                pause_enter();
                ui_header("List items", cat);
                ui_items_table_begin(&id_w, &category_w, &preview_w);
            }
        }
        sqlite3_finalize(st);
    }

    if (shown == 0) {
        ui_table_row("-", cat, "No items registered yet.", id_w, category_w, preview_w);
    }
    ui_items_table_end();

    if (shown == 0) { pause_enter(); return; }

    choice = read_int_range("Item ID to view, or 0:", 0, INT_MAX);
    if (choice != 0 && choice != INPUT_CANCEL) {
        if (item_id_by_seq(cat_id, choice) != 0) {
            view_item(cat_id, choice);
        } else {
            print_indent(get_layout().left);
            printf("%s" "Item not found.\n" "%s", COLOR_YELLOW, COLOR_RESET);
            pause_enter();
        }
    }
}

static void add_item(sqlite3_int64 cat_id) {
    char cat[MAX_NAME];
    char names[MAX_FIELDS][MAX_NAME];
    sqlite3_int64 ids[MAX_FIELDS];
    char values[MAX_FIELDS][MAX_VALUE];
    int nf;
    int f;
    int label_width;
    sqlite3_int64 new_id;
    Layout lay;

    category_name(cat_id, cat, sizeof(cat));
    ui_header("Add new item", cat);
    lay = get_layout();

    nf = field_load(cat_id, names, ids, MAX_FIELDS);
    if (nf <= 0) {
        ui_message_box("This category has no fields. Add fields first.", COLOR_YELLOW);
        pause_enter();
        return;
    }

    ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
    ui_center_line(lay, "Fill the custom fields", COLOR_GREEN);
    ui_line(lay, "Leave optional fields empty if you want.", COLOR_DIM);
    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
    putchar('\n');

    label_width = label_width_from_names(names, nf);

    for (f = 0; f < nf; f++) {
        values[f][0] = '\0';
        if (!read_line_aligned(names[f], label_width, values[f], sizeof(values[f]))) {
            ui_message_box("Input canceled. Item was not saved.", COLOR_YELLOW);
            pause_enter();
            return;
        }
    }

    new_id = item_create(cat_id, values, nf);
    if (new_id != 0) {
        char message[96];
        int seq = (int)db_query_long("SELECT seq FROM items WHERE id=?;", (int)new_id, 0);
        snprintf(message, sizeof(message), "Item saved with ID %d.", seq);
        putchar('\n');
        ui_message_box(message, COLOR_GREEN);
    } else {
        ui_message_box("Save failed.", COLOR_RED);
    }
    pause_enter();
}

static void edit_item(sqlite3_int64 cat_id) {
    char cat[MAX_NAME];
    char names[MAX_FIELDS][MAX_NAME];
    sqlite3_int64 ids[MAX_FIELDS];
    sqlite3_int64 item_id;
    char title[160];
    int seq;
    int nf;
    int f;
    int label_width;
    int changed = 0;
    Layout lay;

    category_name(cat_id, cat, sizeof(cat));
    ui_header("Edit item", cat);
    seq = read_int_range("Item ID:", 1, INT_MAX);
    if (seq == INPUT_CANCEL) return;

    item_id = item_id_by_seq(cat_id, seq);
    if (item_id == 0) {
        ui_message_box("Item not found.", COLOR_YELLOW);
        pause_enter();
        return;
    }

    snprintf(title, sizeof(title), "Editing item ID %d", seq);
    ui_header(title, cat);
    lay = get_layout();

    nf = field_load(cat_id, names, ids, MAX_FIELDS);

    ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
    ui_center_line(lay, "Current values", COLOR_GREEN);
    for (f = 0; f < nf; f++) {
        char value[MAX_VALUE];
        item_value(item_id, ids[f], value, sizeof(value));
        ui_key_value(names[f], value);
    }
    ui_blank_line(lay);
    ui_line(lay, "Press ENTER without text to keep the current value.", COLOR_DIM);
    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
    putchar('\n');

    label_width = label_width_from_names(names, nf);

    if (!db_exec("BEGIN IMMEDIATE;")) { pause_enter(); return; }
    for (f = 0; f < nf; f++) {
        char line[MAX_VALUE];
        if (read_line_aligned(names[f], label_width, line, sizeof(line)) && line[0] != '\0') {
            if (item_value_set(item_id, ids[f], line)) changed = 1;
        }
    }

    if (changed && db_exec("COMMIT;")) {
        putchar('\n');
        ui_message_box("Item updated.", COLOR_GREEN);
    } else {
        db_exec("ROLLBACK;");
        putchar('\n');
        ui_message_box("No changes were saved.", COLOR_DIM);
    }
    pause_enter();
}

static void delete_item_ui(sqlite3_int64 cat_id) {
    char cat[MAX_NAME];
    sqlite3_int64 item_id;
    int seq;
    char question[160];

    category_name(cat_id, cat, sizeof(cat));
    ui_header("Delete item", cat);
    seq = read_int_range("Item ID:", 1, INT_MAX);
    if (seq == INPUT_CANCEL) return;

    item_id = item_id_by_seq(cat_id, seq);
    if (item_id == 0) {
        print_indent(get_layout().left);
        printf("%s" "Item not found.\n" "%s", COLOR_YELLOW, COLOR_RESET);
        pause_enter();
        return;
    }

    snprintf(question, sizeof(question), "Delete item ID %d permanently?", seq);
    if (confirm_action(question)) {
        if (item_delete(cat_id, item_id)) {
            print_indent(get_layout().left);
            printf("%s" "Item deleted.\n" "%s", COLOR_GREEN, COLOR_RESET);
        }
    } else {
        print_indent(get_layout().left);
        printf("%s" "Canceled.\n" "%s", COLOR_DIM, COLOR_RESET);
    }
    pause_enter();
}

/* Search. cat_id == 0 means search every category. Uses LIKE with an escaped
   pattern so the user's text is matched literally, not as wildcards. */
static void search_items(sqlite3_int64 cat_id) {
    char term[MAX_VALUE];
    char pattern[MAX_VALUE + 8];
    char subtitle[MAX_NAME];
    sqlite3_stmt *st = NULL;
    int id_w;
    int category_w;
    int preview_w;
    int found = 0;
    size_t i;
    size_t p = 0;

    if (cat_id != 0) category_name(cat_id, subtitle, sizeof(subtitle));
    else safe_copy(subtitle, sizeof(subtitle), "All categories");

    ui_header("Search", subtitle);
    if (!read_required_line("Search text:", term, sizeof(term))) return;

    /* Build a LIKE pattern: %term%, escaping % _ and the escape char itself. */
    pattern[p++] = '%';
    for (i = 0; term[i] != '\0' && p < sizeof(pattern) - 3; i++) {
        char ch = term[i];
        if (ch == '%' || ch == '_' || ch == '\\') pattern[p++] = '\\';
        pattern[p++] = ch;
    }
    pattern[p++] = '%';
    pattern[p] = '\0';

    ui_header("Search results", term);
    ui_items_table_begin(&id_w, &category_w, &preview_w);

    {
        const char *sql_all =
            "SELECT DISTINCT i.id, i.seq, c.id, c.name FROM items i "
            "JOIN categories c ON c.id=i.category_id "
            "LEFT JOIN item_values v ON v.item_id=i.id "
            "WHERE c.name LIKE ?1 ESCAPE '\\' "
            "   OR v.value LIKE ?1 ESCAPE '\\' "
            "ORDER BY c.position, i.seq;";
        const char *sql_one =
            "SELECT DISTINCT i.id, i.seq, c.id, c.name FROM items i "
            "JOIN categories c ON c.id=i.category_id "
            "LEFT JOIN item_values v ON v.item_id=i.id "
            "WHERE i.category_id=?2 AND (c.name LIKE ?1 ESCAPE '\\' "
            "   OR v.value LIKE ?1 ESCAPE '\\') "
            "ORDER BY i.seq;";

        if (sqlite3_prepare_v2(g_db, cat_id != 0 ? sql_one : sql_all,
                               -1, &st, NULL) == SQLITE_OK) {
            sqlite3_bind_text(st, 1, pattern, -1, SQLITE_TRANSIENT);
            if (cat_id != 0) sqlite3_bind_int64(st, 2, cat_id);
            while (sqlite3_step(st) == SQLITE_ROW) {
                sqlite3_int64 item_id = sqlite3_column_int64(st, 0);
                int seq = sqlite3_column_int(st, 1);
                sqlite3_int64 ccid = sqlite3_column_int64(st, 2);
                const char *cname = (const char *)sqlite3_column_text(st, 3);
                print_item_table_row(item_id, ccid, seq, cname, id_w, category_w, preview_w);
                found++;
                if (found % PAGE_LINES == 0) {
                    ui_items_table_end();
                    pause_enter();
                    ui_header("Search results", term);
                    ui_items_table_begin(&id_w, &category_w, &preview_w);
                }
            }
            sqlite3_finalize(st);
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

static void add_category_ui(void) {
    char name[MAX_NAME];
    sqlite3_int64 cat_id;
    int n;
    int i;

    ui_header("Create category", "Examples: Movies, Books, Places, Goals, Home Items");

    if (!read_required_line("Category name:", name, sizeof(name))) return;

    if (category_exists(name)) {
        print_indent(get_layout().left);
        printf("%s" "A category with this name already exists.\n" "%s", COLOR_YELLOW, COLOR_RESET);
        pause_enter();
        return;
    }

    cat_id = category_create(name);
    if (cat_id == 0) {
        print_indent(get_layout().left);
        printf("%s" "Could not create the category.\n" "%s", COLOR_RED, COLOR_RESET);
        pause_enter();
        return;
    }

    n = read_int_range("Custom fields:", 1, MAX_FIELDS);
    if (n == INPUT_CANCEL) {
        category_delete(cat_id);   /* undo: nothing was committed for the user */
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
        if (!read_required_line(prompt, field, sizeof(field))) break;

        r = field_add(cat_id, field);
        if (r == -2) {
            print_indent(get_layout().left);
            printf("%s" "Duplicated field ignored. Try another name.\n" "%s", COLOR_YELLOW, COLOR_RESET);
            i--;
        }
    }

    if (field_count(cat_id) == 0) {
        category_delete(cat_id);
        print_indent(get_layout().left);
        printf("%s" "Canceled. A category needs at least one field.\n" "%s", COLOR_DIM, COLOR_RESET);
        pause_enter();
        return;
    }

    putchar('\n');
    print_indent(get_layout().left);
    printf("%s" "Category created.\n" "%s", COLOR_GREEN, COLOR_RESET);
    pause_enter();
}

static void list_categories_table(void) {
    sqlite3_stmt *st = NULL;
    int num_w;
    int name_w;
    int info_w;
    int row = 0;
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

    if (sqlite3_prepare_v2(g_db,
            "SELECT id, name FROM categories ORDER BY position, id;",
            -1, &st, NULL) == SQLITE_OK) {
        while (sqlite3_step(st) == SQLITE_ROW) {
            sqlite3_int64 cid = sqlite3_column_int64(st, 0);
            const char *cname = (const char *)sqlite3_column_text(st, 1);
            char nbuf[16];
            char ibuf[80];
            row++;
            snprintf(nbuf, sizeof(nbuf), "%d", row);
            snprintf(ibuf, sizeof(ibuf), "%d item(s), %d field(s)",
                     count_items_in_category(cid), field_count(cid));
            ui_table_row(nbuf, cname, ibuf, num_w, name_w, info_w);
        }
        sqlite3_finalize(st);
    }

    if (row == 0) {
        ui_table_row("-", "No categories yet", "Create one first", num_w, name_w, info_w);
    }
    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
}

static void rename_category(sqlite3_int64 cat_id) {
    char cat[MAX_NAME];
    char newname[MAX_NAME];
    sqlite3_stmt *st = NULL;
    int ok = 0;

    category_name(cat_id, cat, sizeof(cat));
    ui_header("Rename category", cat);

    if (!read_required_line("New name:", newname, sizeof(newname))) return;

    if (strings_equal_ci(newname, cat)) {
        print_indent(get_layout().left);
        printf("%s" "The name did not change.\n" "%s", COLOR_DIM, COLOR_RESET);
        pause_enter();
        return;
    }
    if (category_exists(newname)) {
        print_indent(get_layout().left);
        printf("%s" "A category with this name already exists.\n" "%s", COLOR_YELLOW, COLOR_RESET);
        pause_enter();
        return;
    }

    if (sqlite3_prepare_v2(g_db, "UPDATE categories SET name=? WHERE id=?;",
                           -1, &st, NULL) == SQLITE_OK) {
        sqlite3_bind_text(st, 1, newname, -1, SQLITE_TRANSIENT);
        sqlite3_bind_int64(st, 2, cat_id);
        if (sqlite3_step(st) == SQLITE_DONE) ok = 1;
        sqlite3_finalize(st);
    }

    print_indent(get_layout().left);
    if (ok) printf("%s" "Category renamed.\n" "%s", COLOR_GREEN, COLOR_RESET);
    else printf("%s" "Could not rename.\n" "%s", COLOR_RED, COLOR_RESET);
    pause_enter();
}

static void delete_category_ui(sqlite3_int64 cat_id) {
    char cat[MAX_NAME];
    char question[200];

    category_name(cat_id, cat, sizeof(cat));
    ui_header("Delete category", cat);
    snprintf(question, sizeof(question),
             "Delete category '%s' and all its items?", cat);

    if (!confirm_action(question)) {
        print_indent(get_layout().left);
        printf("%s" "Canceled.\n" "%s", COLOR_DIM, COLOR_RESET);
        pause_enter();
        return;
    }

    if (category_delete(cat_id)) {
        print_indent(get_layout().left);
        printf("%s" "Category deleted.\n" "%s", COLOR_GREEN, COLOR_RESET);
    }
    pause_enter();
}

static void manage_fields(sqlite3_int64 cat_id) {
    char cat[MAX_NAME];

    category_name(cat_id, cat, sizeof(cat));

    for (;;) {
        char names[MAX_FIELDS][MAX_NAME];
        sqlite3_int64 ids[MAX_FIELDS];
        int nf;
        int i;
        int n_w;
        int field_w;
        int note_w;
        int choice;
        Layout lay;
        const char *items[][2] = {
            {"Add field", "Create a new custom column"},
            {"Rename field", "Keep all existing values"},
            {"Delete field", "Remove the column and values"},
            {"Back", "Return to category"}
        };
        const int nums[] = {1, 2, 3, 0};

        nf = field_load(cat_id, names, ids, MAX_FIELDS);

        ui_header("Manage fields", cat);
        lay = get_layout();
        n_w = 5;
        field_w = (int)((double)lay.inner * INV_PHI) - 4;
        if (field_w < 28) field_w = 28;
        note_w = lay.inner - n_w - field_w - 4;
        if (note_w < 16) note_w = 16;

        ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
        ui_table_header("NO", "FIELD", "STATUS", n_w, field_w, note_w);
        ui_rule(lay, '+', UI_HORIZONTAL, '+');
        if (nf == 0) {
            ui_table_row("-", "No fields", "Add one first", n_w, field_w, note_w);
        } else {
            for (i = 0; i < nf; i++) {
                char num[16];
                snprintf(num, sizeof(num), "%d", i + 1);
                ui_table_row(num, names[i], "active", n_w, field_w, note_w);
            }
        }
        ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
        putchar('\n');
        ui_menu_box("Field Actions", "Schema editor", items, nums, 4);

        choice = read_int_range("Choice:", 0, 3);
        if (choice == 0 || choice == INPUT_CANCEL) return;

        if (choice == 1) {
            char field[MAX_NAME];
            if (nf >= MAX_FIELDS) {
                print_indent(get_layout().left);
                printf("%s" "Field limit reached.\n" "%s", COLOR_YELLOW, COLOR_RESET);
                pause_enter();
                continue;
            }
            if (read_required_line("New field:", field, sizeof(field))) {
                int r = field_add(cat_id, field);
                if (r == -2) {
                    print_indent(get_layout().left);
                    printf("%s" "This field already exists.\n" "%s", COLOR_YELLOW, COLOR_RESET);
                } else if (r == 1) {
                    print_indent(get_layout().left);
                    printf("%s" "Field added.\n" "%s", COLOR_GREEN, COLOR_RESET);
                }
                pause_enter();
            }
        } else if (choice == 2) {
            int fi;
            char field[MAX_NAME];
            if (nf == 0) {
                print_indent(get_layout().left);
                printf("%s" "No fields to rename.\n" "%s", COLOR_YELLOW, COLOR_RESET);
                pause_enter();
                continue;
            }
            fi = read_int_range("Field number:", 1, nf);
            if (fi == INPUT_CANCEL) continue;
            fi = fi - 1;
            if (read_required_line("New field:", field, sizeof(field))) {
                sqlite3_stmt *st = NULL;
                int ok = 0;
                if (sqlite3_prepare_v2(g_db, "UPDATE fields SET name=? WHERE id=?;",
                                       -1, &st, NULL) == SQLITE_OK) {
                    sqlite3_bind_text(st, 1, field, -1, SQLITE_TRANSIENT);
                    sqlite3_bind_int64(st, 2, ids[fi]);
                    if (sqlite3_step(st) == SQLITE_DONE) ok = 1;
                    sqlite3_finalize(st);
                }
                print_indent(get_layout().left);
                if (ok) printf("%s" "Field renamed.\n" "%s", COLOR_GREEN, COLOR_RESET);
                else printf("%s" "Could not rename.\n" "%s", COLOR_RED, COLOR_RESET);
                pause_enter();
            }
        } else if (choice == 3) {
            int fi;
            char question[200];
            if (nf == 0) {
                print_indent(get_layout().left);
                printf("%s" "No fields to delete.\n" "%s", COLOR_YELLOW, COLOR_RESET);
                pause_enter();
                continue;
            }
            fi = read_int_range("Field number:", 1, nf);
            if (fi == INPUT_CANCEL) continue;
            fi = fi - 1;
            snprintf(question, sizeof(question),
                     "Delete field '%s' and all its values?", names[fi]);
            if (confirm_action(question)) {
                sqlite3_stmt *st = NULL;
                int ok = 0;
                if (sqlite3_prepare_v2(g_db, "DELETE FROM fields WHERE id=?;",
                                       -1, &st, NULL) == SQLITE_OK) {
                    sqlite3_bind_int64(st, 1, ids[fi]);
                    if (sqlite3_step(st) == SQLITE_DONE) ok = 1;
                    sqlite3_finalize(st);
                }
                print_indent(get_layout().left);
                if (ok) printf("%s" "Field deleted.\n" "%s", COLOR_GREEN, COLOR_RESET);
                else printf("%s" "Could not delete.\n" "%s", COLOR_RED, COLOR_RESET);
            } else {
                print_indent(get_layout().left);
                printf("%s" "Canceled.\n" "%s", COLOR_DIM, COLOR_RESET);
            }
            pause_enter();
        }
    }
}

static void category_menu(sqlite3_int64 cat_id) {
    for (;;) {
        char cat[MAX_NAME];
        char subtitle[160];
        int choice;
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

        if (!category_name(cat_id, cat, sizeof(cat))) return;  /* gone (deleted) */

        snprintf(subtitle, sizeof(subtitle), "%d item(s), %d field(s)",
                 count_items_in_category(cat_id), field_count(cat_id));

        ui_header(cat, subtitle);
        ui_menu_box("Category Menu", "Choose an action  -  ESC = back", items, nums, 9);

        choice = read_int_range("Choice:", 0, 8);
        if (choice == 0 || choice == INPUT_CANCEL) return;
        if (choice == 1) list_items_in_category(cat_id);
        else if (choice == 2) add_item(cat_id);
        else if (choice == 3) search_items(cat_id);
        else if (choice == 4) edit_item(cat_id);
        else if (choice == 5) delete_item_ui(cat_id);
        else if (choice == 6) manage_fields(cat_id);
        else if (choice == 7) rename_category(cat_id);
        else if (choice == 8) { delete_category_ui(cat_id); return; }
    }
}

static void open_category(void) {
    int total;
    int choice;

    ui_header("Categories", "Choose a number to open a category");
    list_categories_table();

    total = total_categories();
    if (total == 0) { pause_enter(); return; }

    choice = read_int_range("Open number, or 0:", 0, total);
    if (choice != INPUT_CANCEL && choice > 0) {
        sqlite3_int64 cid = category_id_at(choice - 1);
        if (cid != 0) category_menu(cid);
    }
}

static void show_stats(void) {
    sqlite3_stmt *st = NULL;
    int name_w;
    int info_w;
    int rows = 0;
    Layout lay;
    char tc[32];
    char ti[32];

    ui_header("Statistics", "Database overview");
    lay = get_layout();
    snprintf(tc, sizeof(tc), "%d", total_categories());
    snprintf(ti, sizeof(ti), "%d", total_items());

    ui_rule(lay, UI_TOP_LEFT, UI_HORIZONTAL, UI_TOP_RIGHT);
    ui_center_line(lay, "Vault Summary", COLOR_GREEN);
    ui_key_value("Total categories", tc);
    ui_key_value("Total items", ti);
    ui_key_value("Database file", DB_FILE);
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

    if (sqlite3_prepare_v2(g_db,
            "SELECT id, name FROM categories ORDER BY position, id;",
            -1, &st, NULL) == SQLITE_OK) {
        while (sqlite3_step(st) == SQLITE_ROW) {
            sqlite3_int64 cid = sqlite3_column_int64(st, 0);
            const char *cname = (const char *)sqlite3_column_text(st, 1);
            char info[80];
            rows++;
            snprintf(info, sizeof(info), "%d item(s), %d field(s)",
                     count_items_in_category(cid), field_count(cid));
            ui_table_row(cname, info, "", name_w, info_w, 0);
        }
        sqlite3_finalize(st);
    }
    if (rows == 0) {
        ui_table_row("No categories", "Create one first", "", name_w, info_w, 0);
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
    ui_line(lay, "4. Everything is stored in a SQLite database that scales to millions.", NULL);
    ui_blank_line(lay);
    ui_line(lay, "Every change is an ACID transaction, so your data is safe even on power loss.", COLOR_DIM);
    ui_rule(lay, UI_BOTTOM_LEFT, UI_HORIZONTAL, UI_BOTTOM_RIGHT);
    pause_enter();
}

static void create_demo_if_empty(void) {
    if (total_categories() != 0) return;
    if (confirm_action("No data yet. Create a small demo category?")) {
        sqlite3_int64 cid = category_create("Movies");
        if (cid != 0) {
            field_add(cid, "Title");
            field_add(cid, "Date");
            field_add(cid, "Rating");
            field_add(cid, "Notes");
        }
    }
}

static void export_text_report(void) {
    static const char *REPORT_FILE = "aureavault_report.txt";
    static const char *REPORT_TEMP = "aureavault_report.txt.tmp";
    FILE *fp;
    sqlite3_stmt *cst = NULL;

    ui_header("Text Report", "Export a printer-friendly summary of your vault.");

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
        fprintf(fp, "Categories: %d    Items: %d\n", total_categories(), total_items());
        fprintf(fp, "============================================================\n\n");
    }

    if (sqlite3_prepare_v2(g_db,
            "SELECT id, name FROM categories ORDER BY position, id;",
            -1, &cst, NULL) == SQLITE_OK) {
        while (sqlite3_step(cst) == SQLITE_ROW) {
            sqlite3_int64 cid = sqlite3_column_int64(cst, 0);
            const char *cname = (const char *)sqlite3_column_text(cst, 1);
            char names[MAX_FIELDS][MAX_NAME];
            sqlite3_int64 ids[MAX_FIELDS];
            int nf = field_load(cid, names, ids, MAX_FIELDS);
            sqlite3_stmt *ist = NULL;
            int shown = 0;

            fprintf(fp, "## %s\n", cname);
            fprintf(fp, "------------------------------------------------------------\n");

            if (sqlite3_prepare_v2(g_db,
                    "SELECT id, seq, created FROM items WHERE category_id=? ORDER BY seq;",
                    -1, &ist, NULL) == SQLITE_OK) {
                sqlite3_bind_int64(ist, 1, cid);
                while (sqlite3_step(ist) == SQLITE_ROW) {
                    sqlite3_int64 item_id = sqlite3_column_int64(ist, 0);
                    int seq = sqlite3_column_int(ist, 1);
                    const char *created = (const char *)sqlite3_column_text(ist, 2);
                    int f;
                    shown++;
                    fprintf(fp, "Item #%d\n", seq);
                    if (created != NULL && created[0] != '\0')
                        fprintf(fp, "  Created: %s\n", created);
                    for (f = 0; f < nf; f++) {
                        char value[MAX_VALUE];
                        item_value(item_id, ids[f], value, sizeof(value));
                        fprintf(fp, "  %s: %s\n", names[f], value);
                    }
                    fprintf(fp, "\n");
                }
                sqlite3_finalize(ist);
            }
            if (shown == 0) fprintf(fp, "(no items)\n\n");
        }
        sqlite3_finalize(cst);
    }

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

static void main_menu(void) {
    for (;;) {
        char subtitle[200];
        char left[160];
        char right[160];
        int choice;
        int cats = total_categories();
        int its = total_items();
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

        snprintf(subtitle, sizeof(subtitle), "%d categories | %d items | %s",
                 cats, its, DB_FILE);
        snprintf(left, sizeof(left), "Categories: %d", cats);
        snprintf(right, sizeof(right), "Items: %d", its);

        ui_header(APP_TAGLINE, subtitle);
        ui_status_box("Vault Status", left, right);
        putchar('\n');
        ui_menu_box("Main Menu", "Elegant catalog management  -  ESC = back", items, nums, 7);

        choice = read_int_range("Choice:", 0, 6);

        if (choice == INPUT_CANCEL) {
            if (g_input_canceled) { g_input_canceled = 0; continue; }
            ui_header("Goodbye", "Your life catalog is safe.");
            return;
        }
        if (choice == 0) {
            ui_header("Goodbye", "Your life catalog is safe.");
            return;
        }
        if (choice == 1) open_category();
        else if (choice == 2) add_category_ui();
        else if (choice == 3) search_items(0);
        else if (choice == 4) show_stats();
        else if (choice == 5) show_help();
        else if (choice == 6) export_text_report();
    }
}

static void choose_color_mode(void) {
    char line[16];
    int value;
    int invalid = 0;
    Layout lay;

    for (;;) {
        lay = get_layout();
        clear_screen();

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
            g_color = 1;
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
    choose_color_mode();

    if (!db_open()) {
        db_close();
        print_indent(get_layout().left);
        printf("%s" "Could not open the database. Exiting.\n" "%s", COLOR_RED, COLOR_RESET);
        return 1;
    }

    ui_header(APP_TAGLINE, "Database ready.");
    create_demo_if_empty();
    main_menu();

    db_close();
    return 0;
}
