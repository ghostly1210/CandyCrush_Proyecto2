/*
 * ============================================================
 * CANDY CRUSH - CC3086 Programación de Microprocesadores
 * Proyecto 2 - Fases 2 y 3
 * Universidad del Valle de Guatemala
 *
 * HILOS INDEPENDIENTES:
 * 1. thread_input    – Captura teclas del jugador
 * 2. thread_match    – Detecta combinaciones en el tablero
 * 3. thread_score    – Acumula el puntaje
 * 4. thread_render   – Redibuja el tablero en consola
 * 5. thread_gravity  – Hace caer dulces al haber huecos
 * 6. thread_refill   – Rellena con nuevos dulces
 *
 * SINCRONIZACIÓN:
 * - mutex_board  : protege el tablero
 * - mutex_game   : protege todo el estado (score, moves, flags)
 * - cond_match   : señala nuevas combinaciones al hilo score
 * - cond_gravity : señala huecos al hilo gravedad
 * - sem_render   : despierta el hilo de render
 * ============================================================
 */

#include <iostream>
#include <fstream>  
#include <string>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <unistd.h>
#include <termios.h>
#include <sys/ioctl.h>
#include <pthread.h>
#include <semaphore.h>

using namespace std;

// ── Dimensiones y reglas ────────────────────────────────────
#define ROWS        8
#define COLS        8
#define SCORE_GOAL  100
#define EASY_MOVES  20
#define HARD_MOVES  12
#define SCOREFILE   "scoreboard.txt"

// ── Colores ANSI ─────────────────────────────────────────────
#define RST   "\033[0m"
#define BOLD  "\033[1m"
#define C_RED "\033[31m"
#define C_GRN "\033[32m"
#define C_YEL "\033[33m"
#define C_BLU "\033[34m"
#define C_MAG "\033[35m"
#define C_CYN "\033[36m"
#define C_WHT "\033[37m"

// ── Dulces ───────────────────────────────────────────────────
// Los índices del tablero son: 0-6 = dulce normal, 7 = especial, -1 = vacío.
#define N_CANDY_EASY 5
#define N_CANDY_HARD 7
static const char* CSYM[] = { "🍬","🍭","🍫","🍰","🍩","🍪","🌟" };
#define IDX_SPECIAL  7
#define IDX_EMPTY   -1

// ── Teclas ───────────────────────────────────────────────────
#define K_UP    'w'
#define K_DOWN  's'
#define K_LEFT  'a'
#define K_RIGHT 'd'
#define K_SEL   ' '
#define K_QUIT  'q'

// ============================================================
//  ESTADO GLOBAL
// ============================================================
static int  board[ROWS][COLS];
static bool marked[ROWS][COLS];

static int  g_score        = 0;
static int  g_moves        = 0;
static int  g_pending_pts  = 0;   
static bool g_running      = true;
static bool g_game_over    = false;
static bool g_won          = false;
static bool g_match_ready  = false;  
static bool g_need_gravity = false;  
static bool g_need_refill  = false;  

static int  g_cr = 0, g_cc = 0;     // cursor
static int  g_sr = -1, g_sc = -1;   // celda seleccionada
static bool g_selected = false;

static int  g_mode       = 1;
static int  g_ncandy     = N_CANDY_EASY;
static char g_name[64]   = "Jugador";

// ── Primitivas ───────────────────────────────────────────────
static pthread_mutex_t mutex_board = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t mutex_game  = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  cond_match  = PTHREAD_COND_INITIALIZER;
static pthread_cond_t  cond_grav   = PTHREAD_COND_INITIALIZER;
static sem_t           sem_render;

// ── Terminal ─────────────────────────────────────────────────
static struct termios orig_term;

void term_raw() {
    tcgetattr(STDIN_FILENO, &orig_term);
    struct termios t = orig_term;
    t.c_lflag &= ~(ICANON | ECHO);
    t.c_cc[VMIN]  = 0;
    t.c_cc[VTIME] = 1;   
    tcsetattr(STDIN_FILENO, TCSAFLUSH, &t);
}

void term_restore() { tcsetattr(STDIN_FILENO, TCSAFLUSH, &orig_term); }
void clrscr()  { printf("\033[H\033[2J"); fflush(stdout); }
void hidecur() { printf("\033[?25l");     fflush(stdout); }
void showcur() { printf("\033[?25h");     fflush(stdout); }
void gotoxy(int r, int c) { printf("\033[%d;%dH", r, c); fflush(stdout); }

// ============================================================
//  TABLERO
// ============================================================
static int rand_candy() { return rand() % g_ncandy; }

static void init_board() {
    for (int i = 0; i < ROWS; i++)
        for (int j = 0; j < COLS; j++) {
            int c;
            int tries = 0;
            do {
                c = rand_candy();
                bool h = (j>=2 && board[i][j-1]==c && board[i][j-2]==c);
                bool v = (i>=2 && board[i-1][j]==c && board[i-2][j]==c);
                if (!h && !v) break;
            } while (++tries < 20);
            board[i][j] = c;
        }
}

// ============================================================
//  HILO 3: PUNTAJE
// ============================================================
static void* thread_score_fn(void*) {
    while (true) {
        pthread_mutex_lock(&mutex_game);
        while (!g_match_ready && g_running)
            pthread_cond_wait(&cond_match, &mutex_game);

        if (!g_running && !g_match_ready) {
            pthread_mutex_unlock(&mutex_game);
            break;
        }

        int pts       = g_pending_pts;
        g_pending_pts = 0;
        g_match_ready = false;
        pthread_mutex_unlock(&mutex_game);

        if (pts > 0) {
            pthread_mutex_lock(&mutex_game);
            g_score += pts;
            if (!g_game_over && g_score >= SCORE_GOAL) {
                g_won      = true;
                g_game_over= true;
                g_running  = false;
                pthread_cond_broadcast(&cond_match);
                pthread_cond_broadcast(&cond_grav);
            }
            pthread_mutex_unlock(&mutex_game);
            sem_post(&sem_render);
        }
    }
    return NULL;
}

// ============================================================
//  HILO 2: DETECCIÓN DE COMBINACIONES
// ============================================================
static void* thread_match_fn(void*) {
    while (true) {
        pthread_mutex_lock(&mutex_game);
        bool alive = g_running;
        pthread_mutex_unlock(&mutex_game);
        if (!alive) break;

        pthread_mutex_lock(&mutex_board);
        memset(marked, 0, sizeof(marked));
        int pts   = 0;
        bool found= false;

        // Horizontal
        for (int i = 0; i < ROWS; i++)
            for (int j = 0; j < COLS-2; ) {
                int c = board[i][j];
                if (c == IDX_EMPTY) { j++; continue; }
                int len = 1;
                while (j+len < COLS && board[i][j+len] == c) len++;
                if (len >= 3) {
                    for (int k=0;k<len;k++) marked[i][j+k]=true;
                    pts += len*10; found = true;
                    if (len >= 4) board[i][j+len/2] = IDX_SPECIAL;
                }
                j += len;
            }

        // Vertical
        for (int j = 0; j < COLS; j++)
            for (int i = 0; i < ROWS-2; ) {
                int c = board[i][j];
                if (c == IDX_EMPTY) { i++; continue; }
                int len = 1;
                while (i+len < ROWS && board[i+len][j] == c) len++;
                if (len >= 3) {
                    for (int k=0;k<len;k++) marked[i+k][j]=true;
                    pts += len*10; found = true;
                    if (len >= 4) board[i+len/2][j] = IDX_SPECIAL;
                }
                i += len;
            }

        if (found) {
            for (int i=0;i<ROWS;i++)
                for (int j=0;j<COLS;j++)
                    if (marked[i][j]) board[i][j] = IDX_EMPTY;

            for (int i=0;i<ROWS;i++)
                for (int j=0;j<COLS;j++)
                    if (board[i][j] == IDX_SPECIAL) {
                        for (int k=0;k<COLS;k++) board[i][k] = IDX_EMPTY;
                        pts += COLS*5;
                    }
        }
        pthread_mutex_unlock(&mutex_board);

        if (found) {
            pthread_mutex_lock(&mutex_game);
            g_pending_pts  += pts;
            g_match_ready   = true;
            g_need_gravity  = true;
            pthread_cond_signal(&cond_match);
            pthread_cond_signal(&cond_grav);
            pthread_mutex_unlock(&mutex_game);
            sem_post(&sem_render);
        }

        usleep(150000);
    }
    return NULL;
}

// ============================================================
//  HILO 5: GRAVEDAD
// ============================================================
static void* thread_gravity_fn(void*) {
    while (true) {
        pthread_mutex_lock(&mutex_game);
        while (!g_need_gravity && g_running)
            pthread_cond_wait(&cond_grav, &mutex_game);
        if (!g_running && !g_need_gravity) {
            pthread_mutex_unlock(&mutex_game);
            break;
        }
        g_need_gravity = false;
        pthread_mutex_unlock(&mutex_game);

        pthread_mutex_lock(&mutex_board);
        for (int j=0;j<COLS;j++)
            for (int i=ROWS-1;i>0;i--)
                if (board[i][j] == IDX_EMPTY)
                    for (int k=i-1;k>=0;k--)
                        if (board[k][j] != IDX_EMPTY) {
                            board[i][j] = board[k][j];
                            board[k][j] = IDX_EMPTY;
                            break;
                        }
        pthread_mutex_unlock(&mutex_board);

        pthread_mutex_lock(&mutex_game);
        g_need_refill = true;
        pthread_mutex_unlock(&mutex_game);

        sem_post(&sem_render);
        usleep(100000);
    }
    return NULL;
}

// ============================================================
//  HILO 6: RELLENO
// ============================================================
static void* thread_refill_fn(void*) {
    while (true) {
        pthread_mutex_lock(&mutex_game);
        bool alive = g_running;
        bool need  = g_need_refill;
        if (need) g_need_refill = false;
        pthread_mutex_unlock(&mutex_game);

        if (!alive) break;

        if (need) {
            pthread_mutex_lock(&mutex_board);
            for (int i=0;i<ROWS;i++)
                for (int j=0;j<COLS;j++)
                    if (board[i][j] == IDX_EMPTY)
                        board[i][j] = rand_candy();
            pthread_mutex_unlock(&mutex_board);
            sem_post(&sem_render);
        }
        usleep(120000);
    }
    return NULL;
}

// ============================================================
//  HILO 4: RENDER
// ============================================================
static void repeat_text(const char* text, int count) {
    for (int i=0;i<count;i++) printf("%s", text);
}

static int terminal_cols() {
    struct winsize ws;
    if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == 0 && ws.ws_col > 0)
        return ws.ws_col;
    return 80;
}

static int frame_inner_width() {
    int width = terminal_cols() - 4;
    return (width < 86) ? 86 : width;
}

static void draw_rule(const char* left, const char* right, int width) {
    printf("%s%s", C_CYN, left);
    repeat_text("═", width);
    printf("%s%s\n", right, RST);
}

static void frame_begin() {
    printf("%s║%s", C_CYN, C_WHT);
}

static void frame_end(int used, int width) {
    if (used < width) repeat_text(" ", width - used);
    printf("%s║%s\n", C_CYN, RST);
}

static void frame_center(const char* text, int width) {
    int len = (int)strlen(text);
    int left = (width - len) / 2;
    int right = width - len - left;
    if (left < 0) left = 0;
    if (right < 0) right = 0;

    printf("%s║%s", C_CYN, BOLD);
    repeat_text(" ", left);
    printf("%s", text);
    repeat_text(" ", right);
    printf("%s║%s\n", C_CYN, RST);
}

static void print_centered_token(const char* text, int width) {
    int len = (int)strlen(text);
    int left = (width - len) / 2;
    int right = width - len - left;
    if (left < 0) left = 0;
    if (right < 0) right = 0;

    repeat_text(" ", left);
    printf("%s", text);
    repeat_text(" ", right);
}

static void print_candy(int idx) {
    if (idx == IDX_SPECIAL) {
        printf("%s%s⭐%s", BOLD, C_YEL, RST);
    } else if (idx == IDX_EMPTY) {
        printf("  ");
    } else if (idx >= 0 && idx < N_CANDY_HARD) {
        printf("%s", CSYM[idx]);
    } else {
        printf("  ");
    }
}

static void print_candy_cell(int idx, bool isCur, bool isSel, int cell_w) {
    const char* accent = isSel ? C_GRN : (isCur ? C_YEL : C_WHT);
    const char* left_edge = isSel ? "[" : (isCur ? "(" : " ");
    const char* right_edge = isSel ? "]" : (isCur ? ")" : " ");
    int inner = cell_w - 2;
    int candy_w = 2;
    int left_pad = (inner - candy_w) / 2;
    int right_pad = inner - candy_w - left_pad;

    printf("%s%s", accent, left_edge);
    repeat_text(" ", left_pad);
    print_candy(idx);
    printf("%s", accent);
    repeat_text(" ", right_pad);
    printf("%s%s", right_edge, C_WHT);
}

static void draw_board() {
    pthread_mutex_lock(&mutex_board);
    pthread_mutex_lock(&mutex_game);
    int  score = g_score, moves = g_moves;
    int  cr    = g_cr,    cc    = g_cc;
    int  sr    = g_sr,    sc    = g_sc;
    bool sel   = g_selected;
    pthread_mutex_unlock(&mutex_game);

    const int width = frame_inner_width();
    const int cell_w = 8;
    const int board_inner = COLS * cell_w;
    const int board_width = 4 + board_inner + 1;
    int board_pad = (width - board_width) / 2;
    if (board_pad < 2) board_pad = 2;

    char score_s[32], moves_s[32], goal_s[32];
    snprintf(score_s, sizeof(score_s), "%d", score);
    snprintf(moves_s, sizeof(moves_s), "%d", moves);
    snprintf(goal_s, sizeof(goal_s), "%d", SCORE_GOAL);

    int score_w = ((int)strlen(score_s) > 6) ? (int)strlen(score_s) : 6;
    int moves_w = ((int)strlen(moves_s) > 4) ? (int)strlen(moves_s) : 4;
    int goal_w = ((int)strlen(goal_s) > 5) ? (int)strlen(goal_s) : 5;

    string player = g_name;
    if (player.size() > 22) player = player.substr(0, 22);

    gotoxy(1,1);
    printf("\033[J");
    draw_rule("╔", "╗", width);
    frame_center("CANDY CRUSH - CC3086 UVG", width);
    draw_rule("╠", "╣", width);

    frame_begin();
    printf("  Jugador: %-22s   Modo: %-8s", player.c_str(), g_mode==1?"EASY":"HARD");
    frame_end(2 + 9 + 22 + 3 + 6 + 8, width);

    frame_begin();
    printf("  Puntaje: %s%-*s%s   Movimientos: %s%-*s%s   Meta: %s%-*s%s",
           C_YEL, score_w, score_s, C_WHT,
           C_GRN, moves_w, moves_s, C_WHT,
           C_MAG, goal_w, goal_s, C_WHT);
    frame_end(2 + 9 + score_w + 3 + 13 + moves_w + 3 + 6 + goal_w, width);

    draw_rule("╠", "╣", width);

    frame_begin();
    repeat_text(" ", board_pad + 4);
    for (int j=0;j<COLS;j++) {
        char label[8];
        snprintf(label, sizeof(label), "%d", j);
        print_centered_token(label, cell_w);
    }
    frame_end(board_pad + 4 + board_inner, width);

    frame_begin();
    repeat_text(" ", board_pad + 3);
    printf("┌");
    repeat_text("─", board_inner);
    printf("┐");
    frame_end(board_pad + 4 + board_inner + 1, width);

    for (int i=0;i<ROWS;i++) {
        frame_begin();
        repeat_text(" ", board_pad);
        printf("%2d │", i);
        for (int j=0;j<COLS;j++) {
            bool isCur = (i==cr && j==cc);
            bool isSel = (sel && i==sr && j==sc);
            print_candy_cell(board[i][j], isCur, isSel, cell_w);
        }
        printf("%s│", C_WHT);
        frame_end(board_pad + 4 + board_inner + 1, width);
    }

    frame_begin();
    repeat_text(" ", board_pad + 3);
    printf("└");
    repeat_text("─", board_inner);
    printf("┘");
    frame_end(board_pad + 4 + board_inner + 1, width);

    draw_rule("╠", "╣", width);

    frame_begin();
    printf("  Dulces: ");
    for (int k=0;k<g_ncandy;k++) printf("%s ", CSYM[k]);
    printf("   %s%s⭐%s=Especial", BOLD,C_YEL,RST);
    frame_end(10 + g_ncandy * 3 + 14, width);

    frame_begin();
    const char* help = "  [WASD] Mover   [Esp] Sel/Swap   [Q] Salir";
    printf("%s", help);
    frame_end((int)strlen(help), width);

    draw_rule("╚", "╝", width);

    pthread_mutex_unlock(&mutex_board);
    fflush(stdout);
}

static void* thread_render_fn(void*) {
    while (true) {
        struct timespec ts;
        clock_gettime(CLOCK_REALTIME, &ts);
        ts.tv_nsec += 200000000L;
        if (ts.tv_nsec >= 1000000000L) { ts.tv_sec++; ts.tv_nsec -= 1000000000L; }
        sem_timedwait(&sem_render, &ts);

        pthread_mutex_lock(&mutex_game);
        bool alive = g_running;
        pthread_mutex_unlock(&mutex_game);
        if (!alive) break;

        draw_board();
    }
    return NULL;
}

// ============================================================
//  HILO 1: INPUT
// ============================================================
static void* thread_input_fn(void*) {
    char ch;
    while (true) {
        ssize_t n = read(STDIN_FILENO, &ch, 1);

        pthread_mutex_lock(&mutex_game);
        bool alive = g_running;
        pthread_mutex_unlock(&mutex_game);
        if (!alive) break;

        if (n <= 0) continue;

        pthread_mutex_lock(&mutex_game);

        if (ch == K_QUIT) {
            g_running   = false;
            g_game_over = true;
            g_won       = false;
            pthread_cond_broadcast(&cond_match);
            pthread_cond_broadcast(&cond_grav);
            pthread_mutex_unlock(&mutex_game);
            sem_post(&sem_render);
            break;
        }

        if (ch==K_UP    && g_cr>0)      g_cr--;
        if (ch==K_DOWN  && g_cr<ROWS-1) g_cr++;
        if (ch==K_LEFT  && g_cc>0)      g_cc--;
        if (ch==K_RIGHT && g_cc<COLS-1) g_cc++;

        if (ch == K_SEL) {
            if (!g_selected) {
                g_selected = true;
                g_sr = g_cr; g_sc = g_cc;
            } else {
                int dr = abs(g_cr-g_sr), dc = abs(g_cc-g_sc);
                if ((dr==1&&dc==0)||(dr==0&&dc==1)) {
                    pthread_mutex_lock(&mutex_board);
                    int tmp = board[g_sr][g_sc];
                    board[g_sr][g_sc] = board[g_cr][g_cc];
                    board[g_cr][g_cc] = tmp;
                    pthread_mutex_unlock(&mutex_board);
                    g_moves--;
                    if (g_moves <= 0 && !g_game_over) {
                        g_game_over = true;
                        g_won       = (g_score >= SCORE_GOAL);
                        g_running   = false;
                        pthread_cond_broadcast(&cond_match);
                        pthread_cond_broadcast(&cond_grav);
                    }
                }
                g_selected = false;
            }
        }

        pthread_mutex_unlock(&mutex_game);
        sem_post(&sem_render);
    }
    return NULL;
}

// ============================================================
//  PANTALLAS
// ============================================================
static void screen_menu() {
    clrscr();
    printf("%s%s", BOLD, C_YEL);
    printf("    ██████╗ █████╗ ███╗  ██╗██████╗ ██╗   ██╗\n");
    printf("   ██╔════╝██╔══██╗████╗ ██║██╔══██╗╚██╗ ██╔╝\n");
    printf("   ██║     ███████║██╔██╗██║██║  ██║ ╚████╔╝ \n");
    printf("   ╚██████╗██║  ██║██║╚████║██████╔╝   ██║   \n");
    printf("    ╚═════╝╚═╝  ╚═╝╚═╝ ╚═══╝╚═════╝    ╚═╝   \n");
    printf("%s%s  ██████╗██████╗ ██╗   ██╗███████╗██╗  ██╗%s\n",BOLD,C_RED,RST);
    printf("%s%s ██╔════╝██╔══██╗██║   ██║██╔════╝██║  ██║%s\n",BOLD,C_RED,RST);
    printf("%s%s ██║     ██████╔╝██║   ██║███████╗███████║%s\n",BOLD,C_RED,RST);
    printf("%s%s ██║     ██║  ██║██║   ██║      █║██║  ██║%s\n",BOLD,C_RED,RST);
    printf("%s%s ╚██████╗██║  ██║╚██████╔╝███████║██║  ██║%s\n",BOLD,C_RED,RST);
    printf("%s%s  ╚═════╝╚═╝  ╚═╝ ╚═════╝╚══════╝╚═╝  ╚═╝%s\n\n",BOLD,C_RED,RST);
    printf("%s╔══════════════════════════════╗%s\n",C_CYN,RST);
    printf("%s║%s      MENÚ PRINCIPAL          %s║%s\n",C_CYN,BOLD,C_CYN,RST);
    printf("%s╠══════════════════════════════╣%s\n",C_CYN,RST);
    printf("%s║%s  1. Iniciar Partida          %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s  2. Instrucciones            %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s  3. Puntajes Destacados      %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s  4. Salir                    %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s╚══════════════════════════════╝%s\n",C_CYN,RST);
    printf("\n  %sOpción:%s ", C_YEL,RST);
    fflush(stdout);
}

static void screen_instructions() {
    clrscr();
    printf("%s%s╔══════════════════════════════════════════════╗%s\n",BOLD,C_CYN,RST);
    printf("%s%s║                INSTRUCCIONES                 ║%s\n",BOLD,C_CYN,RST);
    printf("%s%s╠══════════════════════════════════════════════╣%s\n",BOLD,C_CYN,RST);
    printf("%s║%s  OBJETIVO: alcanzar %s%d pts%s antes de agotar   %s║%s\n",C_CYN,C_WHT,C_YEL,SCORE_GOAL,C_WHT,C_CYN,RST);
    printf("%s║%s  los movimientos disponibles.                 %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s                                               %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s  CONTROLES:                                   %s║%s\n",C_CYN,BOLD,C_CYN,RST);
    printf("%s║%s   W/A/S/D   → mover cursor                   %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s   [Espacio] → seleccionar / confirmar swap   %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s   Q         → salir al menú                  %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s                                               %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s  PUNTAJE:                                     %s║%s\n",C_CYN,BOLD,C_CYN,RST);
    printf("%s║%s   3 en línea → 30 pts                        %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s   4+ en línea → 40+ pts + dulce %s⭐%s especial %s║%s\n",C_CYN,C_WHT,C_YEL,C_WHT,C_CYN,RST);
    printf("%s║%s   Especial %s⭐%s → elimina fila entera +40 pts  %s║%s\n",C_CYN,C_WHT,C_YEL,C_WHT,C_CYN,RST);
    printf("%s╚══════════════════════════════════════════════╝%s\n",C_CYN,RST);
    printf("\n  Presiona %sENTER%s para volver...\n",C_YEL,RST);
    fflush(stdout);
}

static void screen_scores() {
    clrscr();
    printf("%s%s╔══════════════════════════════╗%s\n",BOLD,C_CYN,RST);
    printf("%s%s║     PUNTAJES DESTACADOS      ║%s\n",BOLD,C_CYN,RST);
    printf("%s%s╠══════════════════════════════╣%s\n",BOLD,C_CYN,RST);
    ifstream f(SCOREFILE);
    if (!f.is_open()) {
        printf("%s║%s  (sin registros aún)         %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    } else {
        string line; int rank=1;
        while (getline(f,line) && rank<=10) {
            string d = line;
            while ((int)d.size()<24) d+=' ';
            printf("%s║%s  %2d. %s %s║%s\n",C_CYN,C_WHT,rank,d.substr(0,24).c_str(),C_CYN,RST);
            rank++;
        }
    }
    printf("%s╚══════════════════════════════╝%s\n",C_CYN,RST);
    printf("\n  Presiona %sENTER%s para volver...\n",C_YEL,RST);
    fflush(stdout);
}

static void save_score() {
    ofstream f(SCOREFILE, ios::app);
    if (f.is_open()) f << g_name << " - " << g_score << " pts\n";
}

static void screen_end() {
    showcur();
    term_restore();
    clrscr();

    if (g_won) {
        printf("\n\n");
        printf("%s%s", BOLD, C_YEL);
        printf("  ╔════════════════════════════════════════════════════════════════════╗\n");
        printf("  ║                                                                    ║\n");
        printf("  ║     ██╗   ██╗██╗ ██████╗████████╗ ██████╗ ██████╗ ██╗   ██╗        ║\n");
        printf("  ║     ██║   ██║██║██╔════╝╚══██╔══╝██╔═══██╗██╔══██╗╚██╗ ██╔╝        ║\n");
        printf("  ║     ██║   ██║██║██║        ██║   ██║   ██║██████╔╝ ╚████╔╝         ║\n");
        printf("  ║     ╚██╗ ██╔╝██║██║        ██║   ██║   ██║██╔══██╗  ╚██╔╝          ║\n");
        printf("  ║      ╚████╔╝ ██║╚██████╗   ██║   ╚██████╔╝██║  ██║   ██║           ║\n");
        printf("  ║       ╚═══╝  ╚═╝ ╚═════╝   ╚═╝    ╚═════╝ ╚═╝  ╚═╝   ╚═╝           ║\n");
        printf("  ║                                                                    ║\n");
        printf("  ╠════════════════════════════════════════════════════════════════════╣\n");
        printf("%s", RST);
        
        string vic_msg = "¡ " + string(g_name) + " HA LOGRADO LA VICTORIA !";
        printf("  ║ %s%s%-66s%s ║\n", BOLD, C_GRN, vic_msg.c_str(), RST);
        
        printf("%s%s", BOLD, C_YEL);
        printf("  ║                                                                    ║\n");
        printf("  ╚════════════════════════════════════════════════════════════════════╝\n");
        printf("%s\n", RST);

        int bar = (g_score * 40) / SCORE_GOAL;
        if (bar > 40) bar = 40;
        printf("  %sPuntaje Total: [%s", C_WHT, C_GRN);
        for (int i=0;i<bar;i++)  printf("█");
        for (int i=bar;i<40;i++) printf("░");
        printf("%s]  %s%d / %d pts%s\n\n", C_WHT, C_YEL, g_score, SCORE_GOAL, RST);
        printf("  %s★ ¡Récord inmortalizado en el tablero de puntuaciones! ★%s\n\n", C_GRN, RST);

    } else {
        printf("\n\n");
        printf("%s%s", BOLD, C_RED);
        printf("  ╔═════════════════════════════════════════════════════════════════════════════════════╗\n");
        printf("  ║                                                                                     ║\n");
        printf("  ║        ██████╗  █████╗ ███╗   ███╗███████╗  ██████╗ ██╗   ██╗███████╗██████╗        ║\n");
        printf("  ║       ██╔════╝ ██╔══██╗████╗ ████║██╔════╝ ██╔═══██╗██║   ██║██╔════╝██╔══██╗       ║\n");
        printf("  ║       ██║  ███╗███████║██╔████╔██║█████╗   ██║   ██║██║   ██║█████╗  ██████╔╝       ║\n");
        printf("  ║       ██║   ██║██╔══██║██║╚██╔╝██║██╔══╝   ██║   ██║╚██╗ ██╔╝██╔══╝  ██╔══██╗       ║\n");
        printf("  ║       ╚██████╔╝██║  ██║██║ ╚═╝ ██║███████╗ ╚██████╔╝ ╚████╔╝ ███████╗██║  ██║       ║\n");
        printf("  ║        ╚═════╝ ╚═╝  ╚═╝╚═╝     ╚═╝╚══════╝  ╚═════╝   ╚═══╝  ╚══════╝╚═╝  ╚═╝       ║\n");
        printf("  ║                                                                                     ║\n");
        printf("  ╚═════════════════════════════════════════════════════════════════════════════════════╝\n");
        printf("%s\n", RST);

        int bar = (g_score * 40) / SCORE_GOAL;
        if (bar > 40) bar = 40;
        printf("  %sPuntaje Total: [%s", C_WHT, C_RED);
        for (int i=0;i<bar;i++)  printf("█");
        for (int i=bar;i<40;i++) printf("░");
        printf("%s]  %s%d / %d pts%s\n\n", C_WHT, C_YEL, g_score, SCORE_GOAL, RST);

        int faltaron = SCORE_GOAL - g_score;
        if (faltaron > 0)
            printf("  %s¡Te quedaste a tan solo %d puntos de la gloria!%s\n\n", C_MAG, faltaron, RST);
    }

    printf("  %sEstadísticas finales de la sesión:%s\n", BOLD, RST);
    printf("  %s• Jugador:%s %-19s  %s• Modo de Juego:%s %s\n",
           C_CYN, RST, g_name, C_CYN, RST, g_mode==1?"Fácil (5 Dulces)":"Difícil (7 Dulces)");

    save_score();
    printf("\n  %s► Presiona ENTER para regresar al menú principal...%s\n", C_GRN, RST);
    fflush(stdout);

    tcflush(STDIN_FILENO, TCIFLUSH);
    char buf[8];
    fgets(buf, sizeof(buf), stdin);
}

// ============================================================
//  JUEGO
// ============================================================
static void play_game() {
    g_score=0; g_pending_pts=0;
    g_running=true; g_game_over=false; g_won=false;
    g_match_ready=false; g_need_gravity=false; g_need_refill=false;
    g_cr=0; g_cc=0; g_sr=-1; g_sc=-1; g_selected=false;

    term_restore();
    clrscr();

    printf("\n\n");
    printf("  %s%s╔══════════════════════════════════════════════╗%s\n", BOLD, C_CYN, RST);
    printf("  %s%s║%s        🍬  NUEVA PARTIDA  🍬                 %s%s║%s\n", BOLD, C_CYN, RST, BOLD, C_CYN, RST);
    printf("  %s%s╠══════════════════════════════════════════════╣%s\n", BOLD, C_CYN, RST);
    printf("  %s%s║%s                                              %s%s║%s\n", BOLD, C_CYN, RST, BOLD, C_CYN, RST);
    printf("  %s%s║%s  %s¿Cómo te llamas?%s                          %s%s║%s\n", BOLD, C_CYN, RST, C_YEL, RST, BOLD, C_CYN, RST);
    printf("  %s%s║%s  %s> %s", BOLD, C_CYN, RST, C_GRN, RST);
    fflush(stdout);

    fgets(g_name, sizeof(g_name), stdin);
    int nl = strlen(g_name);
    if (nl>0 && g_name[nl-1]=='\n') g_name[nl-1]='\0';
    if (nl==0 || (nl==1 && g_name[0]=='\0')) snprintf(g_name, sizeof(g_name), "Jugador");

    printf("  %s%s║%s                                              %s%s║%s\n", BOLD, C_CYN, RST, BOLD, C_CYN, RST);
    printf("  %s%s╠══════════════════════════════════════════════╣%s\n", BOLD, C_CYN, RST);
    printf("  %s%s║%s                                              %s%s║%s\n", BOLD, C_CYN, RST, BOLD, C_CYN, RST);
    printf("  %s%s║%s  %s¿Qué dificultad?%s                          %s%s║%s\n", BOLD, C_CYN, RST, C_YEL, RST, BOLD, C_CYN, RST);
    printf("  %s%s║%s                                              %s%s║%s\n", BOLD, C_CYN, RST, BOLD, C_CYN, RST);
    printf("  %s%s║%s  %s%s[ 1 ]  🟢 FÁCIL%s                          %s%s║%s\n", BOLD, C_CYN, RST, BOLD, C_GRN, RST, BOLD, C_CYN, RST);
    printf("  %s%s║%s        %s%d movimientos · 5 dulces%s              %s%s║%s\n", BOLD, C_CYN, RST, C_WHT, EASY_MOVES, RST, BOLD, C_CYN, RST);
    printf("  %s%s║%s                                              %s%s║%s\n", BOLD, C_CYN, RST, BOLD, C_CYN, RST);
    printf("  %s%s║%s  %s%s[ 2 ]  🔴 DIFÍCIL%s                        %s%s║%s\n", BOLD, C_CYN, RST, BOLD, C_RED, RST, BOLD, C_CYN, RST);
    printf("  %s%s║%s        %s%d movimientos · 7 dulces%s              %s%s║%s\n", BOLD, C_CYN, RST, C_WHT, HARD_MOVES, RST, BOLD, C_CYN, RST);
    printf("  %s%s║%s                                              %s%s║%s\n", BOLD, C_CYN, RST, BOLD, C_CYN, RST);
    printf("  %s%s╠══════════════════════════════════════════════╣%s\n", BOLD, C_CYN, RST);
    printf("  %s%s║%s  Jugador: %s%-12s%s                          %s%s║%s\n", BOLD, C_CYN, RST, C_YEL, g_name, RST, BOLD, C_CYN, RST);
    printf("  %s%s╚══════════════════════════════════════════════╝%s\n", BOLD, C_CYN, RST);
    printf("\n  %sOpción [1/2]:%s ", C_YEL, RST);
    fflush(stdout);

    char buf[8]; fgets(buf, sizeof(buf), stdin);
    g_mode   = (buf[0]=='2') ? 2 : 1;
    g_moves  = (g_mode==1) ? EASY_MOVES : HARD_MOVES;
    g_ncandy = (g_mode==1) ? N_CANDY_EASY : N_CANDY_HARD;

    clrscr();
    printf("\n\n");
    printf("  %s%s╔══════════════════════════════════════════════╗%s\n", BOLD, C_CYN, RST);
    printf("  %s%s║%s  🎮  ¡Listo, %s%-10s%s! Modo: %s%-8s%s        %s%s║%s\n",
           BOLD, C_CYN, RST,
           C_YEL, g_name, RST,
           g_mode==1 ? C_GRN : C_RED,
           g_mode==1 ? "FÁCIL" : "DIFÍCIL", RST,
           BOLD, C_CYN, RST);
    printf("  %s%s║%s  %s%d movimientos · Meta: %d pts%s                %s%s║%s\n",
           BOLD, C_CYN, RST, C_WHT, g_moves, SCORE_GOAL, RST, BOLD, C_CYN, RST);
    printf("  %s%s║%s  %sCargando tablero...%s                          %s%s║%s\n",
           BOLD, C_CYN, RST, C_MAG, RST, BOLD, C_CYN, RST);
    printf("  %s%s╚══════════════════════════════════════════════╝%s\n\n", BOLD, C_CYN, RST);
    fflush(stdout);
    usleep(800000);

    srand((unsigned)time(NULL));
    init_board();

    term_raw();
    hidecur();
    clrscr();

    sem_init(&sem_render, 0, 1);

    pthread_t t_render, t_input, t_match, t_score, t_grav, t_refill;
    pthread_create(&t_render, NULL, thread_render_fn,  NULL);
    pthread_create(&t_input,  NULL, thread_input_fn,   NULL);
    pthread_create(&t_match,  NULL, thread_match_fn,   NULL);
    pthread_create(&t_score,  NULL, thread_score_fn,   NULL);
    pthread_create(&t_grav,   NULL, thread_gravity_fn, NULL);
    pthread_create(&t_refill, NULL, thread_refill_fn,  NULL);

    pthread_join(t_input, NULL);

    pthread_mutex_lock(&mutex_game);
    g_running = false;
    pthread_cond_broadcast(&cond_match);
    pthread_cond_broadcast(&cond_grav);
    pthread_mutex_unlock(&mutex_game);
    
    for (int i=0; i<4; i++) sem_post(&sem_render);

    pthread_join(t_match,  NULL);
    pthread_join(t_score,  NULL);
    pthread_join(t_grav,   NULL);
    pthread_join(t_refill, NULL);
    pthread_join(t_render, NULL);

    sem_destroy(&sem_render);

    screen_end();
}

// ============================================================
//  MAIN
// ============================================================
int main() {
    tcgetattr(STDIN_FILENO, &orig_term);
    int opt=0;
    do {
        screen_menu();
        tcsetattr(STDIN_FILENO, TCSAFLUSH, &orig_term);
        char buf[8];
        if (!fgets(buf, sizeof(buf), stdin)) break;
        opt = buf[0] - '0';

        if (opt == 1) play_game();
        if (opt == 2) { screen_instructions(); fgets(buf, sizeof(buf), stdin); }
        if (opt == 3) { screen_scores();       fgets(buf, sizeof(buf), stdin); }

    } while (opt != 4);

    clrscr();
    return 0;
}
