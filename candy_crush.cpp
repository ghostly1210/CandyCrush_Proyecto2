/*
 * ============================================================
 *  CANDY CRUSH - CC3086 Programación de Microprocesadores
 *  Proyecto 2 - Fases 2 y 3
 *  Universidad del Valle de Guatemala
 *
 *  HILOS INDEPENDIENTES:
 *    1. thread_input    – Captura teclas del jugador
 *    2. thread_match    – Detecta combinaciones en el tablero
 *    3. thread_score    – Acumula el puntaje
 *    4. thread_render   – Redibuja el tablero en consola
 *    5. thread_gravity  – Hace caer dulces al haber huecos
 *    6. thread_refill   – Rellena con nuevos dulces
 *
 *  SINCRONIZACIÓN:
 *    - mutex_board  : protege el tablero
 *    - mutex_game   : protege todo el estado (score, moves, flags)
 *    - cond_match   : señala nuevas combinaciones al hilo score
 *    - cond_gravity : señala huecos al hilo gravedad
 *    - sem_render   : despierta el hilo de render
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
#define N_CANDY_EASY 5
#define N_CANDY_HARD 7
static const char  CSYM[]  = { '@','#','$','%','&','!','*' };
static const char* CCOL[]  = { C_BLU,C_GRN,C_YEL,C_RED,C_MAG,C_CYN,C_WHT };
#define SPC_CANDY 'X'   // dulce especial
#define EMPTY     ' '

// ── Teclas ───────────────────────────────────────────────────
#define K_UP    'w'
#define K_DOWN  's'
#define K_LEFT  'a'
#define K_RIGHT 'd'
#define K_SEL   ' '
#define K_QUIT  'q'

// ============================================================
//  ESTADO GLOBAL  (un solo mutex lo protege todo excepto board)
// ============================================================
static char board[ROWS][COLS];
static bool marked[ROWS][COLS];

static int  g_score        = 0;
static int  g_moves        = 0;
static int  g_pending_pts  = 0;   // puntos generados por match, aún no sumados
static bool g_running      = true;
static bool g_game_over    = false;
static bool g_won          = false;
static bool g_match_ready  = false;  // señal: hay pts pendientes para score
static bool g_need_gravity = false;  // señal: hay huecos
static bool g_need_refill  = false;  // señal: hay que rellenar

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
    t.c_cc[VTIME] = 1;   // read timeout 0.1 s → nunca bloquea para siempre
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
static char rand_candy() { return CSYM[rand() % g_ncandy]; }

static void init_board() {
    for (int i = 0; i < ROWS; i++)
        for (int j = 0; j < COLS; j++) {
            char c;
            int  tries = 0;
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
//  Espera cond_match, suma g_pending_pts, verifica victoria.
// ============================================================
static void* thread_score_fn(void*) {
    while (true) {
        pthread_mutex_lock(&mutex_game);
        // Esperar hasta que haya puntos pendientes O el juego termine
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
            // ── Comprobar victoria ──────────────────────────
            if (!g_game_over && g_score >= SCORE_GOAL) {
                g_won      = true;
                g_game_over= true;
                g_running  = false;
                // Despertar hilos bloqueados en cond_*
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
                char c = board[i][j];
                if (c == EMPTY) { j++; continue; }
                int len = 1;
                while (j+len < COLS && board[i][j+len] == c) len++;
                if (len >= 3) {
                    for (int k=0;k<len;k++) marked[i][j+k]=true;
                    pts += len*10; found = true;
                    if (len >= 4) board[i][j+len/2] = SPC_CANDY;
                }
                j += len;
            }

        // Vertical
        for (int j = 0; j < COLS; j++)
            for (int i = 0; i < ROWS-2; ) {
                char c = board[i][j];
                if (c == EMPTY) { i++; continue; }
                int len = 1;
                while (i+len < ROWS && board[i+len][j] == c) len++;
                if (len >= 3) {
                    for (int k=0;k<len;k++) marked[i+k][j]=true;
                    pts += len*10; found = true;
                    if (len >= 4) board[i+len/2][j] = SPC_CANDY;
                }
                i += len;
            }

        // Eliminar marcadas
        if (found) {
            for (int i=0;i<ROWS;i++)
                for (int j=0;j<COLS;j++)
                    if (marked[i][j]) board[i][j] = EMPTY;

            // Activar dulces especiales (eliminan su fila entera)
            for (int i=0;i<ROWS;i++)
                for (int j=0;j<COLS;j++)
                    if (board[i][j] == SPC_CANDY) {
                        for (int k=0;k<COLS;k++) board[i][k] = EMPTY;
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
                if (board[i][j] == EMPTY)
                    for (int k=i-1;k>=0;k--)
                        if (board[k][j] != EMPTY) {
                            board[i][j] = board[k][j];
                            board[k][j] = EMPTY;
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
                    if (board[i][j] == EMPTY)
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
static void print_candy(char c) {
    if (c == SPC_CANDY) { printf("%s%sX%s", BOLD, C_YEL, RST); return; }
    for (int k=0;k<7;k++)
        if (c == CSYM[k]) { printf("%s%s%c%s", BOLD, CCOL[k], c, RST); return; }
    printf(" ");
}

static void draw_board() {
    pthread_mutex_lock(&mutex_board);
    // Leer estado bajo mutex_game
    pthread_mutex_lock(&mutex_game);
    int  score = g_score, moves = g_moves;
    int  cr    = g_cr,    cc    = g_cc;
    int  sr    = g_sr,    sc    = g_sc;
    bool sel   = g_selected;
    pthread_mutex_unlock(&mutex_game);

    gotoxy(1,1);
    printf("%s╔══════════════════════════════════════════════╗%s\n", C_CYN, RST);
    printf("%s║%s  🍬  CANDY CRUSH - CC3086 UVG  🍬             %s║%s\n", C_CYN,BOLD,C_CYN,RST);
    printf("%s╠══════════════════════════════════════════════╣%s\n", C_CYN, RST);
    printf("%s║%s  Jugador: %-12s  Modo: %-5s           %s║%s\n",
           C_CYN,C_WHT, g_name, g_mode==1?"EASY":"HARD", C_CYN,RST);
    printf("%s║%s  Puntaje:%s%-5d%s  Movimientos:%s%-3d%s  Meta:%s%-4d%s %s║%s\n",
           C_CYN,C_WHT, C_YEL,score,C_WHT, C_GRN,moves,C_WHT,
           C_MAG,SCORE_GOAL,C_WHT, C_CYN,RST);
    printf("%s╠══════════════════════════════════════════════╣%s\n", C_CYN, RST);
    printf("%s║%s    ", C_CYN, C_WHT);
    for (int j=0;j<COLS;j++) printf("  %d ", j);
    printf("  %s║%s\n", C_CYN,RST);
    printf("%s║%s  ┌", C_CYN, C_WHT);
    for (int j=0;j<COLS;j++) printf("────");
    printf("┐ %s║%s\n", C_CYN,RST);

    for (int i=0;i<ROWS;i++) {
        printf("%s║%s %d│", C_CYN,C_WHT,i);
        for (int j=0;j<COLS;j++) {
            bool isCur = (i==cr && j==cc);
            bool isSel = (sel && i==sr && j==sc);
            printf("%s", isSel ? C_GRN : (isCur ? C_YEL : C_WHT));
            printf("%s", isSel ? "[" : (isCur ? "(" : " "));
            print_candy(board[i][j]);
            printf("%s", isSel ? "]" : (isCur ? ")" : " "));
        }
        printf("%s│ %s║%s\n", C_WHT, C_CYN, RST);
    }

    printf("%s║%s  └", C_CYN,C_WHT);
    for (int j=0;j<COLS;j++) printf("────");
    printf("┘ %s║%s\n", C_CYN,RST);
    printf("%s╠══════════════════════════════════════════════╣%s\n", C_CYN,RST);
    printf("%s║%s  Dulces: ", C_CYN,C_WHT);
    for (int k=0;k<g_ncandy;k++) printf("%s%c%s ", CCOL[k],CSYM[k],RST);
    printf("  %s%sX%s=Especial           %s║%s\n", BOLD,C_YEL,RST,C_CYN,RST);
    printf("%s║%s  [WASD] Mover  [Esp] Sel/Swap  [Q] Salir    %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s╚══════════════════════════════════════════════╝%s\n", C_CYN,RST);

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
        if (!alive) break;   // salir sin dibujar más

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
        // read() con VTIME=1 → timeout 0.1s, nunca bloquea indefinidamente
        ssize_t n = read(STDIN_FILENO, &ch, 1);

        // Revisar si el juego terminó (por victoria u otro hilo)
        pthread_mutex_lock(&mutex_game);
        bool alive = g_running;
        pthread_mutex_unlock(&mutex_game);
        if (!alive) break;

        if (n <= 0) continue;   // timeout, sin tecla

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

        // Mover cursor
        if (ch==K_UP    && g_cr>0)      g_cr--;
        if (ch==K_DOWN  && g_cr<ROWS-1) g_cr++;
        if (ch==K_LEFT  && g_cc>0)      g_cc--;
        if (ch==K_RIGHT && g_cc<COLS-1) g_cc++;

        // Seleccionar / intercambiar
        if (ch == K_SEL) {
            if (!g_selected) {
                g_selected = true;
                g_sr = g_cr; g_sc = g_cc;
            } else {
                int dr = abs(g_cr-g_sr), dc = abs(g_cc-g_sc);
                if ((dr==1&&dc==0)||(dr==0&&dc==1)) {
                    pthread_mutex_lock(&mutex_board);
                    char tmp = board[g_sr][g_sc];
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
    printf("   ██████╗ █████╗ ███╗  ██╗██████╗ ██╗   ██╗\n");
    printf("  ██╔════╝██╔══██╗████╗ ██║██╔══██╗╚██╗ ██╔╝\n");
    printf("  ██║     ███████║██╔██╗██║██║  ██║ ╚████╔╝ \n");
    printf("  ╚██████╗██║  ██║██║╚████║██████╔╝   ██║   \n");
    printf("   ╚═════╝╚═╝  ╚═╝╚═╝ ╚═══╝╚═════╝    ╚═╝   \n");
    printf("%s%s", C_RED, RST);
    printf("%s%s  ██████╗██████╗ ██╗   ██╗███████╗██╗  ██╗%s\n",BOLD,C_RED,RST);
    printf("%s%s ██╔════╝██╔══██╗██║   ██║██╔════╝██║  ██║%s\n",BOLD,C_RED,RST);
    printf("%s%s ██║     ██████╔╝██║   ██║███████╗███████║%s\n",BOLD,C_RED,RST);
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
    printf("%s%s║               INSTRUCCIONES                  ║%s\n",BOLD,C_CYN,RST);
    printf("%s%s╠══════════════════════════════════════════════╣%s\n",BOLD,C_CYN,RST);
    printf("%s║%s  OBJETIVO: alcanzar %s%d pts%s antes de agotar   %s║%s\n",C_CYN,C_WHT,C_YEL,SCORE_GOAL,C_WHT,C_CYN,RST);
    printf("%s║%s  los movimientos disponibles.                %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s                                              %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s  CONTROLES:                                  %s║%s\n",C_CYN,BOLD,C_CYN,RST);
    printf("%s║%s   W/A/S/D   → mover cursor                  %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s   [Espacio] → seleccionar / confirmar swap   %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s   Q         → salir al menú                  %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s                                              %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s  PUNTAJE:                                    %s║%s\n",C_CYN,BOLD,C_CYN,RST);
    printf("%s║%s   3 en línea → 30 pts                       %s║%s\n",C_CYN,C_WHT,C_CYN,RST);
    printf("%s║%s   4+ en línea → 40+ pts + dulce %sX%s especial %s║%s\n",C_CYN,C_WHT,C_YEL,C_WHT,C_CYN,RST);
    printf("%s║%s   Especial %sX%s → elimina fila entera +40 pts  %s║%s\n",C_CYN,C_WHT,C_YEL,C_WHT,C_CYN,RST);
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
            while ((int)d.size()<28) d+=' ';
            printf("%s║%s  %2d. %s%s║%s\n",C_CYN,C_WHT,rank,d.substr(0,28).c_str(),C_CYN,RST);
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
    // Llamada DESPUES de que todos los hilos terminaron.
    showcur();
    term_restore();
    clrscr();

    if (g_won) {
        printf("\n");
        printf("%s%s", BOLD, C_YEL);
        printf("  ╔══════════════════════════════════════════════════╗\n");
        printf("  ║                                                  ║\n");
        printf("  ║    ██╗   ██╗██╗ ██████╗████████╗ ██████╗ ██╗     ║\n");
        printf("  ║    ██║   ██║██║██╔════╝╚══██╔══╝██╔═══██╗██║     ║\n");
        printf("  ║    ██║   ██║██║██║        ██║   ██║   ██║██║     ║\n");
        printf("  ║    ╚██╗ ██╔╝██║██║        ██║   ██║   ██║██║     ║\n");
        printf("  ║     ╚████╔╝ ██║╚██████╗   ██║   ╚██████╔╝██║     ║\n");
        printf("  ║      ╚═══╝  ╚═╝ ╚═════╝   ╚═╝    ╚═════╝ ╚═╝     ║\n");
        printf("  ║                                                  ║\n");
        printf("%s", RST);
        // Nombre del jugador centrado
        char linebuf[96];
        snprintf(linebuf, sizeof(linebuf), "  Felicitaciones, %s!", g_name);
        int pad = (50 - (int)strlen(linebuf)) / 2;
        if (pad < 0) pad = 0;
        printf("%s%s  ║%*s%s%*s║%s\n", BOLD, C_GRN, pad,"", linebuf, 50-pad-(int)strlen(linebuf),"", RST);
        printf("%s%s", BOLD, C_YEL);
        printf("  ║                                                  ║\n");
        printf("  ╚══════════════════════════════════════════════════╝\n");
        printf("%s\n", RST);

        // Barra de progreso
        int bar = (g_score * 30) / SCORE_GOAL;
        if (bar > 30) bar = 30;
        printf("  %sPuntaje: [%s", C_WHT, C_GRN);
        for (int i=0;i<bar;i++)  printf("█");
        for (int i=bar;i<30;i++) printf("░");
        printf("%s]  %s%d / %d pts%s\n\n", C_WHT, C_YEL, g_score, SCORE_GOAL, RST);
        printf("  %s★ Puntaje guardado en el scoreboard ★%s\n\n", C_GRN, RST);

    } else {
        printf("\n");
        printf("%s%s", BOLD, C_RED);
        printf("  ╔══════════════════════════════════════════════════╗\n");
        printf("  ║                                                  ║\n");
        printf("  ║   ██████╗  █████╗ ███╗   ███╗███████╗           ║\n");
        printf("  ║  ██╔════╝ ██╔══██╗████╗ ████║██╔════╝           ║\n");
        printf("  ║  ██║  ███╗███████║██╔████╔██║█████╗             ║\n");
        printf("  ║  ██║   ██║██╔══██║██║╚██╔╝██║██╔══╝             ║\n");
        printf("  ║  ╚██████╔╝██║  ██║██║ ╚═╝ ██║███████╗           ║\n");
        printf("  ║   ╚═════╝ ╚═╝  ╚═╝╚═╝     ╚═╝╚══════╝           ║\n");
        printf("  ║                                                  ║\n");
        printf("  ║   ██████╗ ██╗   ██╗███████╗██████╗              ║\n");
        printf("  ║  ██╔═══██╗██║   ██║██╔════╝██╔══██╗             ║\n");
        printf("  ║  ██║   ██║██║   ██║█████╗  ██████╔╝             ║\n");
        printf("  ║  ██║   ██║╚██╗ ██╔╝██╔══╝  ██╔══██╗             ║\n");
        printf("  ║  ╚██████╔╝ ╚████╔╝ ███████╗██║  ██║             ║\n");
        printf("  ║   ╚═════╝   ╚═══╝  ╚══════╝╚═╝  ╚═╝             ║\n");
        printf("  ║                                                  ║\n");
        printf("  ╚══════════════════════════════════════════════════╝\n");
        printf("%s\n", RST);

        int bar = (g_score * 30) / SCORE_GOAL;
        if (bar > 30) bar = 30;
        printf("  %sPuntaje: [%s", C_WHT, C_RED);
        for (int i=0;i<bar;i++)  printf("█");
        for (int i=bar;i<30;i++) printf("░");
        printf("%s]  %s%d / %d pts%s\n\n", C_WHT, C_YEL, g_score, SCORE_GOAL, RST);

        int faltaron = SCORE_GOAL - g_score;
        if (faltaron > 0)
            printf("  %s¡Te faltaron %d pts para ganar!%s\n\n", C_MAG, faltaron, RST);
    }

    printf("  %sJugador:%s %-20s  %sModo:%s %s\n",
           C_CYN, RST, g_name, C_CYN, RST, g_mode==1?"Facil":"Dificil");

    save_score();
    printf("\n  %s► Presiona ENTER para continuar...%s\n", C_GRN, RST);
    fflush(stdout);

    // Vaciar teclas residuales del juego antes de leer ENTER
    tcflush(STDIN_FILENO, TCIFLUSH);
    char buf[8];
    fgets(buf, sizeof(buf), stdin);
}

// ============================================================
//  JUEGO
// ============================================================
static void play_game() {
    // Reset estado
    g_score=0; g_pending_pts=0;
    g_running=true; g_game_over=false; g_won=false;
    g_match_ready=false; g_need_gravity=false; g_need_refill=false;
    g_cr=0; g_cc=0; g_sr=-1; g_sc=-1; g_selected=false;

    // Pedir nombre y modo en modo cooked
    term_restore();
    clrscr();
    printf("%s  Ingresa tu nombre:%s ", C_YEL,RST); fflush(stdout);
    fgets(g_name, sizeof(g_name), stdin);
    int nl = strlen(g_name);
    if (nl>0 && g_name[nl-1]=='\n') g_name[nl-1]='\0';

    printf("\n%s  Modo:%s 1=Fácil (%d mov, 5 dulces)  2=Difícil (%d mov, 7 dulces)\n  Opción: ",
           C_YEL,RST, EASY_MOVES, HARD_MOVES);
    fflush(stdout);
    char buf[8]; fgets(buf, sizeof(buf), stdin);
    g_mode   = (buf[0]=='2') ? 2 : 1;
    g_moves  = (g_mode==1) ? EASY_MOVES : HARD_MOVES;
    g_ncandy = (g_mode==1) ? N_CANDY_EASY : N_CANDY_HARD;

    srand((unsigned)time(NULL));
    init_board();

    // Modo raw + pantalla limpia
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

    // Esperar hilo input (termina cuando g_running=false)
    pthread_join(t_input, NULL);

    // Garantizar que todos los hilos vean g_running=false y salgan
    pthread_mutex_lock(&mutex_game);
    g_running = false;
    pthread_cond_broadcast(&cond_match);
    pthread_cond_broadcast(&cond_grav);
    pthread_mutex_unlock(&mutex_game);
    // Despertar render y los hilos con sem
    for (int i=0;i<4;i++) sem_post(&sem_render);

    pthread_join(t_match,  NULL);
    pthread_join(t_score,  NULL);
    pthread_join(t_grav,   NULL);
    pthread_join(t_refill, NULL);
    pthread_join(t_render, NULL);

    sem_destroy(&sem_render);

    // Todos los hilos terminaron → ahora es seguro mostrar pantalla final
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
        // Modo cooked para el menú
        tcsetattr(STDIN_FILENO, TCSAFLUSH, &orig_term);
        char buf[8]; fgets(buf, sizeof(buf), stdin);
        opt = buf[0]-'0';
        switch(opt) {
        case 1: play_game(); break;
        case 2:
            screen_instructions();
            tcsetattr(STDIN_FILENO, TCSAFLUSH, &orig_term);
            { char d[4]; fgets(d,sizeof(d),stdin); }
            break;
        case 3:
            screen_scores();
            tcsetattr(STDIN_FILENO, TCSAFLUSH, &orig_term);
            { char d[4]; fgets(d,sizeof(d),stdin); }
            break;
        case 4:
            clrscr();
            printf("%s  ¡Hasta pronto! 🍬%s\n\n",C_YEL,RST);
            break;
        }
    } while(opt!=4);

    pthread_mutex_destroy(&mutex_board);
    pthread_mutex_destroy(&mutex_game);
    pthread_cond_destroy(&cond_match);
    pthread_cond_destroy(&cond_grav);
    return 0;
}