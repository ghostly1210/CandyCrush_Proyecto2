/*
 * ============================================================
 *  CANDY CRUSH - CC3086 Programación de Microprocesadores
 *  Proyecto 2 - Fases 2 y 3
 *  Universidad del Valle de Guatemala
 *
 *  Implementación con:
 *    - POSIX Threads (pthreads)
 *    - Mutex para acceso al tablero compartido
 *    - Variables de condición para sincronización
 *    - Semáforos para control de turnos
 *    - ASCII-Art para visualización en consola
 * ============================================================
 *
 *  HILOS INDEPENDIENTES:
 *    1. thread_input       – Captura teclas del jugador
 *    2. thread_match       – Detecta combinaciones en el tablero
 *    3. thread_score       – Calcula y acumula el puntaje
 *    4. thread_render      – Redibuja el tablero en consola
 *    5. thread_gravity     – Hace caer dulces al haber huecos
 *    6. thread_refill      – Rellena la fila superior con nuevos dulces
 *
 *  MECANISMOS DE SINCRONIZACIÓN:
 *    - mutex_board         – Protege el tablero compartido
 *    - mutex_score         – Protege la variable de puntaje
 *    - mutex_state         – Protege el estado global del juego
 *    - cond_match_ready    – Señala que hay combinaciones listas
 *    - cond_gravity_ready  – Señala que hay huecos para aplicar gravedad
 *    - sem_render          – Controla frecuencia de renderizado
 * ============================================================
 */

#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <vector>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <unistd.h>
#include <termios.h>
#include <pthread.h>
#include <semaphore.h>

using namespace std;

// ============================================================
//  CONSTANTES
// ============================================================
#define BOARD_ROWS   8
#define BOARD_COLS   8
#define NUM_CANDIES  5       // tipos de dulces en modo fácil
#define NUM_CANDIES_H 7      // tipos en modo difícil
#define EASY_MOVES  20
#define HARD_MOVES  12
#define SCORE_GOAL  100
#define SCOREBOARD  "scoreboard.txt"

// Colores ANSI
#define RESET   "\033[0m"
#define BOLD    "\033[1m"
#define RED     "\033[31m"
#define GREEN   "\033[32m"
#define YELLOW  "\033[33m"
#define BLUE    "\033[34m"
#define MAGENTA "\033[35m"
#define CYAN    "\033[36m"
#define WHITE   "\033[37m"
#define BG_BLACK "\033[40m"

// Dulces representados con caracteres ASCII
// Índice: 0=@(azul) 1=#(verde) 2=$(amarillo) 3=%(rojo) 4=&(magenta) 5=!(cyan) 6=*(blanco)
const char  CANDY_CHAR[]  = { '@', '#', '$', '%', '&', '!', '*' };
const char* CANDY_COLOR[] = { BLUE, GREEN, YELLOW, RED, MAGENTA, CYAN, WHITE };

// Dulce especial (generado con combo >=4)
#define SPECIAL_CANDY 8
#define SPECIAL_CHAR  'X'

// Teclas
#define KEY_UP    'w'
#define KEY_DOWN  's'
#define KEY_LEFT  'a'
#define KEY_RIGHT 'd'
#define KEY_SELECT ' '   // Espacio selecciona/confirma
#define KEY_QUIT  'q'

// ============================================================
//  ESTADO GLOBAL DEL JUEGO
// ============================================================
typedef struct {
    char board[BOARD_ROWS][BOARD_COLS];   // tablero principal
    bool marked[BOARD_ROWS][BOARD_COLS];  // celdas marcadas para eliminar
    bool holes[BOARD_ROWS][BOARD_COLS];   // huecos detectados
    int  cursor_r, cursor_c;              // posición del cursor
    int  sel_r,    sel_c;                 // celda seleccionada (-1 si ninguna)
    bool selected;                        // hay celda seleccionada
    int  score;                           // puntaje actual
    int  moves;                           // movimientos restantes
    int  mode;                            // 1=fácil, 2=difícil
    int  num_candy_types;
    bool game_over;
    bool player_won;
    bool running;                         // hilo principal corriendo
    bool match_pending;                   // hay combinaciones por procesar
    bool gravity_pending;                 // hay huecos por llenar
    bool refill_pending;                  // hay que rellenar fila superior
    int  pending_score;                   // puntaje por confirmar al hilo score
    char player_name[64];
} GameState;

GameState G;

// ============================================================
//  PRIMITIVAS DE SINCRONIZACIÓN
// ============================================================
pthread_mutex_t mutex_board  = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t mutex_score  = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t mutex_state  = PTHREAD_MUTEX_INITIALIZER;
pthread_cond_t  cond_match_ready   = PTHREAD_COND_INITIALIZER;
pthread_cond_t  cond_gravity_ready = PTHREAD_COND_INITIALIZER;
sem_t           sem_render;

// ============================================================
//  UTILIDADES DE TERMINAL
// ============================================================

/* Desactiva el modo canonical (entrada carácter a carácter, sin eco) */
static struct termios orig_termios;

void term_raw_mode() {
    tcgetattr(STDIN_FILENO, &orig_termios);
    struct termios raw = orig_termios;
    raw.c_lflag &= ~(ICANON | ECHO);
    raw.c_cc[VMIN]  = 0;
    raw.c_cc[VTIME] = 1;   // timeout 0.1 s
    tcsetattr(STDIN_FILENO, TCSAFLUSH, &raw);
}

void term_restore() {
    tcsetattr(STDIN_FILENO, TCSAFLUSH, &orig_termios);
}

void clear_screen()   { printf("\033[H\033[2J"); fflush(stdout); }
void hide_cursor()    { printf("\033[?25l"); fflush(stdout); }
void show_cursor()    { printf("\033[?25h"); fflush(stdout); }
void move_cursor(int r, int c) { printf("\033[%d;%dH", r, c); fflush(stdout); }

// ============================================================
//  FUNCIONES DEL TABLERO
// ============================================================

/* Genera un tipo de dulce aleatorio (0..num_types-1), evitando triple inmediato */
char rand_candy(int num_types) {
    int c = rand() % num_types;
    return CANDY_CHAR[c];
}

/* Inicializa el tablero sin combinaciones iniciales */
void init_board(int num_types) {
    for (int i = 0; i < BOARD_ROWS; i++) {
        for (int j = 0; j < BOARD_COLS; j++) {
            char c;
            int attempts = 0;
            do {
                c = rand_candy(num_types);
                attempts++;
                // Evitar 3 en fila horizontal
                bool h = (j >= 2 &&
                          G.board[i][j-1] == c &&
                          G.board[i][j-2] == c);
                // Evitar 3 en columna
                bool v = (i >= 2 &&
                          G.board[i-1][j] == c &&
                          G.board[i-2][j] == c);
                if (!h && !v) break;
            } while (attempts < 20);
            G.board[i][j] = c;
        }
    }
}

/* Devuelve el índice del tipo de dulce según su carácter, -1 si no encontrado */
int candy_index(char c) {
    if (c == SPECIAL_CHAR) return -2;   // especial
    for (int i = 0; i < 7; i++)
        if (CANDY_CHAR[i] == c) return i;
    return -1;
}

/* Intercambia dos celdas del tablero (requiere mutex_board bloqueado) */
void swap_cells(int r1, int c1, int r2, int c2) {
    char tmp = G.board[r1][c1];
    G.board[r1][c1] = G.board[r2][c2];
    G.board[r2][c2] = tmp;
}

// ============================================================
//  HILO 3: CÁLCULO DE PUNTAJE
//  Espera señal de match_ready y suma los puntos pendientes.
// ============================================================
void* thread_score_fn(void* arg) {
    while (true) {
        // Espera que haya puntaje pendiente
        pthread_mutex_lock(&mutex_state);
        while (!G.match_pending && G.running)
            pthread_cond_wait(&cond_match_ready, &mutex_state);
        if (!G.running) {
            pthread_mutex_unlock(&mutex_state);
            break;
        }
        int pts = G.pending_score;
        G.pending_score = 0;
        pthread_mutex_unlock(&mutex_state);

        if (pts > 0) {
            pthread_mutex_lock(&mutex_score);
            G.score += pts;
            pthread_mutex_unlock(&mutex_score);
        }
        usleep(10000);
    }
    return NULL;
}

// ============================================================
//  HILO 2: DETECCIÓN DE COMBINACIONES
//  Escanea el tablero y marca las celdas a eliminar.
// ============================================================
void* thread_match_fn(void* arg) {
    while (true) {
        pthread_mutex_lock(&mutex_state);
        if (!G.running) {
            pthread_mutex_unlock(&mutex_state);
            break;
        }
        pthread_mutex_unlock(&mutex_state);

        pthread_mutex_lock(&mutex_board);

        bool found = false;
        int  pts   = 0;
        memset(G.marked, 0, sizeof(G.marked));

        // Horizontal: 3 o más
        for (int i = 0; i < BOARD_ROWS; i++) {
            for (int j = 0; j < BOARD_COLS - 2; j++) {
                char c = G.board[i][j];
                if (c == ' ') continue;
                int len = 1;
                while (j + len < BOARD_COLS && G.board[i][j+len] == c) len++;
                if (len >= 3) {
                    for (int k = 0; k < len; k++)
                        G.marked[i][j+k] = true;
                    pts  += len * 10;
                    found = true;
                    // Dulce especial si combo >=4
                    if (len >= 4)
                        G.board[i][j + len/2] = SPECIAL_CHAR;
                    j += len - 1;
                }
            }
        }

        // Vertical: 3 o más
        for (int j = 0; j < BOARD_COLS; j++) {
            for (int i = 0; i < BOARD_ROWS - 2; i++) {
                char c = G.board[i][j];
                if (c == ' ') continue;
                int len = 1;
                while (i + len < BOARD_ROWS && G.board[i+len][j] == c) len++;
                if (len >= 3) {
                    for (int k = 0; k < len; k++)
                        G.marked[i+k][j] = true;
                    pts  += len * 10;
                    found = true;
                    if (len >= 4)
                        G.board[i + len/2][j] = SPECIAL_CHAR;
                    i += len - 1;
                }
            }
        }

        // Eliminar celdas marcadas
        if (found) {
            for (int i = 0; i < BOARD_ROWS; i++)
                for (int j = 0; j < BOARD_COLS; j++)
                    if (G.marked[i][j])
                        G.board[i][j] = ' ';

            // Activar dulces especiales (eliminan fila completa)
            for (int i = 0; i < BOARD_ROWS; i++) {
                for (int j = 0; j < BOARD_COLS; j++) {
                    if (G.board[i][j] == SPECIAL_CHAR) {
                        // elimina toda la fila
                        for (int k = 0; k < BOARD_COLS; k++)
                            G.board[i][k] = ' ';
                        pts += BOARD_COLS * 5;
                    }
                }
            }

            pthread_mutex_unlock(&mutex_board);

            // Notifica al hilo de puntaje
            pthread_mutex_lock(&mutex_state);
            G.pending_score  += pts;
            G.match_pending   = true;
            G.gravity_pending = true;
            pthread_cond_signal(&cond_match_ready);
            pthread_mutex_unlock(&mutex_state);

            // Notifica al hilo de gravedad
            pthread_cond_signal(&cond_gravity_ready);

            sem_post(&sem_render);
        } else {
            pthread_mutex_unlock(&mutex_board);
        }

        usleep(150000);   // revisa cada 150 ms
    }
    return NULL;
}

// ============================================================
//  HILO 5: GRAVEDAD – hace caer los dulces
// ============================================================
void* thread_gravity_fn(void* arg) {
    while (true) {
        pthread_mutex_lock(&mutex_state);
        while (!G.gravity_pending && G.running)
            pthread_cond_wait(&cond_gravity_ready, &mutex_state);
        if (!G.running) {
            pthread_mutex_unlock(&mutex_state);
            break;
        }
        G.gravity_pending = false;
        pthread_mutex_unlock(&mutex_state);

        pthread_mutex_lock(&mutex_board);
        // Para cada columna, empuja espacios hacia arriba
        for (int j = 0; j < BOARD_COLS; j++) {
            for (int i = BOARD_ROWS - 1; i > 0; i--) {
                if (G.board[i][j] == ' ') {
                    // busca el primer dulce encima
                    for (int k = i - 1; k >= 0; k--) {
                        if (G.board[k][j] != ' ') {
                            G.board[i][j] = G.board[k][j];
                            G.board[k][j] = ' ';
                            break;
                        }
                    }
                }
            }
        }
        pthread_mutex_unlock(&mutex_board);

        // Marca relleno pendiente
        pthread_mutex_lock(&mutex_state);
        G.refill_pending = true;
        G.match_pending  = false;
        pthread_mutex_unlock(&mutex_state);

        sem_post(&sem_render);
        usleep(100000);
    }
    return NULL;
}

// ============================================================
//  HILO 6: RELLENO – genera nuevos dulces en la fila superior
// ============================================================
void* thread_refill_fn(void* arg) {
    while (true) {
        pthread_mutex_lock(&mutex_state);
        bool need = G.refill_pending && G.running;
        if (need) G.refill_pending = false;
        pthread_mutex_unlock(&mutex_state);

        if (need) {
            pthread_mutex_lock(&mutex_board);
            for (int j = 0; j < BOARD_COLS; j++) {
                for (int i = 0; i < BOARD_ROWS; i++) {
                    if (G.board[i][j] == ' ')
                        G.board[i][j] = rand_candy(G.num_candy_types);
                }
            }
            pthread_mutex_unlock(&mutex_board);
            sem_post(&sem_render);
        }
        usleep(120000);
    }
    return NULL;
}

// ============================================================
//  HILO 4: RENDERIZADO
// ============================================================

void print_candy(char c) {
    int idx = candy_index(c);
    if (c == SPECIAL_CHAR) {
        printf("%s%s%c%s", BOLD, YELLOW, SPECIAL_CHAR, RESET);
    } else if (idx >= 0) {
        printf("%s%s%c%s", BOLD, CANDY_COLOR[idx], c, RESET);
    } else {
        printf("%s %s", BG_BLACK, RESET);
    }
}

void draw_board() {
    pthread_mutex_lock(&mutex_board);
    pthread_mutex_lock(&mutex_score);

    move_cursor(1, 1);

    // Encabezado
    printf("%s╔══════════════════════════════════════════════╗%s\n", CYAN, RESET);
    printf("%s║%s   🍬  CANDY CRUSH  -  CC3086  UVG  🍬         %s║%s\n", CYAN, BOLD, CYAN, RESET);
    printf("%s╠══════════════════════════════════════════════╣%s\n", CYAN, RESET);
    printf("%s║%s  Jugador: %-12s  Modo: %-6s          %s║%s\n",
           CYAN, WHITE,
           G.player_name,
           (G.mode == 1 ? "EASY" : "HARD"),
           CYAN, RESET);
    printf("%s║%s  Puntaje: %s%-5d%s  Movimientos: %s%-3d%s  Meta: %s%-5d%s %s║%s\n",
           CYAN, WHITE,
           YELLOW, G.score, WHITE,
           GREEN,  G.moves, WHITE,
           MAGENTA, SCORE_GOAL, WHITE,
           CYAN, RESET);
    printf("%s╠══════════════════════════════════════════════╣%s\n", CYAN, RESET);

    // Índices columna
    printf("%s║%s    ", CYAN, WHITE);
    for (int j = 0; j < BOARD_COLS; j++)
        printf("  %d ", j);
    printf(" %s║%s\n", CYAN, RESET);
    printf("%s║%s  ┌", CYAN, WHITE);
    for (int j = 0; j < BOARD_COLS; j++) printf("────");
    printf("┐ %s║%s\n", CYAN, RESET);

    for (int i = 0; i < BOARD_ROWS; i++) {
        printf("%s║%s %d│", CYAN, WHITE, i);
        for (int j = 0; j < BOARD_COLS; j++) {
            // Cursor
            bool is_cursor   = (i == G.cursor_r && j == G.cursor_c);
            bool is_selected = (G.selected && i == G.sel_r && j == G.sel_c);

            if (is_selected)
                printf("%s[", GREEN);
            else if (is_cursor)
                printf("%s(", YELLOW);
            else
                printf(" ");

            print_candy(G.board[i][j]);

            if (is_selected)
                printf("%s]", GREEN);
            else if (is_cursor)
                printf("%s)", YELLOW);
            else
                printf(" ");
        }
        printf("%s│ %s║%s\n", WHITE, CYAN, RESET);
    }

    printf("%s║%s  └", CYAN, WHITE);
    for (int j = 0; j < BOARD_COLS; j++) printf("────");
    printf("┘ %s║%s\n", CYAN, RESET);

    // Leyenda de dulces
    printf("%s╠══════════════════════════════════════════════╣%s\n", CYAN, RESET);
    printf("%s║%s  Dulces: ", CYAN, WHITE);
    for (int k = 0; k < G.num_candy_types; k++) {
        printf("%s%c%s ", CANDY_COLOR[k], CANDY_CHAR[k], RESET);
    }
    printf("%s%c%s=Especial", BOLD, SPECIAL_CHAR, RESET);
    // Rellenar hasta el borde
    printf("              %s║%s\n", CYAN, RESET);

    printf("%s╠══════════════════════════════════════════════╣%s\n", CYAN, RESET);
    printf("%s║%s  [W/A/S/D] Mover  [Espacio] Sel/Swap  [Q] Salir %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s╚══════════════════════════════════════════════╝%s\n", CYAN, RESET);

    pthread_mutex_unlock(&mutex_score);
    pthread_mutex_unlock(&mutex_board);
    fflush(stdout);
}

void* thread_render_fn(void* arg) {
    while (true) {
        // Espera señal del semáforo (máx 200 ms de timeout)
        struct timespec ts;
        clock_gettime(CLOCK_REALTIME, &ts);
        ts.tv_nsec += 200000000L;
        if (ts.tv_nsec >= 1000000000L) {
            ts.tv_sec++;
            ts.tv_nsec -= 1000000000L;
        }
        sem_timedwait(&sem_render, &ts);

        pthread_mutex_lock(&mutex_state);
        bool alive = G.running;
        pthread_mutex_unlock(&mutex_state);
        if (!alive) break;

        draw_board();
    }
    return NULL;
}

// ============================================================
//  HILO 1: INPUT DEL JUGADOR
// ============================================================
void* thread_input_fn(void* arg) {
    char ch;
    while (true) {
        ssize_t n = read(STDIN_FILENO, &ch, 1);
        if (n <= 0) { usleep(20000); continue; }

        pthread_mutex_lock(&mutex_state);
        if (!G.running) {
            pthread_mutex_unlock(&mutex_state);
            break;
        }

        if (ch == KEY_QUIT) {
            G.running   = false;
            G.game_over = true;
            pthread_cond_broadcast(&cond_match_ready);
            pthread_cond_broadcast(&cond_gravity_ready);
            pthread_mutex_unlock(&mutex_state);
            sem_post(&sem_render);
            break;
        }

        // Movimiento del cursor
        int nr = G.cursor_r, nc = G.cursor_c;
        if      (ch == KEY_UP    && nr > 0)              nr--;
        else if (ch == KEY_DOWN  && nr < BOARD_ROWS - 1) nr++;
        else if (ch == KEY_LEFT  && nc > 0)              nc--;
        else if (ch == KEY_RIGHT && nc < BOARD_COLS - 1) nc++;

        G.cursor_r = nr;
        G.cursor_c = nc;

        // Selección / intercambio
        if (ch == KEY_SELECT) {
            if (!G.selected) {
                G.selected = true;
                G.sel_r    = G.cursor_r;
                G.sel_c    = G.cursor_c;
            } else {
                int dr = abs(G.cursor_r - G.sel_r);
                int dc = abs(G.cursor_c - G.sel_c);
                // Solo adyacentes
                if ((dr == 1 && dc == 0) || (dr == 0 && dc == 1)) {
                    pthread_mutex_lock(&mutex_board);
                    swap_cells(G.sel_r, G.sel_c, G.cursor_r, G.cursor_c);
                    pthread_mutex_unlock(&mutex_board);

                    pthread_mutex_lock(&mutex_score);
                    G.moves--;
                    pthread_mutex_unlock(&mutex_score);

                    if (G.moves <= 0) {
                        G.game_over  = true;
                        G.player_won = (G.score >= SCORE_GOAL);
                        G.running    = false;
                        pthread_cond_broadcast(&cond_match_ready);
                        pthread_cond_broadcast(&cond_gravity_ready);
                    }
                }
                G.selected = false;
            }
        }

        // Check victoria
        if (G.score >= SCORE_GOAL && !G.game_over) {
            G.game_over  = true;
            G.player_won = true;
            G.running    = false;
            pthread_cond_broadcast(&cond_match_ready);
            pthread_cond_broadcast(&cond_gravity_ready);
        }

        pthread_mutex_unlock(&mutex_state);
        sem_post(&sem_render);
    }
    return NULL;
}

// ============================================================
//  PANTALLAS DE MENÚ (sin hilos, secuencial)
// ============================================================

void print_logo() {
    printf("%s%s", BOLD, YELLOW);
    printf("  ██████╗ █████╗ ███╗   ██╗██████╗ ██╗   ██╗\n");
    printf(" ██╔════╝██╔══██╗████╗  ██║██╔══██╗╚██╗ ██╔╝\n");
    printf(" ██║     ███████║██╔██╗ ██║██║  ██║ ╚████╔╝ \n");
    printf(" ██║     ██╔══██║██║╚██╗██║██║  ██║  ╚██╔╝  \n");
    printf(" ╚██████╗██║  ██║██║ ╚████║██████╔╝   ██║   \n");
    printf("  ╚═════╝╚═╝  ╚═╝╚═╝  ╚═══╝╚═════╝    ╚═╝   \n");
    printf("%s", RESET);
    printf("%s%s", BOLD, RED);
    printf("  ██████╗██████╗ ██╗   ██╗███████╗██╗  ██╗\n");
    printf(" ██╔════╝██╔══██╗██║   ██║██╔════╝██║  ██║\n");
    printf(" ██║     ██████╔╝██║   ██║███████╗███████║\n");
    printf(" ██║     ██╔══██╗██║   ██║╚════██║██╔══██║\n");
    printf(" ╚██████╗██║  ██║╚██████╔╝███████║██║  ██║\n");
    printf("  ╚═════╝╚═╝  ╚═╝ ╚═════╝ ╚══════╝╚═╝  ╚═╝\n");
    printf("%s\n", RESET);
}

void screen_menu() {
    clear_screen();
    print_logo();
    printf("%s╔══════════════════════════════╗%s\n", CYAN, RESET);
    printf("%s║%s        MENÚ PRINCIPAL        %s║%s\n", CYAN, BOLD, CYAN, RESET);
    printf("%s╠══════════════════════════════╣%s\n", CYAN, RESET);
    printf("%s║%s  1. Iniciar Partida          %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s  2. Instrucciones            %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s  3. Puntajes Destacados      %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s  4. Salir                    %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s╚══════════════════════════════╝%s\n", CYAN, RESET);
    printf("\n  %sOpción:%s ", YELLOW, RESET);
    fflush(stdout);
}

void screen_instructions() {
    clear_screen();
    printf("%s%s╔══════════════════════════════════════════════╗%s\n", BOLD, CYAN, RESET);
    printf("%s%s║               INSTRUCCIONES                  ║%s\n", BOLD, CYAN, RESET);
    printf("%s%s╠══════════════════════════════════════════════╣%s\n", BOLD, CYAN, RESET);
    printf("%s║%s                                              %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s  OBJETIVO: Alcanzar %s%d puntos%s antes de       %s║%s\n", CYAN, WHITE, YELLOW, SCORE_GOAL, WHITE, CYAN, RESET);
    printf("%s║%s  agotar los movimientos disponibles.         %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s                                              %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s  CONTROLES:                                  %s║%s\n", CYAN, BOLD, CYAN, RESET);
    printf("%s║%s   W / A / S / D  →  Mover cursor            %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s   [Espacio]       →  Seleccionar / Confirmar %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s   Q               →  Salir al menú           %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s                                              %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s  CÓMO JUGAR:                                 %s║%s\n", CYAN, BOLD, CYAN, RESET);
    printf("%s║%s   1. Usa WASD para posicionar el cursor.     %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s   2. Presiona ESPACIO para seleccionar       %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s      un dulce (aparece [X]).                 %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s   3. Mueve el cursor al dulce adyacente y   %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s      presiona ESPACIO para intercambiar.     %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s   4. Combinar 3+ iguales suma puntos.        %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s   5. Combinar 4+ genera un dulce especial    %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s      (%s%cX%s) que elimina toda su fila.          %s║%s\n", CYAN, WHITE, YELLOW, SPECIAL_CHAR, WHITE, CYAN, RESET);
    printf("%s║%s                                              %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s  PUNTAJE:                                    %s║%s\n", CYAN, BOLD, CYAN, RESET);
    printf("%s║%s   3 en línea  → 30 pts                      %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s   4 en línea  → 40 pts + dulce especial     %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s   Especial    → +40 pts (toda la fila)      %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s║%s                                              %s║%s\n", CYAN, WHITE, CYAN, RESET);
    printf("%s╚══════════════════════════════════════════════╝%s\n", CYAN, RESET);
    printf("\n  Presiona %sENTER%s para volver...\n", YELLOW, RESET);
}

void screen_scores() {
    clear_screen();
    printf("%s%s╔══════════════════════════════╗%s\n", BOLD, CYAN, RESET);
    printf("%s%s║      PUNTAJES DESTACADOS     ║%s\n", BOLD, CYAN, RESET);
    printf("%s%s╠══════════════════════════════╣%s\n", BOLD, CYAN, RESET);

    ifstream f(SCOREBOARD);
    if (!f.is_open()) {
        printf("%s║%s  (Sin registros aún)         %s║%s\n", CYAN, WHITE, CYAN, RESET);
    } else {
        string line;
        int rank = 1;
        while (getline(f, line) && rank <= 10) {
            string display = line;
            if ((int)display.size() > 28) display = display.substr(0, 28);
            // Pad to 28 chars
            while ((int)display.size() < 28) display += ' ';
            printf("%s║%s  %d. %s%s║%s\n",
                   CYAN, WHITE, rank,
                   display.c_str(), CYAN, RESET);
            rank++;
        }
        f.close();
    }
    printf("%s╚══════════════════════════════╝%s\n", CYAN, RESET);
    printf("\n  Presiona %sENTER%s para volver...\n", YELLOW, RESET);
}

void save_score(const char* name, int score) {
    ofstream f(SCOREBOARD, ios::app);
    if (f.is_open()) {
        f << name << " - " << score << " pts\n";
        f.close();
    }
}

void screen_game_over() {
    clear_screen();
    if (G.player_won) {
        printf("%s%s\n", BOLD, GREEN);
        printf("  ██╗   ██╗██╗ ██████╗ ████████╗ ██████╗ ██████╗ ██╗ █████╗ \n");
        printf("  ██║   ██║██║██╔════╝ ╚══██╔══╝██╔═══██╗██╔══██╗██║██╔══██╗\n");
        printf("  ██║   ██║██║██║         ██║   ██║   ██║██████╔╝██║███████║\n");
        printf("  ╚██╗ ██╔╝██║██║         ██║   ██║   ██║██╔══██╗██║██╔══██║\n");
        printf("   ╚████╔╝ ██║╚██████╗    ██║   ╚██████╔╝██║  ██║██║██║  ██║\n");
        printf("    ╚═══╝  ╚═╝ ╚═════╝    ╚═╝    ╚═════╝ ╚═╝  ╚═╝╚═╝╚═╝  ╚═╝\n");
        printf("%s", RESET);
    } else {
        printf("%s%s\n", BOLD, RED);
        printf("  ██████╗  █████╗  ███╗   ███╗███████╗     ██████╗ ██╗   ██╗███████╗██████╗ \n");
        printf("  ██╔════╝██╔══██╗████╗ ████║██╔════╝    ██╔═══██╗██║   ██║██╔════╝██╔══██╗\n");
        printf("  ██║     ███████║██╔████╔██║█████╗      ██║   ██║██║   ██║█████╗  ██████╔╝\n");
        printf("  ██║     ██╔══██║██║╚██╔╝██║██╔══╝      ██║   ██║╚██╗ ██╔╝██╔══╝  ██╔══██╗\n");
        printf("  ╚██████╗██║  ██║██║ ╚═╝ ██║███████╗    ╚██████╔╝ ╚████╔╝ ███████╗██║  ██║\n");
        printf("   ╚═════╝╚═╝  ╚═╝╚═╝     ╚═╝╚══════╝     ╚═════╝   ╚═══╝  ╚══════╝╚═╝  ╚═╝\n");
        printf("%s", RESET);
    }
    printf("\n%s  Jugador: %s%s\n", WHITE, YELLOW, G.player_name);
    printf("%s  Puntaje final: %s%d%s  (Meta: %d)\n", WHITE, YELLOW, G.score, RESET, SCORE_GOAL);
    save_score(G.player_name, G.score);
    printf("\n  Puntaje guardado en scoreboard.\n");
    printf("\n  Presiona %sENTER%s para continuar...\n", GREEN, RESET);
    fflush(stdout);
}

// ============================================================
//  FUNCIÓN PRINCIPAL DE JUEGO
// ============================================================
void play_game() {
    // Inicializar estado
    memset(&G, 0, sizeof(G));
    G.cursor_r = 0; G.cursor_c = 0;
    G.sel_r    = -1; G.sel_c = -1;
    G.selected = false;
    G.game_over  = false;
    G.player_won = false;
    G.running    = true;
    G.match_pending   = false;
    G.gravity_pending = false;
    G.refill_pending  = false;
    G.pending_score   = 0;

    // Nombre y modo
    term_restore();
    clear_screen();
    printf("%s  Ingresa tu nombre: %s", YELLOW, RESET);
    fflush(stdout);
    // Leer nombre con eco normal
    struct termios cooked = orig_termios;
    tcsetattr(STDIN_FILENO, TCSAFLUSH, &cooked);
    fgets(G.player_name, sizeof(G.player_name), stdin);
    // Quitar newline
    int len = strlen(G.player_name);
    if (len > 0 && G.player_name[len-1] == '\n')
        G.player_name[len-1] = '\0';

    printf("\n%s  Selecciona modo:%s\n", YELLOW, RESET);
    printf("  1. %sFácil%s  (tablero 8x8, 5 dulces, %d movimientos)\n", GREEN, RESET, EASY_MOVES);
    printf("  2. %sDifícil%s (tablero 8x8, 7 dulces, %d movimientos)\n", RED, RESET, HARD_MOVES);
    printf("  Opción: ");
    fflush(stdout);
    char buf[8];
    fgets(buf, sizeof(buf), stdin);
    G.mode = (buf[0] == '2') ? 2 : 1;
    G.moves          = (G.mode == 1) ? EASY_MOVES : HARD_MOVES;
    G.num_candy_types = (G.mode == 1) ? NUM_CANDIES : NUM_CANDIES_H;

    srand((unsigned)time(NULL));
    init_board(G.num_candy_types);

    // Modo raw para el juego
    term_raw_mode();
    hide_cursor();
    clear_screen();

    // Inicializar semáforo
    sem_init(&sem_render, 0, 1);

    // Crear hilos
    pthread_t tid_input, tid_match, tid_score, tid_render, tid_gravity, tid_refill;
    pthread_create(&tid_render,  NULL, thread_render_fn,  NULL);
    pthread_create(&tid_input,   NULL, thread_input_fn,   NULL);
    pthread_create(&tid_match,   NULL, thread_match_fn,   NULL);
    pthread_create(&tid_score,   NULL, thread_score_fn,   NULL);
    pthread_create(&tid_gravity, NULL, thread_gravity_fn, NULL);
    pthread_create(&tid_refill,  NULL, thread_refill_fn,  NULL);

    // Esperar a que el juego termine
    pthread_join(tid_input,   NULL);

    // Señalizar cierre a todos los hilos bloqueados
    pthread_mutex_lock(&mutex_state);
    G.running = false;
    pthread_cond_broadcast(&cond_match_ready);
    pthread_cond_broadcast(&cond_gravity_ready);
    pthread_mutex_unlock(&mutex_state);
    sem_post(&sem_render);

    pthread_join(tid_match,   NULL);
    pthread_join(tid_score,   NULL);
    pthread_join(tid_gravity, NULL);
    pthread_join(tid_refill,  NULL);
    pthread_join(tid_render,  NULL);

    sem_destroy(&sem_render);

    show_cursor();
    term_restore();
    screen_game_over();

    // Esperar ENTER
    char dummy[4];
    fgets(dummy, sizeof(dummy), stdin);
}

// ============================================================
//  MAIN
// ============================================================
int main() {
    // Guardar terminal original
    tcgetattr(STDIN_FILENO, &orig_termios);

    int opt = 0;
    do {
        screen_menu();
        char buf[8];
        // Leer con eco para el menú
        struct termios cooked = orig_termios;
        tcsetattr(STDIN_FILENO, TCSAFLUSH, &cooked);
        fgets(buf, sizeof(buf), stdin);
        opt = buf[0] - '0';

        switch (opt) {
        case 1:
            play_game();
            break;
        case 2:
            screen_instructions();
            {
                struct termios cooked2 = orig_termios;
                tcsetattr(STDIN_FILENO, TCSAFLUSH, &cooked2);
                char d[4]; fgets(d, sizeof(d), stdin);
            }
            break;
        case 3:
            screen_scores();
            {
                struct termios cooked2 = orig_termios;
                tcsetattr(STDIN_FILENO, TCSAFLUSH, &cooked2);
                char d[4]; fgets(d, sizeof(d), stdin);
            }
            break;
        case 4:
            clear_screen();
            printf("%s  ¡Hasta pronto! 🍬%s\n\n", YELLOW, RESET);
            break;
        default:
            break;
        }
    } while (opt != 4);

    // Destruir primitivas
    pthread_mutex_destroy(&mutex_board);
    pthread_mutex_destroy(&mutex_score);
    pthread_mutex_destroy(&mutex_state);
    pthread_cond_destroy(&cond_match_ready);
    pthread_cond_destroy(&cond_gravity_ready);

    return 0;
}