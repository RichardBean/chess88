/*
 * chess88.c  --  a faithful, portable C99 translation of the chess engine inside
 *               Don Berg's CHESS88.EXE, which is itself a verbatim port of
 *               SARGON (Dan & Kathe Spracklen, 1978).
 *
 * Translated routine-for-routine from the commented Z80 source (sargon.asm),
 * which IS Chess88's engine.  Berg's two opening modifications are reproduced:
 *
 *   KEPT  : When playing White and it is the game's very first move (start
 *           position, no moves played), do not search; instead play one of four
 *           hard-coded moves chosen at random with equal probability:
 *               e2-e4 (35->55), d2-d4 (34->54), b1-c3 (22->43), g1-f3 (27->46).
 *           Toggleable via UCI option "Random" (default true).
 *   DROPPED: Berg's depth-1 cap on the first three moves is NOT implemented;
 *           we always search at the full selected PLYMAX, including the first
 *           three moves.
 *
 * No opening book (BOOK is not translated).
 *
 * The search machinery (PLYIX, SCORE and the linked move list) is implemented on
 * top of one flat byte-addressable memory image, so that FNDMOV / ASCEND / SORTM /
 * GENMOV can perform their pointer arithmetic exactly as the Z80 source does.
 * Pointers (MLPTRI, MLPTRJ, MLLST, MLNXT, BESTM, SCRIX) are byte offsets into that
 * image, and 16-bit links are stored little-endian just like Sargon.
 *
 * Portable C99; builds clean under:
 *     cc -O2 -Wall -Wextra -std=c99 -o chess88 chess88.c
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef uint8_t  u8;
typedef int8_t   s8;

/* ===== piece encoding: bit7 colour(1=black) bit4 king-castled bit3 moved bits2-0 type ===== */
enum { PAWN = 1, KNIGHT = 2, BISHOP = 3, ROOK = 4, QUEEN = 5, KING = 6 };
#define BLACK 0x80
#define WHITE 0x00
#define BPAWN (BLACK | PAWN)

/* ===== Sargon data tables (exact bytes) ===== */
static const s8 DIRECT[24] = { 9,11,-11,-9, 10,-10,1,-1, -21,-12,8,19, 21,12,-8,-19, 10,10,11,9, -10,-10,-11,-9 };
static const u8 DPOINT[7]  = { 20,16,8,0,4,0,0 };
static const u8 DCOUNT[7]  = { 4,4,8,4,4,8,8 };
/* PVALUE indexed by piece type 1..6 (Sargon's PVALUE = .-TBASE-1, bytes 1,3,3,5,9,10). */
static const s8 PVALUE[7]  = { 0,1,3,3,5,9,10 };
static const u8 PIECES[8]  = { 4,2,3,5,6,3,2,4 };

/* ===== board: 10 wide x 12 tall = 120, 0xFF border, playing squares 21..98 ===== */
static u8 board[120];

/* ===== search sizing ===== */
#define MAXPLY 20

/*
 * Flat memory image holding SCORE[], PLYIX[] and the move list MLIST.
 * Layout (byte offsets):
 *   SCORE : 2*(MAXPLY+4) bytes (Sargon stores words; only low byte carries the
 *           score, but we keep word stride so SCRIX++ matches the source).
 *   PLYIX : 2*2*(MAXPLY+4) bytes (a word PAIR per ply).
 *   MLIST : the remainder, holding 6-byte move records.
 * Offset 0 is never a valid move record (links of 0 == "none").
 */
#define SCORE_OFF  16                      /* leave a little headroom below */
#define SCORE_WORDS (MAXPLY + 6)
#define PLYIX_OFF  (SCORE_OFF + 2 * SCORE_WORDS)
#define PLYIX_WORDS (2 * (MAXPLY + 6))
#define MLIST_OFF  (PLYIX_OFF + 2 * PLYIX_WORDS)
#define MEM_SIZE   (MLIST_OFF + 256 * 1024)

static u8 mem[MEM_SIZE];

/* 8/16-bit accessors into the flat image */
static u8   rb(int a)            { return mem[a]; }
static void wb(int a, u8 v)      { mem[a] = v; }
static int  rw(int a)            { return (int)mem[a] | ((int)mem[a+1] << 8); }
static void ww(int a, int v)     { mem[a] = (u8)(v & 0xFF); mem[a+1] = (u8)((v >> 8) & 0xFF); }

/* move-record field offsets */
#define MLPTR 0   /* link (2 bytes, little-endian) */
#define MLFRP 2   /* from */
#define MLTOP 3   /* to   */
#define MLFLG 4   /* flags / captured piece */
#define MLVAL 5   /* value */

#define MLEND  (MEM_SIZE - 8)              /* last safe record start */

/* Persistent slot (below SCORE) holding the most recently played game move, so
 * that ENPSNT can detect an en-passant capture at the root.  Two 6-byte records
 * fit (a double move's halves).  Offset 0 stays reserved as the null link. */
#define LASTMV_OFF 4

/* ===== King/Queen position list (POSK/POSQ) =====
 *   [0]=white King, [1]=black King, [2]=white Queen, [3]=black Queen, [4]=0xFF.
 */
static u8 posk[5];
#define IPOSK 0
#define IPOSQ 2

/* ===== working cells (mirror Sargon's named bytes) ===== */
static u8 T1, T2, T3;
static u8 M1, M2, M3, M4;
static u8 INDX2;
static u8 P1, P2, P3;

static u8 KOLOR, COLOR;
static u8 MOVENO;
static u8 PLYMAX = 4;
static u8 NPLY;
static u8 CKFLG, MATEF, VALM;
static u8 BRDC;
static u8 PTSL, PTSW1, PTSW2;
static u8 MTRL;
static u8 BC0, MV0;
static u8 PTSCK;
static u8 PMATE;

/* attack list (ATKLST), 14 bytes nibble-packed exactly as Sargon. */
static u8 ATKLST[14];
/* Chess88's per-square ATKLST clear is `mov al,0; rep stosw` -- it clears AL but
 * NOT AH, so it stores 0x(AH)00 into every word, leaving the leftover AH register in
 * each empty type-slot's high byte.  g_atk_ah tracks that AH register (updated by
 * NEXTAD_val / ATKSAV exactly as the 8086 leaves AX); the dirty clear in POINTS uses
 * it.  This reproduces the quirk where an empty type-slot reads as a value-0 attacker
 * and aborts XCHNG (the exchange evaluator under-counts material). */
static u8 g_atk_ah;
#define WACT 0
#define BACT 7

/* pinned-piece list (1-based indices 1..10, like Sargon's PLIST=.-TBASE-1) */
static u8 PLISTA[21];
static u8 PLISTD[21];
static u8 NPINS;

/* pointers (byte offsets into mem[]) */
static int MLNXT;     /* next available move record */
static int MLLST;     /* previous record written (chain build) */
static int MLPTRI;    /* current ply pair pointer (points at pair's CURRENT word) */
static int MLPTRJ;    /* current move record being processed */
static int SCRIX;     /* score table pointer */
static int BESTM;     /* best move record offset */

static int random_first = 1;
/* 1 = reproduce Chess88's eval (rook/queen development penalty always on);
 * 0 = stock Sargon (penalty only while MOVENO<7).  See POINTS PT6 block. */
/* Compile with -DSTOCK_SARGON to build the bug-free "Sargon 1978" opponent: all THREE
 * Berg port bugs -- development penalty (eval_c88), pin off-by-one (eval_c88_pin), and
 * the leftover-AH attack-list clear (eval_c88_dirty) -- default OFF.  Without the flag
 * this is the faithful Chess88 (all three bugs ON), exactly as validated 140/140. */
#ifdef STOCK_SARGON
static int eval_c88 = 0;
static int eval_c88_pin = 0;
static int eval_c88_dirty = 0;   /* leftover-AH attack-list clear (bug 3) OFF */
#else
static int eval_c88 = 1;
static int eval_c88_pin = 1;     /* Berg pin-in-board-control bug (every POINTS) */
static int eval_c88_dirty = 1;   /* leftover-AH attack-list clear (bug 3) ON */
#endif
static int eval_c88_capdev = 0;  /* capture-developed quirk (off: did not reproduce) */
static long g_nodes = 0;         /* moves made this search (UCI "nodes" for SCID) */

/* ============================================================ INITBD (403) */
static void INITBD(void)
{
    int i, x;
    for (i = 0; i < 120; i++) board[i] = 0xFF;
    for (x = 0; x < 8; x++) {
        u8 a = PIECES[x];
        board[21 + x] = a;
        a = (u8)(a | 0x80);
        board[91 + x] = a;
        board[31 + x] = PAWN;
        board[81 + x] = BPAWN;
        board[41 + x] = 0;
        board[51 + x] = 0;
        board[61 + x] = 0;
        board[71 + x] = 0;
    }
    posk[0] = 25; posk[1] = 95; posk[2] = 24; posk[3] = 94; posk[4] = 0xFF;
}

/* ============================================================ PATH (456)
 * 0 empty, 1 opposite colour, 2 same colour, 3 off board.  Updates M2,P2,T2. */
static u8 PATH(s8 c)
{
    u8 a;
    M2 = (u8)(M2 + c);
    a = board[M2];
    if (a == 0xFF) return 3;
    P2 = a;
    T2 = (u8)(a & 7);
    if (a == 0) return 0;
    a = (u8)(P2 ^ P1);
    if ((a & 0x80) == 0) return 2;
    return 1;
}

/* forward decls */
static void ADMOVE(void);
static void CASTLE(void);
static void ENPSNT(void);
static u8   ATTACK(void);
static void ATKSAV(void);
static int  PNCK(void);
static void ADJPTR(void);
static u8   INCHK(void);
static u8   INCHK1(u8 col);

/* shadow flag for MPIECE's EXAF dance (was the square empty?) */
static int EXAF_empty;

/* ============================================================ MPIECE (497) */
static void MPIECE(void)
{
    u8 a, t;
    int b, yi;

    a = (u8)(P1 & 0x87);
    if (a == BPAWN) a--;            /* black pawn uses move-type index 0 */
    a &= 7;
    t = a;
    T1 = t;
    b = DCOUNT[t];
    INDX2 = DPOINT[t];
    yi = INDX2;

    while (b > 0) {
        s8 c = DIRECT[yi];                  /* MP5 */
        M2 = M1;
    MP10:
        a = PATH(c);
        if (a >= 2) goto MP15;              /* CPI 2 ; JRNC MP15 */
        EXAF_empty = (a == 0);
        if (T1 < PAWN + 1) goto MP20;       /* pawn logic */
        ADMOVE();
        if (!EXAF_empty) goto MP15;
        if (T1 == KING) goto MP15;
        if (T1 >= BISHOP) goto MP10;        /* bishop/rook/queen: slide on (keep M2,c) */
        goto MP15;                          /* knight: single step */

    MP15:
        yi++; b--;
        continue;

    MP20:
        {
            int bc = b;
            if (bc < 3) goto MP35;          /* diagonal capture/en-passant */
            if (bc == 3) goto MP30;         /* the two-square move */
            /* one-square forward */
            if (!EXAF_empty) goto MP15;
            if (M2 >= 91) goto MP25;        /* white promotion */
            if (M2 >= 29) goto MP26;        /* no promotion */
        MP25:
            P2 |= 0x20;
        MP26:
            ADMOVE();
            yi++; b--;                      /* adjust to two-square move */
            if (P1 & 0x08) goto MP15;       /* already moved -> no 2-square */
            goto MP10;                       /* try the two-square step (keep M2,c) */
        }
    MP30:
        if (!EXAF_empty) goto MP15;
        ADMOVE();
        goto MP15;
    MP35:
        if (EXAF_empty) { ENPSNT(); goto MP15; }
        if (M2 >= 91) goto MP37;            /* white promotion capture */
        if (M2 >= 29) { ADMOVE(); goto MP15; }
    MP37:
        P2 |= 0x20;
        ADMOVE();
        goto MP15;
    }

    if (T1 == KING) CASTLE();
}

/* ============================================================ ENPSNT (588) */
static void ENPSNT(void)
{
    u8 a, diff;
    int x;

    a = M1;
    if (P1 & 0x80) a = (u8)(a + 10);
    if (a < 61) return;
    if (a >= 69) return;

    x = MLPTRJ;
    if (!(rb(x + MLFLG) & 0x10)) return;   /* previous move must be a first move */
    M4 = rb(x + MLTOP);
    P3 = board[M4];
    if ((P3 & 7) != PAWN) return;

    {
        s8 d = (s8)(M4 - M2);
        if (d < 0) d = (s8)(-d);
        diff = (u8)d;
    }
    if (diff != 10) return;

    P2 |= 0x40;
    ADMOVE();                              /* capturing pawn advance */

    M3 = M1;
    M1 = M4; M2 = M4;
    P2 = P3;
    ADMOVE();                              /* remove captured pawn (dummy move) */
    M1 = M3;
    ADJPTR();
}

/* ============================================================ ADJPTR (646) */
static void ADJPTR(void)
{
    MLLST -= 6;
    ww(MLLST + MLPTR, 0);
}

/* ============================================================ CASTLE (671) */
static void CASTLE(void)
{
    int b, c;

    if (P1 & 0x08) return;
    if (CKFLG) return;

    b = 0xFF; c = 0x03;                    /* king side: step -1, rook offset +3 */
    for (;;) {
        u8 a;
        a = (u8)(M1 + (s8)c);              /* rook position */
        c = a;
        M3 = a;
        a = (u8)(board[M3] & 0x7F);
        if (a != ROOK) goto CA20;
        a = (u8)c;
        goto CA15;
    CA10:
        a = board[M3];
        if (a != 0) goto CA20;
        a = M3;                            /* Sargon LDA M3 BEFORE the QN-square test */
        if (M3 == 22) goto CA15;
        if (M3 == 92) goto CA15;
        if (ATTACK() != 0) goto CA20;
        a = M3;                            /* reload (ATTACK clobbers A in the Z80 original) */
    CA15:
        a = (u8)(a + (s8)b);
        M3 = a;
        if (a != M1) goto CA10;
        a = (u8)(a - (s8)b);
        a = (u8)(a - (s8)b);
        M2 = a;
        P2 = 0x40;
        ADMOVE();                          /* king move */
        a = M1;
        M1 = (u8)c;
        a = (u8)(a - (s8)b);
        M2 = a;
        P2 = 0;
        ADMOVE();                          /* rook move */
        ADJPTR();
        M1 = M3;
    CA20:
        if (b == 1) return;
        b = 0x01; c = 0xFC;                /* queen side: step +1, rook offset -4 */
    }
}

/* ============================================================ ADMOVE (745) */
static void ADMOVE(void)
{
    int dst = MLNXT;
    if (dst > MLEND) {                     /* table overflow: abort entry */
        ww(MLLST + MLPTR, 0);
        return;
    }
    ww(MLLST + MLPTR, dst);                /* link previous -> this */
    MLLST = dst;
    if (!(P1 & 0x08)) P2 |= 0x10;          /* first-move flag */
    ww(dst + MLPTR, 0);
    wb(dst + MLFRP, M1);
    wb(dst + MLTOP, M2);
    wb(dst + MLFLG, P2);
    wb(dst + MLVAL, 0);
    MLNXT = dst + 6;
}

/* ============================================================ GENMOV (798) */
static void GENMOV(void)
{
    u8 pos;

    CKFLG = INCHK();

    /* Advance the ply pair pointer.  Sargon stores MLNXT into the pair's FIRST word
     * [MLPTRI-2] (preserved for ASCEND's MLNXT restore) and sets both MLPTRI and
     * MLLST to the pair's CURRENT word [MLPTRI].  ADMOVE then links the first move
     * into [MLLST] = [MLPTRI], so FM15 (which walks from MLPTRI) finds it. */
    MLPTRI += 2;                           /* INX H, INX H */
    ww(MLPTRI, MLNXT);                     /* store head pointer into [old+2] */
    MLPTRI += 2;                           /* HL = old+4 (the current word) */
    MLLST = MLPTRI;                        /* SHLD MLLST = old+4 */

    for (pos = 21; pos != 99; pos++) {
        u8 a;
        M1 = pos;
        a = board[pos];
        if (a == 0) continue;
        if (a == 0xFF) continue;
        P1 = a;
        a = (u8)(a ^ COLOR);
        if (!(a & 0x80)) MPIECE();
    }
}

/* ============================================================ INCHK / INCHK1 (844) */
static u8 INCHK1(u8 col)
{
    u8 kp = (col == WHITE) ? posk[IPOSK] : posk[IPOSK + 1];
    M3 = kp;
    P1 = board[M3];
    T1 = (u8)(P1 & 7);
    return ATTACK();
}
static u8 INCHK(void) { return INCHK1(COLOR); }

/* ============================================================ ATTACK (892) */
static u8 ATTACK_D;        /* D register: flags(bit5/6/7) + low-nibble scan count */
static int ATTACK_abort;   /* set when PNCK rejects this attacker */
static s8  ATTACK_dir;     /* current ray direction (for PNCK) */

static u8 ATTACK(void)
{
    int b, yi;
    b = 16;
    INDX2 = 0;
    yi = 0;

    for (; b > 0; b--, yi++) {
        s8 c = DIRECT[yi];
        u8 d = 0;
        M2 = M3;
        ATTACK_dir = c;
        for (;;) {                          /* AT10 */
            u8 r;
            d = (u8)(d + 1);
            r = PATH(c);
            if (r == 1) {                   /* opposite colour */
                if (d & 0x40) break;        /* same colour seen earlier */
                d |= 0x20;
            } else if (r == 2) {            /* same colour */
                if (d & 0x20) break;
                d |= 0x40;
            } else if (r == 3) {
                break;                      /* off board */
            } else {
                if (b < 9) break;           /* empty, knight scan -> stop */
                continue;                   /* empty, slider -> keep going */
            }

            /* AT14: does the encountered piece attack the square? */
            {
                u8 e = T2;
                int attacks = 0;
                if (b < 9) {
                    attacks = (e == KNIGHT);
                } else if (e == QUEEN) {
                    d |= 0x80;
                    attacks = 1;
                } else if ((d & 0x0F) == 1 && e == KING) {
                    attacks = 1;
                } else if (b < 13) {
                    attacks = (e == ROOK);  /* files / ranks */
                } else if (e == BISHOP) {
                    attacks = 1;            /* diagonals */
                } else if ((d & 0x0F) == 1 && e == PAWN) {
                    if (P2 & 0x80) {        /* black pawn */
                        attacks = (b >= 15);
                    } else {                /* white pawn */
                        attacks = (b < 15);
                    }
                }
                if (!attacks) break;        /* AT12: next direction */
            }

            /* AT30 */
            ATTACK_D = d;
            if (T1 == 7) {
                ATTACK_abort = 0;
                ATKSAV();
                /* if aborted, the piece was just not recorded; scan continues */
            } else {
                if (d & 0x20) return 1;     /* opposite-colour attacker found */
            }
            /* AT32: kings and knights do not see through; others are transparent */
            if (T2 == KING) break;
            if (T2 == KNIGHT) break;
            /* loop AT10 again (transparency) */
        }
    }
    return 0;
}

/* ============================================================ ATKSAV (1007) */
static void ATKSAV(void)
{
    int base;
    u8  e;
    s8  val;
    int slot;
    u8  pv;

    if (NPINS != 0) {
        if (PNCK()) { ATTACK_abort = 1; return; }
    }

    val = PVALUE[T2];

    base = (P2 & 0x80) ? BACT : WACT;
    e = (u8)(P2 & 7);
    if (ATTACK_D & 0x80) e = QUEEN;

    ATKLST[base]++;
    slot = base + e;
    pv = (u8)(val & 0x0F);

    /* Sargon stores into a WORD per type: word = (old_low << 8) | PVALUE, i.e. the new
     * value goes to the LOW byte and the old low byte rotates up to HIGH (AH ends as the
     * value just placed in the high byte).  Modelled here with low/high NIBBLES.  The
     * low-empty case CLEARS the dirty high (old_low==0), which is the key to overwriting
     * the leftover-AH garbage when a real attacker exists. */
    if ((ATKLST[slot] & 0x0F) == 0) {
        ATKLST[slot] = pv;                       /* AH := old_low (0) */
        g_atk_ah = 0;
    } else if ((ATKLST[slot] & 0xF0) == 0) {
        ATKLST[slot] = (u8)((ATKLST[slot] & 0x0F) | (pv << 4));
        g_atk_ah = pv;                           /* AH := PVALUE */
    } else {
        /* both nibbles full: rotate into the NEXT slot (Sargon INX H; jmp AS20). */
        slot++;
        g_atk_ah = (u8)(ATKLST[slot] & 0x0F);    /* AH := next slot's old low */
        ATKLST[slot] = (u8)(((ATKLST[slot] & 0x0F) << 4) | pv);
    }
}

/* ============================================================ PNCK (1066)
 * Returns 1 if the attacker (at M2) is pinned in a direction that conflicts with
 * the attack direction (so it must be excluded), else 0. */
static int PNCK(void)
{
    s8  dir = ATTACK_dir;
    u8  pos = M2;
    int i, j;

    /* Berg's Chess88 ATKSAV has an OFF-BY-ONE in its pin scan with a subtle second
     * effect.  The REPNE SCASB starts at PLISTA[0] (0x165) with CX=NPINS, scanning
     * indices [0..NPINS-1]: it tests a junk slot and never reaches the last-recorded
     * pin PLISTA[NPINS] (so that pin's piece is never excluded -- effect #1, what
     * spares a lone black pin e6/c6).  But there is also effect #2: after a VALID
     * direction match (piece pinned but attacking along the pin line), the code loops
     * back to the SCASB to look for a second occurrence.  When the match was the LAST
     * slot scanned (i == NPINS-1, so CX is already 0), that second SCASB is a no-op and
     * the ZF=1 left by the direction compare falls through 0x98 into the "already found"
     * path at 0x9b -> the piece is EXCLUDED even though it legally attacks along the pin.
     * This is what makes Chess88 score a defended capturing piece (e.g. Bxg6, where the
     * captured-square bishop pins the f7-pawn to the king) as SAFE: the f7-pawn sits at
     * PLISTA[NPINS-1] and is wrongly dropped, leaving only Rg8 (>bishop) as attacker, so
     * the exchange evaluates to 0.  Confirmed by the live d3g6 dump M+03 B+12 L+00 C+00.
     * Stock Sargon scans [1..NPINS] correctly and applies neither effect. */
    int _hi = eval_c88_pin ? (int)NPINS - 1 : (int)NPINS;
    for (i = 1; i <= _hi; i++) {
        if (PLISTA[i] != pos) continue;         /* first occurrence of this attacker */
        {   s8 pd = (s8)PLISTD[i];
            if (pd != dir && (s8)(-(int)pd) != dir)
                return 1;                       /* PC5: direction conflicts -> exclude */
        }
        /* valid along pin: SCASB resumes looking for a second occurrence in (i.._hi] */
        for (j = i + 1; j <= _hi; j++)
            if (PLISTA[j] == pos) return 1;     /* pinned on two lines -> exclude */
        if (eval_c88_pin && i == _hi)
            return 1;                           /* effect #2: CX-exhausted misfire excludes */
        return 0;                               /* otherwise the attacker counts */
    }
    return 0;
}

/* ============================================================ PINFND (1110) */
static void PINFND(void)
{
    int di;

    NPINS = 0;
    di = 0;
    for (;;) {
        u8 royal = posk[di];
        int b, yi;
        if (royal == 0) { di++; continue; }
        if (royal == 0xFF) return;
        M3 = royal;
        P1 = board[M3];
        b = 8;
        INDX2 = 0;
        yi = 0;

        for (; b > 0; b--, yi++) {
            s8 c = DIRECT[yi];
            M2 = M3;
            M4 = 0;
            for (;;) {                          /* PF5 */
                u8 r = PATH(c);
                if (r == 0) continue;
                if (r == 3) break;
                if (r == 2) {                   /* same colour */
                    if (M4 != 0) break;         /* two same-colour -> no pin */
                    M4 = M2;
                    continue;
                }
                /* r == 1: opposite colour */
                if (M4 == 0) break;             /* nothing behind to pin */
                {
                    u8 e = T2;
                    if (e == QUEEN) {
                        if ((P1 & 7) == QUEEN) {
                            int wd, bd;
                            int res;
                            memset(ATKLST, 0, sizeof(ATKLST));
                            T1 = 7;
                            ATTACK();
                            if (P1 & 0x80) { bd = ATKLST[BACT]; wd = ATKLST[WACT]; }
                            else           { bd = ATKLST[WACT]; wd = ATKLST[BACT]; }
                            res = bd - wd - 1;   /* defenders - attackers - 1 */
                            if (res >= 0) break; /* JP PF25: pin not valid */
                            /* else fall to record */
                        }
                        /* PF20 (queen pins) */
                    } else {
                        if (b > 4) {            /* diagonal directions (yi 0..3) */
                            if (e != BISHOP) break;
                        } else {                /* straight directions (yi 4..7) */
                            if (e != ROOK) break;
                        }
                    }
                    NPINS++;
                    PLISTD[NPINS] = (u8)c;
                    PLISTA[NPINS] = M4;
                    break;
                }
            }
        }
        di++;
    }
}

/* ============================================================ NEXTAD (1282) / XCHNG (1219)
 * Static exchange evaluation.  We model NEXTAD's cheapest-first retrieval and the
 * doubling of each value, then run XCHNG's alternating accumulation. */
static int  nx_count[2], nx_pos[2], nx_base[2], nx_side;

static int NEXTAD_val(int *out)
{
    int side;
    nx_side ^= 1;
    side = nx_side;
    if (nx_count[side] == 0) { *out = 0; g_atk_ah = 0; return 0; }  /* Sargon mov ax,0 */
    for (;;) {
        nx_pos[side]++;
        if (nx_pos[side] >= nx_base[side] + 7) { *out = 0; g_atk_ah = 0; return 0; }
        if (ATKLST[nx_pos[side]] != 0) break;     /* SCASW: first non-zero WORD */
    }
    nx_count[side]--;
    {
        u8 byte = ATKLST[nx_pos[side]];
        u8 v = (u8)(byte & 0x0F);                 /* value = LOW byte (0 for a dirty slot) */
        ATKLST[nx_pos[side]] = (u8)(byte >> 4);   /* RRD */
        g_atk_ah = (u8)((byte >> 4) & 0x0F);      /* AH := word's high byte */
        nx_pos[side]--;
        *out = (int)((v + v) & 0xFF);             /* doubled */
        return 1;
    }
}

static int XCHNG_D, XCHNG_E;

static void XCHNG(void)
{
    int b, e, cval, Dreg;
    int atk, dfd, Lval;

    if (P1 & 0x80) {
        nx_base[0] = WACT; nx_count[0] = ATKLST[WACT]; nx_pos[0] = WACT;  /* attackers */
        nx_base[1] = BACT; nx_count[1] = ATKLST[BACT]; nx_pos[1] = BACT;  /* defenders */
    } else {
        nx_base[0] = BACT; nx_count[0] = ATKLST[BACT]; nx_pos[0] = BACT;  /* attackers */
        nx_base[1] = WACT; nx_count[1] = ATKLST[WACT]; nx_pos[1] = WACT;  /* defenders */
    }
    nx_side = 1;                                  /* first toggle -> side 0 */

    cval = 0;
    e = 0;
    /* Sargon keeps TWO copies of the doubled attacked-piece value: register D is
     * set once and NEVER changed (it is what POINTS reads back as the material
     * value), while register B is the running "current attacked value" that the
     * exchange loop mutates via `MOV B,L`.  Only B participates in the swap; D is
     * frozen.  XCHNG_D must therefore return the ORIGINAL doubled value, not b. */
    Dreg = (PVALUE[T3] << 1) & 0xFF;              /* register D (frozen) */
    b = Dreg;                                     /* register B (running) */

    /* Sargon increments the swap counter (BP) INSIDE NEXTAD and then branches on the
     * ZF left by NEXTAD's `add al,al` -- so a value-0 result (count exhausted OR an
     * empty type-slot left dirty by the leftover-AH clear) is treated as "no piece".
     * The first attacker being value-0 aborts the exchange (XCHNG returns e=0). */
    NEXTAD_val(&atk); cval++;
    if (atk == 0) { XCHNG_D = Dreg; XCHNG_E = e; return; }

    for (;;) {                                    /* XC10 */
        Lval = atk;
        NEXTAD_val(&dfd); cval++;
        if (dfd == 0) goto XC18;                  /* jz: no defender */
        if (b >= Lval) goto XC18;                 /* jnc: attacked >= attacker (XC19==XC18) */
    XC15:
        if (dfd < Lval) { XCHNG_D = Dreg; XCHNG_E = e; return; }  /* defender < attacker */
        NEXTAD_val(&atk); cval++;
        if (atk == 0) { XCHNG_D = Dreg; XCHNG_E = e; return; }    /* je: no attacker */
        Lval = atk;
        NEXTAD_val(&dfd); cval++;
        if (dfd != 0) goto XC15;                  /* jnz: more defenders */
        dfd = 0;
    XC18:
        {
            int aval = b;
            if (cval & 1) aval = (-aval) & 0xFF;
            e = (e + aval) & 0xFF;
            if (dfd == 0) { XCHNG_D = Dreg; XCHNG_E = e; return; }
            /* MOV B,L : prev attacker (Lval) becomes the new attacked value; the
             * prev defender (dfd) becomes the new attacker. */
            b = Lval;
            atk = dfd;
            continue;                             /* XC10 with prev defender as attacker */
        }
    }
}

/* ============================================================ LIMIT (1500) */
static u8 LIMIT(u8 limit, s8 b)
{
    if (b & 0x80) {
        s8 n = (s8)(-(int)b);
        if ((u8)n >= limit) return (u8)(-(int)limit);
        return (u8)b;
    } else {
        if ((u8)b >= limit) return limit;
        return (u8)b;
    }
}

/* ============================================================ POINTS (1317) */
static void POINTS(void)
{
    int sq;

    MTRL = 0; BRDC = 0; PTSL = 0; PTSW1 = 0; PTSW2 = 0; PTSCK = 0;
    g_atk_ah = 0;          /* AH register at POINTS entry; Sargon's PINFND leaves it 0 */
    T1 = 7;

    for (sq = 21; sq != 99; sq++) {
        u8 piece, ptype;
        M3 = (u8)sq;
        piece = board[M3];
        if (piece == 0xFF) continue;
        P1 = piece;
        ptype = (u8)(piece & 7);
        T3 = ptype;

        /* development / castling adjustments (PT5..PT6D) */
        if (ptype >= KNIGHT) {
            int do_adj = 0;
            s8 adj = 0;
            if (ptype < ROOK) {                    /* knight/bishop: PT6B */
                if (!(P1 & 0x08)) { adj = (P1 & 0x80) ? (s8)2 : (s8)-2; do_adj = 1; }
            } else if (ptype == KING) {            /* PT6AA */
                if (P1 & 0x10) { adj = (P1 & 0x80) ? (s8)-6 : (s8)6; do_adj = 1; }
                else if (P1 & 0x08) { adj = (P1 & 0x80) ? (s8)2 : (s8)-2; do_adj = 1; }
            } else {                               /* rook/queen */
                /* Stock Sargon gates this penalty on MOVENO<7 (CPI 7; JRC PT6A;
                 * JMP PT6X).  Berg's Chess88 mistranslated the JMP PT6X as
                 * JNC PT6A (bytes "72 13 / 73 11" at 0xcee), so BOTH branches
                 * fall into the penalty path -> a developed rook/queen is
                 * penalised at every move number, not just the opening.  With
                 * eval_c88 set we reproduce that; clear it for stock Sargon. */
                if ((eval_c88 || MOVENO < 7) && (P1 & 0x08)) {
                    adj = (P1 & 0x80) ? (s8)2 : (s8)-2; do_adj = 1;
                }
            }
            if (do_adj) BRDC = (u8)(BRDC + (u8)adj);
        }

        /* PT6X: build attack list.  Sargon's clear (`mov al,0; rep stosw`) leaves the
         * leftover AH in every word's high byte: empty type-slots become (g_atk_ah<<4)
         * in the high nibble, 0 in the low; the count slots (WACT/BACT) read back as the
         * incremented count (their high byte is never scanned by NEXTAD). */
        {
            int k;
            for (k = 0; k < 14; k++)
                ATKLST[k] = (k == WACT || k == BACT) ? 0
                          : (u8)(eval_c88_dirty ? ((g_atk_ah & 0x0F) << 4) : 0);
        }
        ATTACK();
        BRDC = (u8)(BRDC + (u8)((s8)ATKLST[WACT] - (s8)ATKLST[BACT]));

        if (P1 == 0) continue;

        /* exchange evaluation */
        XCHNG();
        {
            int D = XCHNG_D;
            int E = XCHNG_E;
            if (E != 0) {
                u8 cmp = (u8)(P1 ^ COLOR);
                D = (D - 1) & 0xFF;                /* deduct half a pawn */
                if (cmp & 0x80) {
                    /* PT20: points won by side to move.
                     * Sargon keeps A = max(E,PTSW1)'s "loser": if E>=PTSW1, PTSW1
                     * becomes E and A=old PTSW1; else PTSW1 stays and A=E.  Then the
                     * second-max PTSW2 absorbs A whenever A>=PTSW2. */
                    u8 A;
                    if ((u8)E >= PTSW1) {
                        A = PTSW1;
                        PTSW1 = (u8)E;
                    } else {
                        A = (u8)E;
                    }
                    if (A >= PTSW2) PTSW2 = A;
                } else {
                    /* PTSL: points lost */
                    if ((u8)E >= PTSL) {
                        PTSL = (u8)E;
                        if (M3 == rb(MLPTRJ + MLTOP)) PTSCK = M3;
                    }
                }
            }
            {
                s8 v = (s8)D;
                if (P1 & 0x80) v = (s8)(-(int)v);
                MTRL = (u8)(MTRL + (u8)v);
            }
        }
    }

    /* PT25A */
    if (PTSCK != 0) { PTSW1 = PTSW2; PTSW2 = 0; }
    {
        s8 a;
        u8 B = PTSL;
        s8 mat;
        u8 Ev, Dv;

        if (B != 0) B = (u8)(B - 1);
        if (PTSW1 == 0) {
            a = (s8)(0 - (int)B);
        } else {
            u8 w2 = PTSW2;
            if (w2 != 0) w2 = (u8)(w2 - 1);
            w2 = (u8)(w2 >> 1);
            a = (s8)((int)(s8)w2 - (int)(s8)B);
        }
        if (COLOR & 0x80) a = (s8)(-(int)a);
        mat = (s8)((int)(s8)(MTRL + (u8)a) - (int)(s8)MV0);
        Ev = LIMIT(30, mat);

        {
            s8 b2 = (s8)(BRDC - BC0);
            if (PTSCK != 0) b2 = 0;
            Dv = LIMIT(6, b2);
        }

        {
            s8 m = (s8)Ev;
            int total = ((int)m + m + m + m) + (int)(s8)Dv;
            if (!(COLOR & 0x80)) total = -total;
            total = (total + 0x80) & 0xFF;
            VALM = (u8)total;
            wb(MLPTRJ + MLVAL, (u8)total);
        }
    }
}

/* ============================================================ MOVE (1530) */
static void MOVE(void)
{
    int p = MLPTRJ;
    g_nodes++;

MV1:
    p += 2;
    M1 = rb(p); p++;
    M2 = rb(p); p++;
    {
        u8 D = rb(p);
        u8 E = board[M1];
        if (D & 0x20) { E |= 0x04; goto MV5; }    /* promotion: pawn -> queen */
        {
            u8 t = (u8)(E & 7);
            if (t == QUEEN) { int h = IPOSQ; if (E & 0x80) h++; posk[h] = M2; goto MV5; }
            if (t == KING) {
                int h = IPOSK;
                if (D & 0x40) E |= 0x10;          /* castled flag */
                if (E & 0x80) h++;
                posk[h] = M2;
                goto MV5;
            }
        }
    MV5:
        E |= 0x08;
        board[M2] = E;
        board[M1] = 0;
        if (D & 0x40) goto MV40;                  /* double move */
        {
            u8 ct = (u8)(D & 7);
            if (ct == QUEEN) { int h = IPOSQ; if (D & 0x80) h++; posk[h] = 0; }
        }
        return;
    }
MV40:
    /* second half of a double move: the next 6-byte record.  Sargon adds 8 to
     * MLPTRJ and re-enters AFTER the 2-byte link skip; our MV1 re-applies the +2
     * skip, so we add 6 here. */
    p = MLPTRJ + 6;
    goto MV1;
}

/* ============================================================ UNMOVE (1604) */
static void UNMOVE(void)
{
    int p = MLPTRJ;

UM1:
    p += 2;
    M1 = rb(p); p++;
    M2 = rb(p); p++;
    {
        u8 D = rb(p);
        u8 E = board[M2];
        if (D & 0x20) { E &= (u8)~0x04; goto UM5; }   /* undo promotion */
        {
            u8 t = (u8)(E & 7);
            if (t == QUEEN) { int h = IPOSQ; if (E & 0x80) h++; posk[h] = M1; goto UM5; }
            if (t == KING) {
                int h = IPOSK;
                if (D & 0x40) E &= (u8)~0x10;
                if (E & 0x80) h++;
                posk[h] = M1;
                goto UM5;
            }
        }
    UM5:
        if (D & 0x10) E &= (u8)~0x08;             /* clear moved flag (first move) */
        board[M1] = E;
        board[M2] = (u8)(D & 0x8F);
        if (D & 0x40) goto UM40;
        {
            u8 ct = (u8)(D & 7);
            if (ct == QUEEN) { int h = IPOSQ; if (D & 0x80) h++; posk[h] = M2; }
        }
        return;
    }
UM40:
    p = MLPTRJ + 6;     /* +8 in Sargon minus our re-applied +2 link skip */
    goto UM1;
}

/* ============================================================ EVAL (1733) */
static void EVAL(void)
{
    MOVE();
    if (INCHK() != 0) {
        VALM = 0;
        wb(MLPTRJ + MLVAL, 0);
    } else {
        PINFND();
        POINTS();
    }
    UNMOVE();
}

/* ============================================================ SORTM (1679)
 * Re-link the current ply's move list into ascending order of value byte, after
 * evaluating each move via EVAL.
 *
 * Sargon roots the working list at [MLPTRI] (the pair's CURRENT word).  We pull
 * each node off the original chain, EVAL it (which sets MLVAL via POINTS, or 0 for
 * an illegal move), then insert it into the sorted chain rooted at the same word.
 * Tie-break matches Sargon's "JRNC SR30": insert after all nodes of equal value. */
static void SORTM(void)
{
    int head_word = MLPTRI;                /* working/sorted list head */
    int cur = rw(head_word);               /* first node in the original chain */

    /* detach the original chain from the head; we rebuild it sorted. */
    ww(head_word, 0);

    while (cur != 0) {
        int nxt = rw(cur + MLPTR);         /* original next, captured before relink */

        MLPTRJ = cur;
        EVAL();                            /* sets VALM and node's MLVAL */

        {
            int prev = -1;                 /* -1 means "at head word" */
            int node = rw(head_word);
            int v = VALM;
            for (;;) {
                if (node == 0) {
                    if (prev == -1) ww(head_word, cur);
                    else ww(prev + MLPTR, cur);
                    ww(cur + MLPTR, 0);
                    break;
                }
                if (v < rb(node + MLVAL)) {
                    if (prev == -1) ww(head_word, cur);
                    else ww(prev + MLPTR, cur);
                    ww(cur + MLPTR, node);
                    break;
                }
                prev = node;
                node = rw(node + MLPTR);
            }
        }
        cur = nxt;
    }
}

/* ============================================================ FNDMOV (1764)
 * Byte negamax alpha-beta search. */
static void ASCEND(void);

/* The negamax score table (SCORE) is byte-strided: one byte per ply, with two
 * dummy entries below it for plies -1 and 0.  "score 2 plies above" = [SCRIX],
 * "score 1 ply above" = [SCRIX+1]; FM30 reads the finished child at [SCRIX+2].
 *
 * The shared compare tail (Sargon's FM36/FM37) is factored into fm_update():
 *   returns 1 -> caller should ASCEND then continue (FM40 / beta cutoff),
 *   returns 0 -> caller should just continue (FM15). */
static int FNDMOV(void)
{
    int i;
    u8 A;
    u8 plymax_save = PLYMAX;        /* Sargon snapshots PLYMAX at entry (0x612) and
                                     * restores it at every exit (0x7a6); its sub
                                     * PLYMAX,2 on a root mate is dead code.  We
                                     * mirror that so PLYMAX never leaks across calls. */

    NPLY = 0;
    BESTM = 0;
    MLNXT = MLIST_OFF;
    MLPTRI = PLYIX_OFF - 2;                 /* PLYIX-2 */
    COLOR = KOLOR;
    SCRIX = SCORE_OFF;
    for (i = 0; i < (PLYMAX + 2); i++) wb(SCORE_OFF + i, 0);
    BC0 = 0; MV0 = 0;
    PINFND();
    POINTS();
    BC0 = BRDC;
    MV0 = MTRL;

FM5:
    NPLY++;
    MATEF = 0;
    GENMOV();
    if (NPLY < PLYMAX) SORTM();            /* Sargon CC SORTM = call only while NPLY<PLYMAX
                                            * (not at/after the terminal+extension ply) */
    MLPTRJ = MLPTRI;                        /* walker starts at the ply pair word */

FM15:
    {
        int link = rw(MLPTRJ);             /* next move pointer */
        if (link == 0) goto FM25;          /* end of move list */
        MLPTRJ = link;                     /* SDED MLPTRJ: current move = node */
        ww(MLPTRI, link);                  /* save in ply pointer list */
    }

    if (NPLY < PLYMAX) goto FM18;

    /* terminal ply: make move, test legality */
    MOVE();
    if (INCHK() != 0) { UNMOVE(); goto FM15; }
    if (NPLY != PLYMAX) goto FM35;         /* Sargon: LDA NPLY;CMP PLYMAX;JRNZ FM35 -
                                            * already past max (one check-extension used)
                                            * -> evaluate, do NOT extend again */
    {
        u8 opp = (u8)(COLOR ^ 0x80);
        if (INCHK1(opp) != 0) goto FM19;   /* opponent in check -> one more ply */
    }
    goto FM35;

FM18:
    if (rb(MLPTRJ + MLVAL) == 0) goto FM15;   /* illegal move (score 0) */
    MOVE();

FM19:
    COLOR ^= 0x80;
    if (!(COLOR & 0x80)) MOVENO++;
    wb(SCRIX + 2, rb(SCRIX));               /* score[ply+2] = score[ply] */
    SCRIX += 1;
    goto FM5;

FM25:
    if (MATEF != 0) goto FM30;
    if (CKFLG != 0) { PMATE = MOVENO; A = 0xFF; }   /* checkmate */
    else A = 0x80;                                  /* stalemate */
    MATEF |= 1;
    goto FM37;

FM30:
    if (NPLY == 1) { PLYMAX = plymax_save; return BESTM; }
    ASCEND();
    A = rb(SCRIX + 2);                      /* score of finished child subtree */
    goto FM37;

FM35:
    PINFND();
    POINTS();
    UNMOVE();
    A = VALM;
    MATEF |= 1;
    /* fall through to FM37 */

FM37:
    /* CMP M ; JRC FM40 ; JRZ FM40 : if A <= score 2 plies above -> beta cutoff */
    if (A <= rb(SCRIX)) { ASCEND(); goto FM15; }
    A = (u8)((0x100 - A) & 0xFF);          /* negate */
    /* INX H ; CMP M ; JC FM15 ; JZ FM15 : if A_neg <= score 1 ply above -> no gain */
    if (A <= rb(SCRIX + 1)) goto FM15;
    wb(SCRIX + 1, A);                      /* new best at this node */
    if (NPLY != 1) goto FM15;
    BESTM = MLPTRJ;
    if (rb(SCORE_OFF + 1) == 0xFF) {       /* SCORE+1: best score is a checkmate */
        if (PLYMAX >= 2) PLYMAX = (u8)(PLYMAX - 2);   /* dead in Sargon (restored below) */
        if (KOLOR & 0x80) { if (PMATE != 0) PMATE--; }
        PLYMAX = plymax_save;              /* Sargon's exit epilogue restores PLYMAX */
        return BESTM;                      /* and Sargon RETURNS on a root mate */
    }
    goto FM15;
}

/* ============================================================ ASCEND (1932) */
static void ASCEND(void)
{
    COLOR ^= 0x80;
    if (COLOR & 0x80) { if (MOVENO != 0) MOVENO--; }
    SCRIX -= 1;
    NPLY--;
    {
        /* MLPTRI points at this ply's pair CURRENT word.
         *   pair = [head, current]; head is at MLPTRI-2, the previous pair's
         *   current word is at MLPTRI-4.
         * Sargon:
         *   DCX H -> [MLPTRI-2] = head of this ply  -> restore MLNXT
         *   DCX H -> [MLPTRI-4] = previous current  -> restore MLPTRJ; MLPTRI=MLPTRI-4
         */
        int head_word = MLPTRI - 2;
        MLNXT = rw(head_word);
        MLPTRI = head_word - 2;
        MLPTRJ = rw(MLPTRI);
    }
    UNMOVE();
}

/* ============================================================ UCI front end */
static void sq_to_uci(u8 sq, char *out)
{
    int file = (sq % 10) - 1;
    int rank = (sq / 10) - 2;
    out[0] = (char)('a' + file);
    out[1] = (char)('1' + rank);
    out[2] = '\0';
}
static u8 uci_to_sq(char f, char r)
{
    int file = f - 'a';
    int rank = r - '1';
    return (u8)((rank + 2) * 10 + (file + 1));
}

/* Generate moves for COLOR into the first ply list; return the chain head node
 * offset (== [MLPTRI], the pair's current word, which ADMOVE chains from). */
static int gen_root_moves(void)
{
    MLNXT = MLIST_OFF;
    MLPTRI = PLYIX_OFF - 2;
    GENMOV();
    return rw(MLPTRI);
}

/* Persistent record holding the most recently played game move, so that ENPSNT
 * (which reads the previous move via MLPTRJ) can detect an en-passant capture at
 * the root.  Lives in a fixed mem[] slot below SCORE so move generation never
 * overwrites it.  For a double move (castling/en passant) the second half is
 * stored in the next 6 bytes so MOVE/UNMOVE's MV40/UM40 still work if ever needed. */
static void store_lastmove(int node)
{
    int i;
    for (i = 0; i < 6; i++) wb(LASTMV_OFF + i, rb(node + i));
    ww(LASTMV_OFF + MLPTR, 0);
    if (rb(node + MLFLG) & 0x40) {              /* double move: copy second half too */
        int second = node + 6;
        for (i = 0; i < 6; i++) wb(LASTMV_OFF + 6 + i, rb(second + i));
        ww(LASTMV_OFF + 6 + MLPTR, 0);
    }
}

/* Berg's Chess88 commits the OPPONENT's moves through a separate input routine
 * (not the search MOVE), and that routine does NOT set the "developed" bit when
 * the piece's FIRST move is a capture -- so such a piece is scored as still
 * undeveloped (PT6B / RQ penalty key off bit 3).  The engine's own moves go
 * through MOVE (develops unconditionally).  We reproduce it: an OPPONENT piece
 * (colour != side to move at the queried position) whose first move is a capture
 * keeps bit 3 clear.  Toggle with eval_c88 (Chess88 quirk set). */
static int apply_uci_move2(u8 from, u8 to, int promo, int is_opp)
{
    int node;
    int head;

    MLPTRJ = LASTMV_OFF;
    head = gen_root_moves();
    for (node = head; node != 0; node = rw(node + MLPTR)) {
        u8 mover, mtype;
        int was_first, is_cap;
        if (rb(node + MLFRP) != from) continue;
        if (rb(node + MLTOP) != to) continue;
        if (promo && !(rb(node + MLFLG) & 0x20)) continue;
        mover = board[from];
        mtype = (u8)(mover & 7);
        was_first = !(mover & 0x08);
        is_cap = (board[to] != 0);
        store_lastmove(node);
        MLPTRJ = node;
        MOVE();
        if (INCHK() != 0) { UNMOVE(); continue; }
        /* capture-developed quirk (Berg input path): opponent's first-move capture
         * stays undeveloped.  Disabled -- did not reproduce cleanly (broke G4.mv13);
         * kept behind a flag for future investigation. */
        if (eval_c88_capdev && is_opp && was_first && is_cap && mtype >= KNIGHT && mtype <= QUEEN)
            board[to] = (u8)(board[to] & ~0x08);
        COLOR ^= 0x80;
        if (!(COLOR & 0x80)) MOVENO++;
        MLPTRJ = LASTMV_OFF;
        return 1;
    }
    return 0;
}

static int apply_uci_move(u8 from, u8 to, int promo)
{
    return apply_uci_move2(from, to, promo, 0);
}

static void new_game(void)
{
    int i;
    INITBD();
    COLOR = WHITE;
    KOLOR = WHITE;
    MOVENO = 1;
    NPINS = 0;
    for (i = 0; i < 12; i++) wb(LASTMV_OFF + i, 0);   /* clear last-move record */
    MLPTRJ = LASTMV_OFF;
}

static void position_startpos(char *line)
{
    char *tok;
    new_game();
    tok = strtok(line, " \t\r\n");
    if (!tok) return;
    tok = strtok(NULL, " \t\r\n");
    if (!tok) return;
    if (strcmp(tok, "startpos") != 0) { /* only startpos supported */ }
    tok = strtok(NULL, " \t\r\n");
    if (!tok) return;
    if (strcmp(tok, "moves") != 0) return;
    {
        /* collect move tokens so we can know the final side to move; the piece
         * colour != that side is the "opponent" whose first-move captures stay
         * undeveloped (Berg input-path quirk). */
        static char *mvtok[1024];
        int nmv = 0, i;
        int final_white;
        while ((tok = strtok(NULL, " \t\r\n")) != NULL) {
            if (nmv < 1024) mvtok[nmv++] = tok;
        }
        final_white = (nmv % 2 == 0);   /* White to move after an even number of plies */
        for (i = 0; i < nmv; i++) {
            u8 from, to;
            int promo = 0, mover_white, is_opp;
            size_t len = strlen(mvtok[i]);
            if (len < 4) continue;
            from = uci_to_sq(mvtok[i][0], mvtok[i][1]);
            to   = uci_to_sq(mvtok[i][2], mvtok[i][3]);
            if (len >= 5 && (mvtok[i][4] == 'q' || mvtok[i][4] == 'Q' || mvtok[i][4] == 'r' ||
                             mvtok[i][4] == 'b' || mvtok[i][4] == 'n')) promo = 1;
            mover_white = (i % 2 == 0);
            is_opp = (mover_white != final_white);
            apply_uci_move2(from, to, promo, is_opp);
        }
    }
}

/* ============================================================ FEN setup
 * Lets SCID analyse ARBITRARY positions ("position fen ..."), not just
 * startpos+moves.  A FEN carries no move history, so the per-piece "moved" bit
 * (0x08, which drives Sargon's development scoring) is inferred: a piece off its
 * home square has moved; castling rights pin the kings/rooks down as un-moved;
 * the ep target square is turned back into a synthetic last move so ENPSNT fires. */
static void clear_moved_sq(int sq)
{
    if (board[sq] != 0xFF && board[sq] != 0) board[sq] = (u8)(board[sq] & ~0x08);
}

static void setup_fen(const char *placement, char stm,
                      const char *castle, const char *ep, int movno)
{
    int i, rank, file, sq;
    const char *p;

    for (i = 0; i < 120; i++) board[i] = 0xFF;             /* border */
    for (rank = 0; rank < 8; rank++)
        for (file = 0; file < 8; file++)
            board[21 + file + 10 * rank] = 0;              /* empty playable squares */
    posk[0] = posk[1] = posk[2] = posk[3] = 0; posk[4] = 0xFF;  /* 0 = skipped by PINFND */

    rank = 7; file = 0;                                    /* FEN lists rank 8 first */
    for (p = placement; *p && *p != ' '; p++) {
        char ch = *p, up;
        u8 color, type, piece;
        int home;
        if (ch == '/') { rank--; file = 0; continue; }
        if (ch >= '1' && ch <= '8') { file += (ch - '0'); continue; }
        color = (ch >= 'a' && ch <= 'z') ? BLACK : WHITE;
        up    = (ch >= 'a' && ch <= 'z') ? (char)(ch - 'a' + 'A') : ch;
        switch (up) {
            case 'P': type = PAWN;   break;  case 'N': type = KNIGHT; break;
            case 'B': type = BISHOP; break;  case 'R': type = ROOK;   break;
            case 'Q': type = QUEEN;  break;  case 'K': type = KING;   break;
            default:  continue;
        }
        if (rank < 0 || rank > 7 || file < 0 || file > 7) { file++; continue; }
        sq = 21 + file + 10 * rank;
        if (type == PAWN) home = (color == WHITE) ? (rank == 1) : (rank == 6);
        else { int br = (color == WHITE) ? 0 : 7; home = (rank == br && PIECES[file] == type); }
        piece = (u8)(type | color | (home ? 0 : 0x08));
        board[sq] = piece;
        if (type == KING)        posk[(color == WHITE) ? 0 : 1] = (u8)sq;
        else if (type == QUEEN) { int idx = (color == WHITE) ? 2 : 3;
                                  if (posk[idx] == 0) posk[idx] = (u8)sq; }   /* first queen */
        file++;
    }

    /* castling rights -> the named king and rook are on their home squares un-moved */
    if (castle && strchr(castle, 'K')) { clear_moved_sq(25); clear_moved_sq(28); }
    if (castle && strchr(castle, 'Q')) { clear_moved_sq(25); clear_moved_sq(21); }
    if (castle && strchr(castle, 'k')) { clear_moved_sq(95); clear_moved_sq(98); }
    if (castle && strchr(castle, 'q')) { clear_moved_sq(95); clear_moved_sq(91); }

    COLOR = (stm == 'b' || stm == 'B') ? BLACK : WHITE;
    KOLOR = COLOR;
    MOVENO = (movno >= 1 && movno <= 255) ? (u8)movno : 1;

    for (i = 0; i < 12; i++) wb(LASTMV_OFF + i, 0);
    if (ep && ep[0] >= 'a' && ep[0] <= 'h' && ep[1] >= '1' && ep[1] <= '8') {
        int er = ep[1] - '1', epsq = 21 + (ep[0] - 'a') + 10 * er, land = 0, frm = 0;
        if (er == 2)      { land = epsq + 10; frm = epsq - 10; }   /* a White pawn pushed */
        else if (er == 5) { land = epsq - 10; frm = epsq + 10; }   /* a Black pawn pushed */
        if (land) { wb(LASTMV_OFF + MLFRP, (u8)frm); wb(LASTMV_OFF + MLTOP, (u8)land);
                    wb(LASTMV_OFF + MLFLG, 0x10); }                /* "first move" marker */
    }
    MLPTRJ = LASTMV_OFF;
}

/* "position fen <placement> <stm> <castle> <ep> <half> <full> [moves ...]" */
static void position_fen(char *line)
{
    char *f = strstr(line, "fen");
    char placement[128] = "", stm[8] = "w", castle[8] = "-", ep[8] = "-";
    int half = 0, full = 1;
    char *moves;
    if (!f) { position_startpos(line); return; }
    sscanf(f + 3, "%127s %7s %7s %7s %d %d", placement, stm, castle, ep, &half, &full);
    setup_fen(placement, stm[0], castle, ep, full);
    moves = strstr(line, "moves");
    if (moves) {
        char *tok = strtok(moves + 5, " \t\r\n");
        while (tok) {
            if (strlen(tok) >= 4) {
                int promo = (strlen(tok) >= 5 && strchr("qrbnQRBN", tok[4]) != NULL);
                apply_uci_move(uci_to_sq(tok[0], tok[1]), uci_to_sq(tok[2], tok[3]), promo);
            }
            tok = strtok(NULL, " \t\r\n");
        }
    }
}

/* Accept true/on/yes/1 as "on" for check options, so the engine behaves whether a GUI
 * sends `setoption ... value true` or `value 1`. (Does NOT fix Scid's GUI-side config
 * crash, which is in Scid's own Tcl saveConfig, but makes the engine robust elsewhere.) */
static int uci_value_on(const char *p)
{
    char val[16] = "";
    const char *v = strstr(p, "value");
    if (!v) return 0;
    sscanf(v + 5, "%15s", val);
    return (strcmp(val, "true") == 0 || strcmp(val, "True") == 0 || strcmp(val, "TRUE") == 0 ||
            strcmp(val, "1") == 0 || strcmp(val, "on") == 0 || strcmp(val, "yes") == 0);
}

static void do_go(void)
{
    int best;
    char uci[6];

    if (random_first && COLOR == WHITE && MOVENO == 1) {
        static const u8 fr[4] = {35, 34, 22, 27};
        static const u8 to[4] = {55, 54, 43, 46};
        int k = rand() % 4;
        sq_to_uci(fr[k], uci);
        sq_to_uci(to[k], uci + 2);
        uci[4] = '\0';
        printf("bestmove %s\n", uci);
        fflush(stdout);
        return;
    }

    KOLOR = COLOR;
    MLPTRJ = LASTMV_OFF;           /* so the first GENMOV can see en passant */
    {
        clock_t t0 = clock();
        long ms, nps;
        int  raw, cp;
        g_nodes = 0;
        best = FNDMOV();
        ms = (long)((double)(clock() - t0) * 1000.0 / (double)CLOCKS_PER_SEC);
        if (best == 0) { printf("bestmove 0000\n"); fflush(stdout); return; }
        sq_to_uci(rb(best + MLFRP), uci);
        sq_to_uci(rb(best + MLTOP), uci + 2);
        uci[4] = '\0';
        if (rb(best + MLFLG) & 0x20) { uci[4] = 'q'; uci[5] = '\0'; }
        /* Sargon's backed-up root score (SCORE+1) is a 0x80-biased byte measuring the
         * IMPROVEMENT over the root position (baselines MV0/BC0).  For a conventional
         * absolute SCID score we add the root's static eval: 4*material + board-control
         * (MV0/BC0 are from White's view; flip for Black to move).  4 score-units ~= 1
         * pawn, so centipawns = total * 25, from the side-to-move's point of view. */
        raw = rb(SCORE_OFF + 1);
        {
            int rootw = 4 * (int)(s8)MV0 + (int)(s8)BC0;     /* root static, White's view */
            int stm   = (KOLOR & 0x80) ? -rootw : rootw;     /* from side-to-move          */
            cp = (stm + ((int)raw - 0x80)) * 25;
        }
        nps = (ms > 0) ? (g_nodes * 1000L / ms) : 0;
        printf("info depth %d score cp %d nodes %ld time %ld nps %ld pv %s\n",
               (int)PLYMAX, cp, g_nodes, ms, nps, uci);
        printf("bestmove %s\n", uci);
        fflush(stdout);
    }
}

int main(void)
{
    char line[8192];
    char copy[8192];

    /* Seed with per-process entropy so the random White first move varies even
     * across separate launches within the same wall-clock second (stack-address
     * ASLR + CPU clock + time).  Within one persistent process (the usual UCI
     * case) rand() simply advances each game. */
    srand((unsigned)time(NULL) ^ (unsigned)(uintptr_t)&line ^ (unsigned)clock());
    new_game();
    setvbuf(stdout, NULL, _IOLBF, 0);

    while (fgets(line, sizeof(line), stdin)) {
        strncpy(copy, line, sizeof(copy) - 1);
        copy[sizeof(copy) - 1] = '\0';

        if (strncmp(line, "uci", 3) == 0 &&
            (line[3] == '\n' || line[3] == '\r' || line[3] == ' ' || line[3] == '\0')) {
#ifdef STOCK_SARGON
            printf("id name Sargon 1978 (stock eval)\n");
#else
            printf("id name Chess88 (Berg 1988 port)\n");
#endif
            printf("id author Spracklen; port Berg; C translation\n");
            printf("option name Level type spin default 4 min 1 max 20\n");
            printf("option name Random type check default true\n");
            printf("option name StockSargon type check default false\n");
            printf("uciok\n");
            fflush(stdout);
        } else if (strncmp(line, "isready", 7) == 0) {
            printf("readyok\n");
            fflush(stdout);
        } else if (strncmp(line, "ucinewgame", 10) == 0) {
            new_game();
        } else if (strncmp(line, "position", 8) == 0) {
            if (strstr(copy, "fen")) position_fen(copy);
            else                     position_startpos(copy);
        } else if (strncmp(line, "setoption", 9) == 0) {
            char *p = strstr(copy, "name");
            if (p) {
                if (strstr(p, "Level")) {
                    char *v = strstr(p, "value");
                    if (v) {
                        int n = atoi(v + 5);
                        if (n < 1) n = 1;
                        if (n > MAXPLY) n = MAXPLY;
                        PLYMAX = (u8)n;
                    }
                } else if (strstr(p, "Sargon")) {   /* StockSargon=on -> disable ALL THREE Berg bugs */
                    if (strstr(p, "value")) { int stock = uci_value_on(p);
                        eval_c88 = stock ? 0 : 1; eval_c88_pin = stock ? 0 : 1;
                        eval_c88_dirty = stock ? 0 : 1; }
                } else if (strstr(p, "Random")) {
                    if (strstr(p, "value")) random_first = uci_value_on(p);
                }
            }
        } else if (strncmp(line, "go", 2) == 0) {
            char *d = strstr(copy, "depth");
            if (d) {
                int n = atoi(d + 5);
                if (n < 1) n = 1;
                if (n > MAXPLY) n = MAXPLY;
                PLYMAX = (u8)n;
            }
            do_go();
        } else if (strncmp(line, "quit", 4) == 0) {
            break;
        }
    }
    return 0;
}
