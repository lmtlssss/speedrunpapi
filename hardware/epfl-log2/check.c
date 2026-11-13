/* Checks the formula and the LUT netlist of this folder against the EPFL benchmark `log2` on every input.

   usage: check log2.aig log2_size_2027.blif tables.json [threads] [first_block last_block]

   log2.aig is the benchmark (binary AIGER, 32 inputs, 32 outputs). The program simulates it on all 2^32 input words,
   512 at a time, and compares two things with it:
     the formula below, computed in integer arithmetic with the four tables of tables.json;
     the netlist, read from the BLIF file and simulated LUT by LUT.
   It prints how many input words differ for each and returns 1 when either count is not zero.
   A block is 512 input words: inputs 0..5 run inside a 64-bit word, 6..8 over the eight words of a block, 9..31 are
   the block number. There are 2^23 blocks; first_block and last_block (exclusive) select a part of them.

   The formula, for the input word x, with A = x[30:23]:
     U   = (C2[A] + ((M2[A] * x) >> 32)) mod 2^40          read as two's complement
     V   = (C1[A] + ((U * x) >> 31)) mod 2^41              read as two's complement
     out = ((C0[A] + ((V * x) >> 31)) >> 4) mod 2^32
   where >> rounds toward minus infinity. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pthread.h>

#define BW 8                                   /* 64-bit words per block */
typedef unsigned __int128 u128;
typedef __int128 i128;

static void die(const char *msg, const char *arg) { fprintf(stderr, "%s %s\n", msg, arg ? arg : ""); exit(2); }

/* ------------------------------------------------------------------ benchmark: binary AIGER */
typedef struct { int ni, no, na; uint32_t *outs, *r0, *r1; } Aig;

static Aig load_aig(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) die("cannot open", path);
    Aig a; int m, l;
    if (fscanf(f, "aig %d %d %d %d %d\n", &m, &a.ni, &l, &a.no, &a.na) != 5 || l != 0) die("not a combinational binary AIGER file:", path);
    a.outs = malloc(sizeof(uint32_t) * a.no);
    for (int i = 0; i < a.no; i++) { unsigned v; if (fscanf(f, "%u\n", &v) != 1) die("bad output list in", path); a.outs[i] = v; }
    a.r0 = malloc(sizeof(uint32_t) * a.na); a.r1 = malloc(sizeof(uint32_t) * a.na);
    for (int k = 0; k < a.na; k++) {
        uint32_t d[2];
        for (int j = 0; j < 2; j++) {
            uint32_t v = 0; int s = 0, c;
            do { c = fgetc(f); if (c == EOF) die("truncated", path); v |= (uint32_t)(c & 127) << s; s += 7; } while (c & 128);
            d[j] = v;
        }
        uint32_t lhs = 2 * (uint32_t)(a.ni + k + 1);
        a.r0[k] = lhs - d[0]; a.r1[k] = a.r0[k] - d[1];
    }
    fclose(f);
    return a;
}

static void set_inputs(uint64_t *v, int ni, uint64_t block) {      /* v: value of input i at v + i * BW */
    static const uint64_t M[6] = { 0xAAAAAAAAAAAAAAAAULL, 0xCCCCCCCCCCCCCCCCULL, 0xF0F0F0F0F0F0F0F0ULL,
                                   0xFF00FF00FF00FF00ULL, 0xFFFF0000FFFF0000ULL, 0xFFFFFFFF00000000ULL };
    for (int i = 0; i < ni; i++) {
        uint64_t *p = v + (size_t)i * BW;
        for (int w = 0; w < BW; w++)
            p[w] = i < 6 ? M[i] : i < 9 ? (((w >> (i - 6)) & 1) ? ~0ULL : 0ULL) : (((block >> (i - 9)) & 1) ? ~0ULL : 0ULL);
    }
}

static void eval_aig(const Aig *g, uint64_t *v, uint64_t block) {  /* v: variable k at v + k * BW, variable 0 = false */
    memset(v, 0, sizeof(uint64_t) * BW);
    set_inputs(v + BW, g->ni, block);
    for (int k = 0; k < g->na; k++) {
        const uint64_t *x = v + (size_t)(g->r0[k] >> 1) * BW, *y = v + (size_t)(g->r1[k] >> 1) * BW;
        uint64_t mx = (g->r0[k] & 1) ? ~0ULL : 0ULL, my = (g->r1[k] & 1) ? ~0ULL : 0ULL;
        uint64_t *z = v + (size_t)(g->ni + 1 + k) * BW;
        for (int w = 0; w < BW; w++) z[w] = (x[w] ^ mx) & (y[w] ^ my);
    }
}

/* ------------------------------------------------------------------ netlist: BLIF with LUTs of at most 6 inputs */
typedef struct { int nin, in[6]; uint64_t tt; } Lut;
typedef struct { int ni, no, nl; Lut *lut; int *out; int *order; } Net;   /* signal ids: 0..ni-1 inputs, ni+k = LUT k */

typedef struct { char **key; int *val; int cap, n; } Map;
static uint64_t hash(const char *s) { uint64_t h = 1469598103934665603ULL; while (*s) { h ^= (unsigned char)*s++; h *= 1099511628211ULL; } return h; }
static int map_get(Map *m, const char *k, int add) {
    if (m->n * 2 >= m->cap) {
        int nc = m->cap ? m->cap * 2 : 1024; char **nk = calloc(nc, sizeof(char *)); int *nv = malloc(sizeof(int) * nc);
        for (int i = 0; i < m->cap; i++) if (m->key[i]) { uint64_t h = hash(m->key[i]) % nc; while (nk[h]) h = (h + 1) % nc; nk[h] = m->key[i]; nv[h] = m->val[i]; }
        free(m->key); free(m->val); m->key = nk; m->val = nv; m->cap = nc;
    }
    uint64_t h = hash(k) % m->cap;
    while (m->key[h]) { if (!strcmp(m->key[h], k)) return m->val[h]; h = (h + 1) % m->cap; }
    if (!add) return -1;
    m->key[h] = strdup(k); m->val[h] = m->n;
    return m->n++;
}

static char *read_logical_line(FILE *f) {       /* joins lines that end with a backslash; NULL at end of file */
    static char *buf; static size_t cap;
    size_t n = 0; int c, any = 0;
    for (;;) {
        c = fgetc(f);
        if (c == EOF) break;
        any = 1;
        if (c == '\n') { if (n && buf[n - 1] == '\\') { n--; continue; } break; }
        if (n + 2 > cap) { cap = cap ? cap * 2 : 4096; buf = realloc(buf, cap); }
        buf[n++] = (char)c;
    }
    if (!any) return NULL;
    if (n + 1 > cap) { cap = n + 16; buf = realloc(buf, cap); }
    buf[n] = 0;
    return buf;
}

static Net load_blif(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) die("cannot open", path);
    Map names = {0};
    int cap = 1 << 16, nl = 0, ni = 0, no = 0;
    int *lut_sig = malloc(sizeof(int) * cap); Lut *lut = malloc(sizeof(Lut) * cap);
    int *in_sig = malloc(sizeof(int) * 64), *out_sig = malloc(sizeof(int) * 4096);
    int cur = -1, saw_row = 0, offset = 0;
    char *line;
    while ((line = read_logical_line(f))) {
        char *tok[80]; int nt = 0;
        for (char *p = strtok(line, " \t\r"); p && nt < 80; p = strtok(NULL, " \t\r")) tok[nt++] = p;
        if (!nt || tok[0][0] == '#') continue;
        if (tok[0][0] == '.') {
            if (cur >= 0 && offset) lut[cur].tt = ~lut[cur].tt & (lut[cur].nin == 6 ? ~0ULL : ((1ULL << (1 << lut[cur].nin)) - 1));
            cur = -1;
            if (!strcmp(tok[0], ".inputs")) for (int i = 1; i < nt; i++) in_sig[ni++] = map_get(&names, tok[i], 1);
            else if (!strcmp(tok[0], ".outputs")) for (int i = 1; i < nt; i++) out_sig[no++] = map_get(&names, tok[i], 1);
            else if (!strcmp(tok[0], ".names")) {
                if (nt - 2 > 6) die("a LUT has more than six inputs in", path);
                if (nl == cap) { cap *= 2; lut = realloc(lut, sizeof(Lut) * cap); lut_sig = realloc(lut_sig, sizeof(int) * cap); }
                cur = nl++; lut[cur].nin = nt - 2; lut[cur].tt = 0; saw_row = 0; offset = 0;
                for (int i = 0; i < nt - 2; i++) lut[cur].in[i] = map_get(&names, tok[i + 1], 1);
                lut_sig[cur] = map_get(&names, tok[nt - 1], 1);
            } else if (strcmp(tok[0], ".model") && strcmp(tok[0], ".end")) die("unsupported BLIF line", tok[0]);
            continue;
        }
        if (cur < 0) die("cover row outside a .names block in", path);
        const char *pat = nt == 2 ? tok[0] : "", *val = tok[nt - 1];
        if ((int)strlen(pat) != lut[cur].nin) die("cover row of the wrong width in", path);
        if (saw_row && (val[0] == '0') != offset) die("mixed on-set and off-set rows in", path);
        saw_row = 1; offset = val[0] == '0';
        for (int r = 0; r < (1 << lut[cur].nin); r++) {
            int hit = 1;
            for (int i = 0; i < lut[cur].nin; i++) if (pat[i] != '-' && (pat[i] == '1') != ((r >> i) & 1)) hit = 0;
            if (hit) lut[cur].tt |= 1ULL << r;
        }
    }
    if (cur >= 0 && offset) lut[cur].tt = ~lut[cur].tt & (lut[cur].nin == 6 ? ~0ULL : ((1ULL << (1 << lut[cur].nin)) - 1));
    fclose(f);
    /* name ids -> signal ids */
    int *sig = malloc(sizeof(int) * names.n);
    for (int i = 0; i < names.n; i++) sig[i] = -1;
    for (int i = 0; i < ni; i++) sig[in_sig[i]] = i;
    for (int k = 0; k < nl; k++) { if (sig[lut_sig[k]] != -1) die("a signal is driven twice in", path); sig[lut_sig[k]] = ni + k; }
    Net n; n.ni = ni; n.no = no; n.nl = nl; n.lut = lut; n.out = malloc(sizeof(int) * no); n.order = malloc(sizeof(int) * nl);
    for (int k = 0; k < nl; k++) for (int i = 0; i < lut[k].nin; i++) { if (sig[lut[k].in[i]] < 0) die("undriven signal in", path); lut[k].in[i] = sig[lut[k].in[i]]; }
    for (int i = 0; i < no; i++) { if (sig[out_sig[i]] < 0) die("undriven output in", path); n.out[i] = sig[out_sig[i]]; }
    /* topological order */
    char *state = calloc(nl, 1); int *stack = malloc(sizeof(int) * (nl + 1)), sp, cnt = 0;
    for (int root = 0; root < nl; root++) {
        if (state[root]) continue;
        sp = 0; stack[sp++] = root;
        while (sp) {
            int k = stack[sp - 1], pushed = 0;
            if (state[k] == 2) { sp--; continue; }
            state[k] = 1;
            for (int i = 0; i < lut[k].nin; i++) {
                int s = lut[k].in[i] - ni;
                if (s >= 0 && state[s] != 2) { if (state[s] == 1) die("combinational loop in", path); stack[sp++] = s; pushed = 1; break; }
            }
            if (!pushed) { state[k] = 2; n.order[cnt++] = k; sp--; }
        }
    }
    return n;
}

/* a LUT is evaluated by splitting on its inputs from the last to the first; equal halves are computed once */
static void eval_tt(uint64_t tt, int nv, uint64_t *const *in, uint64_t *out, uint64_t *scratch) {
    uint64_t full = nv == 6 ? ~0ULL : ((1ULL << (1 << nv)) - 1);
    tt &= full;
    if (tt == 0) { for (int w = 0; w < BW; w++) out[w] = 0; return; }
    if (tt == full) { for (int w = 0; w < BW; w++) out[w] = ~0ULL; return; }
    int h = 1 << (nv - 1);
    uint64_t lo = tt & ((1ULL << h) - 1), hi = tt >> h, half = (1ULL << h) - 1;
    const uint64_t *s = in[nv - 1];
    if (lo == hi) { eval_tt(lo, nv - 1, in, out, scratch); return; }
    if (lo == 0 && hi == half) { for (int w = 0; w < BW; w++) out[w] = s[w]; return; }
    if (lo == half && hi == 0) { for (int w = 0; w < BW; w++) out[w] = ~s[w]; return; }
    if (hi == (~lo & half)) {                                   /* complementary halves: one half xor the input */
        eval_tt(lo, nv - 1, in, out, scratch);
        for (int w = 0; w < BW; w++) out[w] ^= s[w];
        return;
    }
    uint64_t *a = scratch;                                       /* value of the half with the input at 1 */
    eval_tt(hi, nv - 1, in, a, scratch + BW);
    eval_tt(lo, nv - 1, in, out, scratch + BW);
    for (int w = 0; w < BW; w++) out[w] ^= s[w] & (a[w] ^ out[w]);
}

static void eval_net(const Net *n, uint64_t *v, uint64_t block) {  /* v: signal k at v + k * BW */
    uint64_t scratch[8 * BW], *in[6];
    set_inputs(v, n->ni, block);
    for (int t = 0; t < n->nl; t++) {
        const Lut *l = &n->lut[n->order[t]];
        for (int i = 0; i < l->nin; i++) in[i] = v + (size_t)l->in[i] * BW;
        eval_tt(l->tt, l->nin, in, v + (size_t)(n->ni + n->order[t]) * BW, scratch);
    }
}

/* ------------------------------------------------------------------ formula */
static uint64_t M2[256], C2[256], C1[256], C0[256];

static void load_tables(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) die("cannot open", path);
    fseek(f, 0, SEEK_END); long len = ftell(f); fseek(f, 0, SEEK_SET);
    char *s = malloc(len + 1);
    if (fread(s, 1, len, f) != (size_t)len) die("cannot read", path);
    s[len] = 0; fclose(f);
    const char *keys[4] = { "\"M2\"", "\"C2\"", "\"C1\"", "\"C0\"" };
    uint64_t *dst[4] = { M2, C2, C1, C0 };
    for (int k = 0; k < 4; k++) {
        char *p = s;
        for (;;) {                                               /* the key, a colon, an opening bracket */
            p = strstr(p, keys[k]);
            if (!p) die("missing table", keys[k]);
            p += strlen(keys[k]);
            char *q = p;
            while (*q == ' ' || *q == '\t' || *q == '\n' || *q == '\r') q++;
            if (*q != ':') continue;
            q++;
            while (*q == ' ' || *q == '\t' || *q == '\n' || *q == '\r') q++;
            if (*q == '[') { p = q; break; }
        }
        for (int i = 0; i < 256; i++) {
            while (*p && (*p < '0' || *p > '9')) { if (*p == ']') die("short table", keys[k]); p++; }
            dst[k][i] = strtoull(p, &p, 10);
        }
    }
    free(s);
}

static uint32_t formula(uint32_t x) {
    unsigned A = (x >> 23) & 255;
    int64_t U = (int64_t)((C2[A] + (uint64_t)(((u128)M2[A] * x) >> 32)) & ((1ULL << 40) - 1));
    if (U >> 39) U -= (int64_t)1 << 40;
    int64_t V = (int64_t)(((u128)C1[A] + (u128)(((i128)U * x) >> 31)) & ((1ULL << 41) - 1));
    if (V >> 40) V -= (int64_t)1 << 41;
    return (uint32_t)((((u128)C0[A] + (u128)(((i128)V * x) >> 31)) >> 4) & 0xFFFFFFFFu);
}

/* ------------------------------------------------------------------ comparison */
typedef struct { const Aig *a; const Net *n; uint64_t lo, hi, bad_formula, bad_net, first_formula, first_net; int hf, hn; } Job;

static void *work(void *arg) {
    Job *j = arg;
    uint64_t *va = malloc(sizeof(uint64_t) * BW * (size_t)(j->a->ni + j->a->na + 1));
    uint64_t *vn = malloc(sizeof(uint64_t) * BW * (size_t)(j->n->ni + j->n->nl));
    for (uint64_t blk = j->lo; blk < j->hi; blk++) {
        eval_aig(j->a, va, blk);
        eval_net(j->n, vn, blk);
        uint64_t dn[BW], df[BW], fo[32][BW];
        memset(dn, 0, sizeof dn); memset(df, 0, sizeof df); memset(fo, 0, sizeof fo);
        for (int w = 0; w < BW; w++)
            for (int b = 0; b < 64; b++) {
                uint32_t val = formula((uint32_t)((blk << 9) | ((uint64_t)w << 6) | (uint64_t)b));
                for (int o = 0; val; o++, val >>= 1) if (val & 1) fo[o][w] |= 1ULL << b;
            }
        for (int o = 0; o < j->a->no; o++) {
            const uint64_t *r = va + (size_t)(j->a->outs[o] >> 1) * BW, *y = vn + (size_t)j->n->out[o] * BW;
            uint64_t m = (j->a->outs[o] & 1) ? ~0ULL : 0ULL;
            for (int w = 0; w < BW; w++) { dn[w] |= r[w] ^ m ^ y[w]; df[w] |= r[w] ^ m ^ fo[o][w]; }
        }
        for (int w = 0; w < BW; w++) {
            if (dn[w]) { j->bad_net += (uint64_t)__builtin_popcountll(dn[w]); if (!j->hn) { j->hn = 1; j->first_net = (blk << 9) | ((uint64_t)w << 6) | (uint64_t)__builtin_ctzll(dn[w]); } }
            if (df[w]) { j->bad_formula += (uint64_t)__builtin_popcountll(df[w]); if (!j->hf) { j->hf = 1; j->first_formula = (blk << 9) | ((uint64_t)w << 6) | (uint64_t)__builtin_ctzll(df[w]); } }
        }
    }
    free(va); free(vn);
    return NULL;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: check log2.aig netlist.blif tables.json [threads] [first_block last_block]\n"); return 2; }
    Aig a = load_aig(argv[1]);
    Net n = load_blif(argv[2]);
    load_tables(argv[3]);
    if (a.ni != 32 || a.no != 32 || n.ni != 32 || n.no != 32) die("both circuits must have 32 inputs and 32 outputs", NULL);
    int T = argc > 4 ? atoi(argv[4]) : 4;
    if (T < 1 || T > 64) T = 4;
    uint64_t blocks = 1ULL << (32 - 9), lo = 0, hi = blocks;
    if (argc > 6) { lo = strtoull(argv[5], 0, 10); hi = strtoull(argv[6], 0, 10); }
    if (hi > blocks || lo > hi) die("block range outside 0 ..", "8388608");
    int big = 0;
    for (int k = 0; k < n.nl; k++) if (n.lut[k].nin > big) big = n.lut[k].nin;
    pthread_t th[64]; Job jobs[64];
    for (int t = 0; t < T; t++) {
        jobs[t] = (Job){ &a, &n, lo + (hi - lo) * t / T, lo + (hi - lo) * (t + 1) / T, 0, 0, 0, 0, 0, 0 };
        pthread_create(&th[t], NULL, work, &jobs[t]);
    }
    uint64_t bf = 0, bn = 0, ff = 0, fn = 0; int hf = 0, hn = 0;
    for (int t = 0; t < T; t++) {
        pthread_join(th[t], NULL);
        bf += jobs[t].bad_formula; bn += jobs[t].bad_net;
        if (jobs[t].hf && (!hf || jobs[t].first_formula < ff)) { hf = 1; ff = jobs[t].first_formula; }
        if (jobs[t].hn && (!hn || jobs[t].first_net < fn)) { hn = 1; fn = jobs[t].first_net; }
    }
    printf("benchmark: %d AND nodes. netlist: %d LUTs, at most %d inputs each.\n", a.na, n.nl, big);
    printf("input words 0x%08llx to 0x%08llx (%llu words)\n", (unsigned long long)(lo << 9), (unsigned long long)((hi << 9) - 1), (unsigned long long)((hi - lo) << 9));
    printf("formula against benchmark: %llu differ", (unsigned long long)bf);
    if (hf) printf(", first at 0x%08llx", (unsigned long long)ff);
    printf("\nnetlist against benchmark: %llu differ", (unsigned long long)bn);
    if (hn) printf(", first at 0x%08llx", (unsigned long long)fn);
    printf("\n");
    return (bf || bn) ? 1 : 0;
}
