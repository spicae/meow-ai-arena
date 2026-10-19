// Land bot (territory game): loop-planner with enemy-arrival safety model,
// opportunistic trail cutting, and a time budget to avoid per-turn timeouts.
// Handles both 1v1 (N=2) and 4-player melee (N=4) from the INIT line.
#include <bits/stdc++.h>
using namespace std;

const int DX[4] = {0, 0, -1, 1};
const int DY[4] = {-1, 1, 0, 0};
const char DC[4] = {'U', 'D', 'L', 'R'};
const int INF = 1e9;
const int MAXC = 48 * 48;

int W, H, MAX_TURNS, N, ME, MOVE_MS, INIT_MS;
int spx[4], spy[4];
int own[MAXC], trl[MAXC], prot[MAXC];
struct Player { int x, y, dir, tl, area, deaths; } pl[4];
int turnNo;

// per-turn data
int deMin[MAXC];           // min over enemies of BFS steps to reach a cell
int deE[4][MAXC];          // enemy e steps to each cell (INF if unreachable)
int hd[MAXC];              // steps to nearest own territory (avoiding my trail)
vector<int> myTrail;

chrono::steady_clock::time_point t0;
double elapsedMs() { return chrono::duration<double, milli>(chrono::steady_clock::now() - t0).count(); }

int dirIndex(char c) { return string("UDLR").find(c); }
inline bool inb(int x, int y) { return x >= 0 && x < W && y >= 0 && y < H; }

static int qbuf[MAXC];
// BFS from (sx,sy) heading dir; cannot reverse on the first step.
// Cells with trl==blockOwner are walls. dist[start]=0.
void bfsFrom(int sx, int sy, int dir, int blockOwner, int* dist) {
    for (int i = 0; i < W * H; i++) dist[i] = INF;
    int qh = 0, qt = 0;
    int s = sy * W + sx;
    dist[s] = 0;
    for (int d = 0; d < 4; d++) {
        if (d == (dir ^ 1)) continue;
        int nx = sx + DX[d], ny = sy + DY[d];
        if (!inb(nx, ny)) continue;
        int k = ny * W + nx;
        if (trl[k] == blockOwner || dist[k] != INF) continue;
        dist[k] = 1;
        qbuf[qt++] = k;
    }
    while (qh < qt) {
        int k = qbuf[qh++];
        int x = k % W, y = k / W;
        for (int d = 0; d < 4; d++) {
            int nx = x + DX[d], ny = y + DY[d];
            if (!inb(nx, ny)) continue;
            int nk = ny * W + nx;
            if (trl[nk] == blockOwner || dist[nk] != INF) continue;
            dist[nk] = dist[k] + 1;
            qbuf[qt++] = nk;
        }
    }
}

// ---------- path simulation ----------
struct Sim {
    int n, L;          // n = steps walked, L = closure length
    bool cap;          // closed a loop
    int cells[300];    // non-territory cells visited (new trail)
    int nt;
};
static int visStamp[MAXC];
static int stampCtr = 0;

// Walk the legs (dir + len; len<0 means "until captured"), return false if it hits
// a wall, my trail, an already visited cell, or the step count exceeds the budget.
bool simulate(const int* dirs, const int* lens, int nl, Sim& s, int maxSteps) {
    stampCtr++;
    int x = pl[ME].x, y = pl[ME].y;
    bool hasTrail = pl[ME].tl > 0;
    s.n = 0; s.nt = 0; s.cap = false;
    bool first = true;
    for (int li = 0; li < nl; li++) {
        int d = dirs[li];
        int len = lens[li];
        int cnt = 0;
        int lim = len < 0 ? maxSteps : len;
        while (cnt < lim) {
            if (first && d == (pl[ME].dir ^ 1)) return false;
            first = false;
            x += DX[d]; y += DY[d];
            if (!inb(x, y)) return false;
            int k = y * W + x;
            if (trl[k] == ME || visStamp[k] == stampCtr) return false;
            if (s.n >= maxSteps) return false;
            s.cells[s.n++] = k;
            cnt++;
            if (own[k] == ME) {
                if (hasTrail) { s.cap = true; s.L = s.n; return true; }
            } else {
                visStamp[k] = stampCtr;
                s.nt = s.n;
                hasTrail = true;
            }
        }
    }
    s.L = s.n;
    return false;
}

// ---------- gain evaluation (exact flood fill, per-cell) ----------
// Gain = new cells that become mine when the loop closes:
//   the new trail cells plus any neutral/enemy cells enclosed by
//   (my territory + trail) as walls (flood from the border).
double constGain;          // value of my existing trail cells
double EW;                 // weight of enemy territory vs neutral

inline double cellVal(int k) {
    if (prot[k] != -1 && prot[k] != ME) return 0;
    if (own[k] == ME) return 0;
    return own[k] == -1 ? 1.0 : EW;
}

double exactGain(const Sim& s) {
    // wall = my territory | my trail | cells this loop walks over (s.cells[0..s.nt))
    static int seen[MAXC];
    static int bq[MAXC];
    static int loopStamp[MAXC];  // marks cells of the current loop as walls
    static int loopCtr = 0;
    loopCtr++;
    for (int i = 0; i < s.nt; i++) loopStamp[s.cells[i]] = loopCtr;
    auto wall = [&](int k) {
        if (own[k] == ME) return true;
        if (trl[k] == ME) return true;
        return loopStamp[k] == loopCtr;
    };
    double g = constGain;
    int qh = 0, qt = 0;
    for (int x = 0; x < W; x++) {
        for (int y : {0, H - 1}) {
            int k = y * W + x;
            if (!wall(k) && seen[k] != loopCtr) { seen[k] = loopCtr; bq[qt++] = k; }
        }
    }
    for (int y = 0; y < H; y++) {
        for (int x : {0, W - 1}) {
            int k = y * W + x;
            if (!wall(k) && seen[k] != loopCtr) { seen[k] = loopCtr; bq[qt++] = k; }
        }
    }
    while (qh < qt) {
        int u = bq[qh++];
        int x = u % W, y = u / W;
        for (int d = 0; d < 4; d++) {
            int nx = x + DX[d], ny = y + DY[d];
            if (!inb(nx, ny)) continue;
            int nk = ny * W + nx;
            if (!wall(nk) && seen[nk] != loopCtr) { seen[nk] = loopCtr; bq[qt++] = nk; }
        }
    }
    for (int i = 0; i < s.nt; i++) g += cellVal(s.cells[i]);
    for (int k = 0; k < W * H; k++) {
        if (wall(k) || seen[k] == loopCtr) continue;
        g += cellVal(k);
    }
    return g;
}

// ---------- candidate enumeration ----------
struct Cand { double est; int dirs[4]; int lens[4]; int nl; int L; };

// safety: every trail cell (existing + planned) must be at least `margin`
// steps away from every enemy, until the loop closes (L steps).
bool pathSafe(const Sim& s, int margin) {
    int L = s.L;
    for (int k : myTrail)
        if (deMin[k] <= L + margin) return false;
    for (int i = 0; i < s.nt; i++)
        if (deMin[s.cells[i]] <= L + margin) return false;
    return true;
}

// ---- head-on avoidance ----
// If I move to cell k this turn, would I crash into an enemy?
// (a) an enemy whose current position equals k (I step onto its head -> head-on);
// (b) an enemy that also moves into k this turn (same target cell);
// (c) an enemy that swaps cells with me (we step onto each other's current cell).
bool willHeadOn(int k) {
    int mx = k % W, my = k / W;
    for (int e = 0; e < N; e++) {
        if (e == ME) continue;
        if (pl[e].tl == 0) continue;  // just respawned or eliminated: don't overreact
        int ex = pl[e].x, ey = pl[e].y;
        // (a) I step onto enemy's current head
        if (ex == mx && ey == my) return true;
        // (c) swap: enemy steps onto my current cell while I step onto its current cell
        int eo = pl[e].dir;
        int enx = ex + DX[eo], eny = ey + DY[eo];
        if (enx == pl[ME].x && eny == pl[ME].y && mx == ex && my == ey) return true;
        // (b) enemy steps into the same target cell this turn
        if (enx == mx && eny == my) return true;
    }
    return false;
}

// pick the move that stays inside own territory as long as possible (depth-limited)
int stayInside() {
    const Player& me = pl[ME];
    int bestD = -1, bestScore = -1;
    for (int d = 0; d < 4; d++) {
        if (d == (me.dir ^ 1)) continue;
        int nx = me.x + DX[d], ny = me.y + DY[d];
        if (!inb(nx, ny) || trl[ny * W + nx] == ME) continue;
        int score = 0;
        if (own[ny * W + nx] == ME) {
            score = 1;
            function<int(int, int, int, int)> go = [&](int x, int y, int dir, int depth) -> int {
                if (depth == 0) return 0;
                int best = 0;
                for (int e = 0; e < 4; e++) {
                    if (e == (dir ^ 1)) continue;
                    int ax = x + DX[e], ay = y + DY[e];
                    if (!inb(ax, ay) || own[ay * W + ax] != ME) continue;
                    best = max(best, 1 + go(ax, ay, e, depth - 1));
                }
                return best;
            };
            score += go(nx, ny, d, 6);
        }
        if (score > bestScore) { bestScore = score; bestD = d; }
    }
    return bestD;
}

int decide() {
    t0 = chrono::steady_clock::now();
    const Player& me = pl[ME];
    int WH = W * H;
    int remaining = MAX_TURNS - turnNo;
    bool melee = (N != 2);
    int maxL = min(remaining, melee ? 40 : 60);  // shorter loops in melee: less to defend

    // enemy distance maps (BFS ignoring walls; an enemy's own trail is its wall)
    for (int k = 0; k < WH; k++) deMin[k] = INF;
    for (int e = 0; e < N; e++) {
        if (e == ME) continue;
        bfsFrom(pl[e].x, pl[e].y, pl[e].dir, e, deE[e]);
        for (int k = 0; k < WH; k++) deMin[k] = min(deMin[k], deE[e][k]);
    }
    myTrail.clear();
    for (int k = 0; k < WH; k++) if (trl[k] == ME) myTrail.push_back(k);
    constGain = 0;
    for (int k : myTrail) constGain += cellVal(k);

    // distance to own territory (avoiding my trail) for the "go home" fallback
    {
        int qh = 0, qt = 0;
        for (int k = 0; k < WH; k++) { hd[k] = INF; if (own[k] == ME) { hd[k] = 0; qbuf[qt++] = k; } }
        while (qh < qt) {
            int k = qbuf[qh++];
            int x = k % W, y = k / W;
            for (int d = 0; d < 4; d++) {
                int nx = x + DX[d], ny = y + DY[d];
                if (!inb(nx, ny)) continue;
                int nk = ny * W + nx;
                if (trl[nk] == ME || hd[nk] != INF) continue;
                hd[nk] = hd[k] + 1;
                qbuf[qt++] = nk;
            }
        }
    }

    // time budget: generous on turn 0, otherwise ~60% of the 50ms
    double budget = (turnNo == 0) ? 1200.0 : (MOVE_MS * 0.6);
    int margin = melee ? 2 : 0;  // melee needs extra safety: more enemies can cut the loop

    double bestRate = -1;
    int bestDir = -1;
    Cand bestC; bestC.nl = 0;
    // head-on penalty: prefer a candidate whose first step does not crash
    auto firstStepCell = [&](int d) { return (pl[ME].y + DY[d]) * W + (pl[ME].x + DX[d]); };

    Sim s;
    // ---- loop candidates: 2-leg (go out, turn, until captured) and
    //      3-leg (go out, turn, go back parallel, until captured) rectangles ----
    int A = 26, B = 18;
    for (int d1 = 0; d1 < 4 && elapsedMs() < budget; d1++) {
        if (d1 == (me.dir ^ 1)) continue;
        for (int a = 1; a <= A && elapsedMs() < budget; a++) {
            for (int si = 0; si < 2; si++) {
                int sd = (d1 < 2 ? 2 : 0) + si;
                // 2-leg
                {
                    int dirs[2] = {d1, sd}, lens[2] = {a, -1};
                    if (simulate(dirs, lens, 2, s, maxL) && s.cap && s.L <= maxL && pathSafe(s, margin)) {
                        double g = exactGain(s);
                        double rate = g / (s.L + 20.0);
                        if (willHeadOn(firstStepCell(d1))) rate -= 1e6;  // never pick a suicidal first step
                        if (rate > bestRate) {
                            bestRate = rate; bestDir = d1;
                            bestC.nl = 2; bestC.dirs[0] = d1; bestC.lens[0] = a;
                            bestC.dirs[1] = sd; bestC.lens[1] = -1; bestC.L = s.L;
                        }
                    }
                }
                // 3-leg
                for (int b = 1; b <= B && elapsedMs() < budget; b++) {
                    int dirs[3] = {d1, sd, d1 ^ 1}, lens[3] = {a, b, -1};
                    if (simulate(dirs, lens, 3, s, maxL) && s.cap && s.L <= maxL && pathSafe(s, margin)) {
                        double g = exactGain(s);
                        double rate = g / (s.L + 20.0);
                        if (willHeadOn(firstStepCell(d1))) rate -= 1e6;
                        if (rate > bestRate) {
                            bestRate = rate; bestDir = d1;
                            bestC.nl = 3; bestC.dirs[0] = d1; bestC.lens[0] = a;
                            bestC.dirs[1] = sd; bestC.lens[1] = b;
                            bestC.dirs[2] = d1 ^ 1; bestC.lens[2] = -1; bestC.L = s.L;
                        }
                    }
                }
            }
        }
    }

    // ---- attack: go cut an enemy's trail if it is closer than its owner can defend ----
    if (me.tl > 0) {
        static int dm[MAXC], par[MAXC];
        for (int k = 0; k < WH; k++) dm[k] = INF;
        int qh = 0, qt = 0;
        int st = me.y * W + me.x;
        dm[st] = 0;
        for (int d = 0; d < 4; d++) {
            if (d == (me.dir ^ 1)) continue;
            int nx = me.x + DX[d], ny = me.y + DY[d];
            if (!inb(nx, ny)) continue;
            int k = ny * W + nx;
            if (trl[k] == ME || dm[k] != INF) continue;
            dm[k] = 1; par[k] = d; qbuf[qt++] = k;
        }
        while (qh < qt) {
            int k = qbuf[qh++];
            int x = k % W, y = k / W;
            for (int d = 0; d < 4; d++) {
                int nx = x + DX[d], ny = y + DY[d];
                if (!inb(nx, ny)) continue;
                int nk = ny * W + nx;
                if (trl[nk] == ME || dm[nk] != INF) continue;
                dm[nk] = dm[k] + 1; par[nk] = d; qbuf[qt++] = nk;
            }
        }
        for (int e = 0; e < N; e++) {
            if (e == ME || pl[e].tl == 0) continue;
            int bk = -1, bd = INF;
            for (int k = 0; k < WH; k++)
                if (trl[k] == e && dm[k] < bd) { bd = dm[k]; bk = k; }
            if (bk < 0 || bd > maxL) continue;
            // how far the enemy's own trail is from its head: it defends its trail
            int ehome = INF;
            for (int k = 0; k < WH; k++) if (own[k] == e) ehome = min(ehome, deE[e][k]);
            if (bd > ehome + 2) continue;
            // the enemy must not be able to reach any of my trail cells before I finish
            bool safe = true;
            for (int k : myTrail)
                if (deMin[k] <= bd + 2) { safe = false; break; }
            if (!safe) continue;
            // other enemies must not punish the chase
            int other = INF;
            for (int k = 0; k < N; k++)
                if (k != ME && k != e && deE[k][bk] < other) other = deE[k][bk];
            if (other <= bd + 2) continue;
            double V = 6.0 + 1.5 * pl[e].tl;
            double rate = V / (bd + 2.0);
            if (willHeadOn(firstStepCell(par[bk]))) rate -= 1e6;
            if (rate > bestRate) {
                bestRate = rate; bestDir = par[bk];
                bestC.nl = 0; bestC.L = bd;
            }
        }
    }

    if (bestDir >= 0) return bestDir;

    // ---- fallbacks ----
    if (me.tl == 0) {
        int d = stayInside();
        if (d >= 0) return d;
    }
    // go home by the shortest safe path
    {
        static int dist[MAXC];
        for (int k = 0; k < WH; k++) dist[k] = INF;
        int qh = 0, qt = 0;
        for (int k = 0; k < WH; k++) if (own[k] == ME) { dist[k] = 0; qbuf[qt++] = k; }
        while (qh < qt) {
            int k = qbuf[qh++];
            int x = k % W, y = k / W;
            for (int d = 0; d < 4; d++) {
                int nx = x + DX[d], ny = y + DY[d];
                if (!inb(nx, ny)) continue;
                int nk = ny * W + nx;
                if (trl[nk] == ME || dist[nk] != INF) continue;
                dist[nk] = dist[k] + 1;
                qbuf[qt++] = nk;
            }
        }
        int bd = -1, bv = INF;
        for (int d = 0; d < 4; d++) {
            if (d == (me.dir ^ 1)) continue;
            int nx = me.x + DX[d], ny = me.y + DY[d];
            if (!inb(nx, ny) || trl[ny * W + nx] == ME) continue;
            if (willHeadOn(ny * W + nx)) continue;  // don't go home through a head-on
            int v = dist[ny * W + nx];
            if (v < bv) { bv = v; bd = d; }
        }
        if (bd >= 0) return bd;
    }
    for (int d = 0; d < 4; d++) {
        if (d == (me.dir ^ 1)) continue;
        int nx = me.x + DX[d], ny = me.y + DY[d];
        if (inb(nx, ny) && !willHeadOn(ny * W + nx)) return d;
    }
    for (int d = 0; d < 4; d++) {
        if (d == (me.dir ^ 1)) continue;
        int nx = me.x + DX[d], ny = me.y + DY[d];
        if (inb(nx, ny)) return d;
    }
    return me.dir;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    string tok;
    cin >> tok;
    cin >> W >> H >> MAX_TURNS >> N >> ME >> MOVE_MS >> INIT_MS;
    for (int i = 0; i < N; i++) {
        int id, x, y;
        cin >> tok >> id >> x >> y;
        spx[id] = x; spy[id] = y;
    }
    for (int k = 0; k < W * H; k++) prot[k] = -1;
    for (int i = 0; i < N; i++)
        for (int y = spy[i] - 1; y <= spy[i] + 1; y++)
            for (int x = spx[i] - 1; x <= spx[i] + 1; x++)
                if (inb(x, y)) prot[y * W + x] = i;
    EW = (N == 2) ? 2.0 : 1.8;  // melee: capturing enemy territory is almost as good as neutral
    while (true) {
        if (!(cin >> tok)) break;
        cin >> turnNo;
        for (int i = 0; i < N; i++) {
            int id; char d; Player q;
            cin >> tok >> id >> q.x >> q.y >> d >> q.tl >> q.area >> q.deaths;
            q.dir = dirIndex(d);
            pl[id] = q;
        }
        cin >> tok;  // OWNER
        for (int y = 0; y < H; y++) {
            string row; cin >> row;
            for (int x = 0; x < W; x++) own[y * W + x] = row[x] == '.' ? -1 : row[x] - '0';
        }
        cin >> tok;  // TRAIL
        for (int y = 0; y < H; y++) {
            string row; cin >> row;
            for (int x = 0; x < W; x++) trl[y * W + x] = row[x] == '.' ? -1 : row[x] - '0';
        }
        cin >> tok;  // END
        int d = decide();
        cout << turnNo << ' ' << DC[d] << endl;
    }
}
