// Urban Water Supply & Leak Detection Network
// DSA Microproject - menu-driven prototype
// Graph + MST (Kruskal / Prim) + BFS / DFS fault isolation + BST sensor registry
//
// Compile:  g++ -O2 -std=c++17 -o water water.cpp
// Run:      ./water            (Windows: water.exe)
// Extras:   ./water --tests    runs the report tests T1-T11 and exits
//           ./water --bench    runs only the scaling benchmark and exits

#include <bits/stdc++.h>
using namespace std;

struct Edge { int u, v, w; };

// ---------------------------------------------------------------- helpers
static string low(string s) { for (auto& c : s) c = (char)tolower((unsigned char)c); return s; }
static string trim(const string& s) {
    size_t a = s.find_first_not_of(" \t\r\n");
    if (a == string::npos) return "";
    size_t b = s.find_last_not_of(" \t\r\n");
    return s.substr(a, b - a + 1);
}
static string ask(const string& prompt) {
    cout << prompt; cout.flush();
    string s;
    if (!getline(cin, s)) { cout << "\n"; exit(0); }
    return trim(s);
}
static int askInt(const string& prompt, int lo, int hi) {
    while (true) {
        string s = ask(prompt);
        try {
            size_t pos; int v = stoi(s, &pos);
            if (pos == s.size() && v >= lo && v <= hi) return v;
        } catch (...) {}
        cout << "  Please enter a whole number between " << lo << " and " << hi << ".\n";
    }
}
static double askDouble(const string& prompt, double lo, double hi) {
    while (true) {
        string s = ask(prompt);
        try {
            size_t pos; double v = stod(s, &pos);
            if (pos == s.size() && v >= lo && v <= hi) return v;
        } catch (...) {}
        cout << "  Please enter a number between " << lo << " and " << hi << ".\n";
    }
}
static void line(char c = '-', int n = 64) { cout << string(n, c) << "\n"; }

// ------------------------------------------------------------------ Graph
class Graph {
public:
    vector<string> names;
    vector<Edge> edges;
    map<string, int> id;

    int V() const { return (int)names.size(); }
    int find(const string& n) const { auto it = id.find(low(n)); return it == id.end() ? -1 : it->second; }
    int addNode(const string& n) {
        if (find(n) >= 0) return -1;
        id[low(n)] = V(); names.push_back(n); return V() - 1;
    }
    bool hasEdge(int a, int b) const {
        for (auto& e : edges) if ((e.u == a && e.v == b) || (e.u == b && e.v == a)) return true;
        return false;
    }
    bool addEdge(const string& a, const string& b, int w) {
        int x = find(a), y = find(b);
        if (x < 0 || y < 0 || x == y || w <= 0 || hasEdge(x, y)) return false;
        edges.push_back({x, y, w}); return true;
    }
    void clear() { names.clear(); edges.clear(); id.clear(); }
};

static void loadSample(Graph& g) {
    g.clear();
    for (string n : {"Plant", "Z1", "Z2", "Z3", "Z4", "Z5", "Z6", "Z7"}) g.addNode(n);
    struct E { const char* a; const char* b; int w; };
    vector<E> es = {{"Plant","Z1",4},{"Plant","Z2",8},{"Z1","Z2",11},{"Z1","Z3",8},{"Z2","Z4",7},
                    {"Z2","Z5",1},{"Z3","Z4",2},{"Z3","Z6",4},{"Z4","Z5",6},{"Z4","Z7",14},
                    {"Z5","Z7",9},{"Z6","Z7",10},{"Z1","Z6",9}};
    for (auto& e : es) g.addEdge(e.a, e.b, e.w);
}

static string edgeStr(const Graph& g, const Edge& e) {
    return g.names[e.u] + " - " + g.names[e.v] + " (" + to_string(e.w) + ")";
}

// -------------------------------------------------------------- Union-Find
struct DSU {
    vector<int> p, r;
    DSU(int n) : p(n), r(n, 0) { iota(p.begin(), p.end(), 0); }
    int find(int x) { return p[x] == x ? x : p[x] = find(p[x]); }
    bool unite(int a, int b) {
        a = find(a); b = find(b);
        if (a == b) return false;
        if (r[a] < r[b]) swap(a, b);
        p[b] = a; if (r[a] == r[b]) r[a]++;
        return true;
    }
};

// --------------------------------------------------------------------- MST
static vector<Edge> kruskal(int V, vector<Edge> e) {
    stable_sort(e.begin(), e.end(), [](const Edge& a, const Edge& b) { return a.w < b.w; });
    DSU d(V); vector<Edge> mst;
    for (auto& x : e) if (d.unite(x.u, x.v)) mst.push_back(x);
    return mst;
}
static vector<Edge> prim(int V, const vector<Edge>& e, int start = 0) {
    vector<vector<pair<int,int>>> adj(V);
    for (auto& x : e) { adj[x.u].push_back({x.v, x.w}); adj[x.v].push_back({x.u, x.w}); }
    vector<bool> in(V, false); vector<Edge> mst;
    priority_queue<tuple<int,int,int>, vector<tuple<int,int,int>>, greater<>> pq;
    in[start] = true;
    for (auto& a : adj[start]) pq.push({a.second, start, a.first});
    while (!pq.empty()) {
        auto [w, u, v] = pq.top(); pq.pop();
        if (in[v]) continue;
        in[v] = true; mst.push_back({u, v, w});
        for (auto& a : adj[v]) if (!in[a.first]) pq.push({a.second, v, a.first});
    }
    return mst;
}
static long long total(const vector<Edge>& m) { long long s = 0; for (auto& x : m) s += x.w; return s; }

// ------------------------------------------------------------- BFS / DFS
static vector<vector<int>> adjOf(int V, const vector<Edge>& e, int skipU = -1, int skipV = -1) {
    vector<vector<int>> a(V);
    for (auto& x : e) {
        if ((x.u == skipU && x.v == skipV) || (x.u == skipV && x.v == skipU)) continue;
        a[x.u].push_back(x.v); a[x.v].push_back(x.u);
    }
    return a;
}
static vector<int> bfs(const vector<vector<int>>& a, int s) {
    vector<bool> vis(a.size(), false); vector<int> order; queue<int> q;
    q.push(s); vis[s] = true;
    while (!q.empty()) {
        int u = q.front(); q.pop(); order.push_back(u);
        for (int v : a[u]) if (!vis[v]) { vis[v] = true; q.push(v); }
    }
    return order;
}
static bool dfsPath(const vector<vector<int>>& a, int u, int t, vector<bool>& vis, vector<int>& path) {
    vis[u] = true; path.push_back(u);
    if (u == t) return true;
    for (int v : a[u]) if (!vis[v] && dfsPath(a, v, t, vis, path)) return true;
    path.pop_back(); return false;
}
// parent[v] = the zone that feeds v in the MST rooted at the plant (node 0)
static vector<int> parentsOf(int V, const vector<Edge>& mst) {
    auto A = adjOf(V, mst);
    vector<int> par(V, -1); vector<bool> vis(V, false); queue<int> q;
    q.push(0); vis[0] = true;
    while (!q.empty()) {
        int u = q.front(); q.pop();
        for (int v : A[u]) if (!vis[v]) { vis[v] = true; par[v] = u; q.push(v); }
    }
    return par;
}
static bool inMst(const vector<Edge>& m, int a, int b) {
    for (auto& e : m) if ((e.u == a && e.v == b) || (e.u == b && e.v == a)) return true;
    return false;
}
// zones that lose supply when pipe a-b is closed (BFS from the plant)
static vector<int> cutOff(const Graph& g, const vector<Edge>& mst, int a, int b) {
    auto A = adjOf(g.V(), mst, a, b);
    auto ord = bfs(A, 0);
    vector<bool> ok(g.V(), false);
    for (int x : ord) ok[x] = true;
    vector<int> r;
    for (int i = 1; i < g.V(); i++) if (!ok[i]) r.push_back(i);
    return r;
}
static string joinNames(const Graph& g, const vector<int>& v) {
    if (v.empty()) return "(none)";
    string s;
    for (size_t i = 0; i < v.size(); i++) s += g.names[v[i]] + (i + 1 < v.size() ? ", " : "");
    return s;
}

// --------------------------------------------------------- BST sensor registry
struct Sensor { int id; string zone; vector<double> drops; };
struct BNode { Sensor s; BNode *l = nullptr, *r = nullptr; BNode(Sensor x) : s(std::move(x)) {} };

class BST {
    static void destroy(BNode* n) { if (!n) return; destroy(n->l); destroy(n->r); delete n; }
    BNode* insertRec(BNode* n, const Sensor& s, bool& added) {
        if (!n) { added = true; return new BNode(s); }
        if (s.id < n->s.id) n->l = insertRec(n->l, s, added);
        else if (s.id > n->s.id) n->r = insertRec(n->r, s, added);
        else added = false;
        return n;
    }
    BNode* removeRec(BNode* n, int id, bool& done) {
        if (!n) return nullptr;
        if (id < n->s.id) n->l = removeRec(n->l, id, done);
        else if (id > n->s.id) n->r = removeRec(n->r, id, done);
        else {
            done = true;
            if (!n->l) { BNode* r = n->r; delete n; return r; }
            if (!n->r) { BNode* l = n->l; delete n; return l; }
            BNode* m = n->r; while (m->l) m = m->l;       // in-order successor
            n->s = m->s;
            bool d2 = false; n->r = removeRec(n->r, m->s.id, d2);
        }
        return n;
    }
    void inorderRec(BNode* n, vector<Sensor*>& out) { if (!n) return; inorderRec(n->l, out); out.push_back(&n->s); inorderRec(n->r, out); }
    int heightRec(BNode* n) { return n ? 1 + max(heightRec(n->l), heightRec(n->r)) : 0; }
public:
    BNode* root = nullptr; int cnt = 0;
    BST() {}
    BST(const BST&) = delete;
    BST& operator=(const BST&) = delete;
    ~BST() { destroy(root); }
    void clear() { destroy(root); root = nullptr; cnt = 0; }
    bool insert(const Sensor& s) { bool a = false; root = insertRec(root, s, a); if (a) cnt++; return a; }
    bool remove(int id) { bool d = false; root = removeRec(root, id, d); if (d) cnt--; return d; }
    BNode* search(int id, int& steps) {
        BNode* c = root; steps = 0;
        while (c) { steps++; if (id == c->s.id) return c; c = id < c->s.id ? c->l : c->r; }
        return nullptr;
    }
    vector<Sensor*> inorder() { vector<Sensor*> o; inorderRec(root, o); return o; }
    int height() { return heightRec(root); }
};

// =================================================================== App
static const double ALARM_PSI = 20.0;   // a drop at or above this triggers fault isolation

struct App {
    Graph g;
    vector<Edge> mst;
    string algo;
    BST sensors;

    void invalidate() { mst.clear(); algo.clear(); }

    void loadSampleAll() {
        loadSample(g); invalidate(); sensors.clear();
        int ids[] = {50, 30, 70, 20, 40, 60, 80};
        const char* zn[] = {"Z1", "Z2", "Z3", "Z4", "Z5", "Z6", "Z7"};
        for (int i = 0; i < 7; i++) sensors.insert({ids[i], zn[i], {}});
        cout << "  Sample network loaded: 1 plant, 7 zones, 13 candidate pipelines, 7 sensors.\n";
    }

    void showNetwork() {
        line('=');
        cout << "NETWORK  (V = " << g.V() << " nodes, E = " << g.edges.size() << " candidate pipelines)\n";
        line();
        if (g.V() == 0) { cout << "  Empty. Use option 1 or 2.\n"; return; }
        cout << "  Nodes: ";
        for (int i = 0; i < g.V(); i++) cout << g.names[i] << (i == 0 ? " [plant]" : "") << (i + 1 < g.V() ? ", " : "\n");
        cout << "  Candidate pipelines (cost):\n";
        long long all = 0;
        for (auto& e : g.edges) { cout << "    " << edgeStr(g, e) << "\n"; all += e.w; }
        cout << "  Total cost of ALL candidates = " << all << "\n";
        if (!mst.empty()) {
            cout << "  Built network (" << algo << "), " << mst.size() << " pipes, cost " << total(mst) << ":\n";
            for (auto& e : mst) cout << "    " << edgeStr(g, e) << "\n";
        } else cout << "  Least-cost network not built yet (use option 4 or 5).\n";
    }

    bool build(bool useKruskal) {
        if (g.V() < 2) { cout << "  Add a plant and at least one zone first.\n"; return false; }
        auto e = useKruskal ? kruskal(g.V(), g.edges) : prim(g.V(), g.edges, 0);
        if ((int)e.size() != g.V() - 1) {
            auto reach = bfs(adjOf(g.V(), g.edges), 0);
            vector<bool> ok(g.V(), false); for (int x : reach) ok[x] = true;
            vector<int> miss; for (int i = 0; i < g.V(); i++) if (!ok[i]) miss.push_back(i);
            cout << "  The candidate network is NOT connected - no spanning tree exists.\n"
                 << "  Zones with no possible route from the plant: " << joinNames(g, miss) << "\n"
                 << "  Add more candidate pipelines (option 3) and try again.\n";
            return false;
        }
        mst = e; algo = useKruskal ? "Kruskal" : "Prim";
        long long all = 0; for (auto& x : g.edges) all += x.w;
        cout << "  " << algo << "'s MST built:\n";
        for (auto& x : mst) cout << "    " << edgeStr(g, x) << "\n";
        cout << "  Pipes = " << mst.size() << " (V-1), total cost = " << total(mst)
             << " vs " << all << " for all candidates -> saving "
             << all - total(mst) << " (" << fixed << setprecision(1) << 100.0 * (all - total(mst)) / all << "%)\n";
        cout.unsetf(ios::floatfield); cout << setprecision(6);
        return true;
    }
    bool needMST() {
        if (g.V() < 2) { cout << "  Add a plant and at least one zone first.\n"; return false; }
        if (mst.empty()) { cout << "  (Network not built yet - building it with Kruskal's first.)\n"; return build(true); }
        return true;
    }

    void compare() {
        if (g.V() < 2) { cout << "  Add a plant and at least one zone first.\n"; return; }
        auto k = kruskal(g.V(), g.edges), p = prim(g.V(), g.edges, 0);
        if ((int)k.size() != g.V() - 1) { build(true); return; }
        cout << "  Kruskal total = " << total(k) << ",  Prim total = " << total(p)
             << "  -> equal? " << (total(k) == total(p) ? "YES" : "NO") << "\n";
        int E = (int)g.edges.size(), V = g.V();
        if (E > 22) { cout << "  Brute-force optimality check skipped (more than 22 candidate pipes).\n"; return; }
        long long best = LLONG_MAX, trees = 0;
        for (long long mask = 0; mask < (1LL << E); mask++) {
            if (__builtin_popcountll(mask) != V - 1) continue;
            DSU d(V); bool ok = true; long long s = 0;
            for (int i = 0; i < E && ok; i++) if (mask >> i & 1) { if (!d.unite(g.edges[i].u, g.edges[i].v)) ok = false; s += g.edges[i].w; }
            if (ok) { trees++; best = min(best, s); }
        }
        cout << "  Brute force: " << trees << " spanning trees enumerated, cheapest = " << best
             << "  -> MST optimal? " << (best == total(k) ? "YES" : "NO") << "\n";
    }

    void traceFlow() {
        if (!needMST()) return;
        string z = ask("  Destination zone: ");
        int t = g.find(z);
        if (t < 0) { cout << "  No such zone.\n"; return; }
        auto A = adjOf(g.V(), mst);
        cout << "  BFS visit order from plant: ";
        for (int x : bfs(A, 0)) cout << g.names[x] << " "; cout << "\n";
        vector<bool> vis(g.V(), false); vector<int> path;
        if (!dfsPath(A, 0, t, vis, path)) { cout << "  No flow path found.\n"; return; }
        cout << "  DFS flow path: ";
        for (size_t i = 0; i < path.size(); i++) cout << g.names[path[i]] << (i + 1 < path.size() ? " -> " : "\n");
        cout << "  Pipes crossed: " << path.size() - 1 << "\n";
    }

    void isolateReport(int a, int b) {
        if (!inMst(mst, a, b)) {
            cout << "  Pipe " << g.names[a] << " - " << g.names[b] << " is not part of the built network -> no zones affected.\n";
            return;
        }
        auto cut = cutOff(g, mst, a, b);
        cout << "  Close pipe " << g.names[a] << " - " << g.names[b] << ":\n"
             << "    supplied zones : " << (g.V() - 1 - (int)cut.size()) << " of " << g.V() - 1 << "\n"
             << "    cut-off zones  : " << joinNames(g, cut) << "\n";
    }
    void isolateLeak() {
        if (!needMST()) return;
        int a = g.find(ask("  Leaking pipe, first end  : "));
        int b = g.find(ask("  Leaking pipe, second end : "));
        if (a < 0 || b < 0 || a == b) { cout << "  Unknown zone name(s).\n"; return; }
        isolateReport(a, b);
    }
    void contamination() {
        if (!needMST()) return;
        int z = g.find(ask("  Contaminated zone: "));
        if (z <= 0) { cout << "  Enter a distribution zone (not the plant, not unknown).\n"; return; }
        auto par = parentsOf(g.V(), mst);
        auto A = adjOf(g.V(), mst, z, par[z]);
        auto o = bfs(A, z);
        cout << "  Parent pipe " << g.names[par[z]] << " - " << g.names[z] << " closed.\n"
             << "  Contamination can reach (downstream): ";
        for (int x : o) cout << g.names[x] << " "; cout << "| " << o.size() << " zone(s)\n";
    }

    // ------------------------------------------------------------ sensors
    void registerSensor() {
        int id = askInt("  Sensor ID (1-999999): ", 1, 999999);
        string z = ask("  Zone it monitors   : ");
        if (g.find(z) < 0) { cout << "  Zone '" << z << "' is not in the network.\n"; return; }
        bool ok = sensors.insert({id, g.names[g.find(z)], {}});
        cout << (ok ? "  Sensor registered.\n" : "  Duplicate sensor ID rejected.\n");
    }
    void searchSensor() {
        int id = askInt("  Sensor ID to search: ", 1, 999999);
        int st; BNode* n = sensors.search(id, st);
        if (!n) { cout << "  Sensor S" << id << " not found (" << st << " comparison" << (st == 1 ? "" : "s") << ").\n"; return; }
        cout << "  Found S" << id << " in " << st << " step(s). Zone: " << n->s.zone
             << ". Logged pressure drops: " << n->s.drops.size();
        if (!n->s.drops.empty()) {
            cout << " [";
            for (size_t i = 0; i < n->s.drops.size(); i++) cout << n->s.drops[i] << (i + 1 < n->s.drops.size() ? ", " : "");
            cout << "] psi";
        }
        cout << "\n";
    }
    void pressureDrop() {
        int id = askInt("  Sensor ID reporting: ", 1, 999999);
        int st; BNode* n = sensors.search(id, st);
        if (!n) { cout << "  Sensor S" << id << " is not registered.\n"; return; }
        double d = askDouble("  Pressure drop (psi): ", 0, 1000);
        n->s.drops.push_back(d);
        cout << "  Logged " << d << " psi for S" << id << " (zone " << n->s.zone << ").\n";
        if (d < ALARM_PSI) { cout << "  Below the " << ALARM_PSI << " psi alarm level - monitoring continues.\n"; return; }
        cout << "  *** LEAK ALARM: drop >= " << ALARM_PSI << " psi ***\n";
        if (!needMST()) return;
        int z = g.find(n->s.zone);
        if (z <= 0) { cout << "  Sensor sits at the plant; inspect the plant outlet manually.\n"; return; }
        auto par = parentsOf(g.V(), mst);
        cout << "  Suspect pipe = parent pipe of " << g.names[z] << " in the network: "
             << g.names[par[z]] << " - " << g.names[z] << "\n";
        isolateReport(par[z], z);
        cout << "  Valves to shut: only that pipe. The other " << (g.V() - 1) - (int)cutOff(g, mst, par[z], z).size()
             << " zone(s) keep their supply.\n";
    }
    void deleteSensor() {
        int id = askInt("  Sensor ID to delete: ", 1, 999999);
        cout << (sensors.remove(id) ? "  Sensor deleted.\n" : "  Sensor not found.\n");
    }
    void showSensors() {
        auto v = sensors.inorder();
        line('=');
        cout << "SENSOR REGISTRY (BST in-order = sorted by ID)  count=" << sensors.cnt << "  tree height=" << sensors.height() << "\n";
        line();
        if (v.empty()) cout << "  (empty)\n";
        for (auto s : v) {
            cout << "  S" << setw(6) << left << s->id << right << " zone " << setw(6) << left << s->zone << right
                 << " drops logged: " << s->drops.size();
            if (!s->drops.empty()) cout << "  (last " << s->drops.back() << " psi)";
            cout << "\n";
        }
    }
};

// ============================================== report tests (T1 - T11)
static void benchmark() {
    cout << "\n[T10] Scaling benchmark (random connected graphs, E=4V, seed=7)\n";
    cout << "  V        E        Kruskal(ms)  Prim(ms)  BFS(ms)  cost_equal\n";
    mt19937 rng(7);
    for (int V : {1000, 5000, 20000, 100000}) {
        vector<Edge> e;
        for (int i = 1; i < V; i++) e.push_back({(int)(rng() % i), i, (int)(rng() % 1000) + 1});
        while ((int)e.size() < 4 * V) { int a = rng() % V, b = rng() % V; if (a != b) e.push_back({a, b, (int)(rng() % 1000) + 1}); }
        auto t0 = chrono::steady_clock::now(); auto k = kruskal(V, e);
        auto t1 = chrono::steady_clock::now(); auto p = prim(V, e, 0);
        auto t2 = chrono::steady_clock::now(); auto ad = adjOf(V, k); auto o = bfs(ad, 0);
        auto t3 = chrono::steady_clock::now();
        auto ms = [](auto a, auto b) { return chrono::duration<double, milli>(b - a).count(); };
        cout << "  " << setw(7) << left << V << "  " << setw(7) << e.size() << "  " << setw(11) << fixed << setprecision(2) << ms(t0, t1)
             << "  " << setw(8) << ms(t1, t2) << "  " << setw(7) << ms(t2, t3) << "  "
             << (total(k) == total(p) ? "yes" : "NO") << " (bfs visited " << o.size() << ")\n";
    }
    cout.unsetf(ios::floatfield); cout << setprecision(6);
}
static void bstBalance() {
    cout << "\n[T11] BST balance: random vs sorted insertion\n";
    mt19937 rng(7);
    for (int n : {1000, 10000}) {
        BST r, s; vector<int> v(n); iota(v.begin(), v.end(), 1);
        for (int i = 0; i < n; i++) s.insert({v[i], "", {}});
        shuffle(v.begin(), v.end(), rng);
        for (int x : v) r.insert({x, "", {}});
        int st; s.search(n, st);
        cout << "  n=" << n << "  random: height=" << r.height() << "  | sorted: height=" << s.height()
             << " (worst-case search steps=" << st << ")\n";
    }
}
static void runReportTests() {
    App a; a.loadSampleAll();
    Graph& g = a.g;
    cout << "\nV=" << g.V() << " E=" << g.edges.size() << "\n";
    long long base = 0; for (auto& e : g.edges) base += e.w;
    cout << "Total cost of ALL candidate pipelines = " << base << "\n";

    cout << "\n[T1] Kruskal MST\n";
    auto mk = kruskal(g.V(), g.edges);
    for (auto& e : mk) cout << "  " << edgeStr(g, e) << "\n";
    cout << "  edges=" << mk.size() << " total=" << total(mk) << "\n";

    cout << "\n[T2] Prim MST (start=Plant)\n";
    auto mp = prim(g.V(), g.edges, 0);
    for (auto& e : mp) cout << "  " << edgeStr(g, e) << "\n";
    cout << "  edges=" << mp.size() << " total=" << total(mp) << "\n";
    cout << "  Kruskal total == Prim total ? " << (total(mk) == total(mp) ? "YES" : "NO") << "\n";
    cout << "  Cost saving vs all candidates = " << base - total(mk) << " (" << fixed << setprecision(1)
         << 100.0 * (base - total(mk)) / base << "%)\n";
    cout.unsetf(ios::floatfield); cout << setprecision(6);

    { // T3 brute force
        int E = (int)g.edges.size(), V = g.V(); long long best = LLONG_MAX, trees = 0;
        for (int mask = 0; mask < (1 << E); mask++) {
            if (__builtin_popcount(mask) != V - 1) continue;
            DSU d(V); bool ok = true; long long s = 0;
            for (int i = 0; i < E && ok; i++) if (mask >> i & 1) { if (!d.unite(g.edges[i].u, g.edges[i].v)) ok = false; s += g.edges[i].w; }
            if (ok) { trees++; best = min(best, s); }
        }
        cout << "\n[T3] Brute-force check: spanning trees enumerated=" << trees << " minimum cost=" << best
             << " -> MST optimal ? " << (best == total(mk) ? "YES" : "NO") << "\n";
    }

    auto A = adjOf(g.V(), mk);
    cout << "\n[T4] BFS from Plant over MST: ";
    for (int x : bfs(A, 0)) cout << g.names[x] << " "; cout << "\n";
    cout << "[T5] DFS flow path Plant -> Z7: ";
    { vector<bool> vis(g.V(), false); vector<int> p; bool f = dfsPath(A, 0, g.find("Z7"), vis, p);
      cout << (f ? "" : "NOT FOUND");
      for (size_t i = 0; i < p.size(); i++) cout << g.names[p[i]] << (i + 1 < p.size() ? " -> " : ""); cout << "\n"; }

    cout << "\n[T6] Leak isolation on MST pipes (only the faulty segment closed)\n";
    for (auto& e : mk) {
        auto cut = cutOff(g, mk, e.u, e.v);
        cout << "  Leak on pipe " << g.names[e.u] << "-" << g.names[e.v] << ": supplied zones = "
             << g.V() - 1 - (int)cut.size() << " of " << g.V() - 1 << "; cut-off zones: ";
        if (cut.empty()) cout << "(none)"; for (int x : cut) cout << g.names[x] << " "; cout << "\n";
    }
    cout << "[T7] Leak on non-MST candidate pipe Z4-Z7 (not built): "
         << (inMst(mk, g.find("Z4"), g.find("Z7")) ? "in MST" : "not part of built network -> no zones affected") << "\n";
    cout << "[T8] Contamination detected at Z5 (parent pipe Z2-Z5 closed); zones reachable downstream via BFS: ";
    { auto A3 = adjOf(g.V(), mk, g.find("Z2"), g.find("Z5")); auto o = bfs(A3, g.find("Z5"));
      for (int x : o) cout << g.names[x] << " "; cout << "| count=" << o.size() << "\n"; }

    cout << "\n[T9] BST sensor registry\n";
    { BST t; int ids[] = {50, 30, 70, 20, 40, 60, 80, 30}; string zn[] = {"Z1","Z2","Z3","Z4","Z5","Z6","Z7","Z2"};
      for (int i = 0; i < 8; i++) { bool ad = t.insert({ids[i], zn[i], {}}); cout << "  insert S" << ids[i] << " -> " << (ad ? "added" : "duplicate rejected") << "\n"; }
      int st; auto n = t.search(60, st); n->s.drops.push_back(12.5); n->s.drops.push_back(31.0);
      cout << "  search S60: found, steps=" << st << ", logs=" << n->s.drops.size() << " (last drop " << n->s.drops.back() << " psi)\n";
      n = t.search(65, st); cout << "  search S65: " << (n ? "found" : "not found") << ", steps=" << st << "\n";
      cout << "  in-order IDs: "; for (auto s : t.inorder()) cout << s->id << " ";
      cout << "| count=" << t.cnt << " height=" << t.height() << "\n";
      t.remove(50);
      cout << "  after deleting S50 (BST deletion): "; for (auto s : t.inorder()) cout << s->id << " ";
      cout << "| count=" << t.cnt << " height=" << t.height() << "\n"; }

    benchmark();
    bstBalance();
}

// =================================================================== menu
static void menu() {
    cout << "\n";
    line('=');
    cout << " URBAN WATER SUPPLY & LEAK DETECTION NETWORK\n";
    line('=');
    cout << " NETWORK DESIGN                       FAULT HANDLING\n"
            "  1  Load sample network               9  Trace flow  (BFS / DFS)\n"
            "  2  Create new empty network         10  Isolate a leaking pipe\n"
            "  3  Add zone / candidate pipeline    11  Contamination reach\n"
            "  4  Build network - Kruskal's MST\n"
            "  5  Build network - Prim's MST       SENSOR REGISTRY (BST)\n"
            "  6  Compare Kruskal vs Prim +        12  Register sensor\n"
            "     brute-force optimality check     13  Search sensor / pressure logs\n"
            "  7  Show network                     14  Report pressure drop (auto-alarm)\n"
            "  8  Show built (MST) pipes only      15  Delete sensor\n"
            "                                      16  Show sensors (sorted)\n"
            " TESTING\n"
            " 17  Run all report tests T1-T11     18  Scaling benchmark\n"
            "  0  Exit\n";
    line();
}

int main(int argc, char** argv) {
    if (argc > 1 && string(argv[1]) == "--tests") { runReportTests(); return 0; }
    if (argc > 1 && string(argv[1]) == "--bench") { benchmark(); bstBalance(); return 0; }

    App app;
    app.loadSampleAll();
    while (true) {
        menu();
        int c = askInt("Choose an option (0-18): ", 0, 18);
        cout << "\n";
        switch (c) {
            case 0: cout << "Goodbye.\n"; return 0;
            case 1: app.loadSampleAll(); break;
            case 2: {
                string p = ask("  Name of the treatment plant: ");
                if (p.empty()) { cout << "  Name cannot be empty.\n"; break; }
                app.g.clear(); app.invalidate(); app.sensors.clear(); app.g.addNode(p);
                cout << "  New network created with plant '" << p << "'. Add zones and pipelines with option 3.\n";
                break;
            }
            case 3: {
                cout << "  a) add a zone   b) add a candidate pipeline\n";
                string t = low(ask("  Choose a or b: "));
                if (t == "a") {
                    string n = ask("  Zone name: ");
                    if (n.empty()) cout << "  Name cannot be empty.\n";
                    else if (app.g.addNode(n) < 0) cout << "  That name already exists.\n";
                    else { app.invalidate(); cout << "  Zone added.\n"; }
                } else if (t == "b") {
                    string a = ask("  From node: "), b = ask("  To node  : ");
                    int w = askInt("  Cost / length (1-1000000): ", 1, 1000000);
                    if (app.g.find(a) < 0 || app.g.find(b) < 0) cout << "  Unknown node name.\n";
                    else if (app.g.find(a) == app.g.find(b)) cout << "  A pipe must join two different nodes.\n";
                    else if (!app.g.addEdge(a, b, w)) cout << "  That pipeline already exists.\n";
                    else { app.invalidate(); cout << "  Pipeline added.\n"; }
                } else cout << "  Please choose a or b.\n";
                break;
            }
            case 4: app.build(true); break;
            case 5: app.build(false); break;
            case 6: app.compare(); break;
            case 7: app.showNetwork(); break;
            case 8:
                if (app.mst.empty()) cout << "  Network not built yet (use option 4 or 5).\n";
                else {
                    cout << "  Built network (" << app.algo << "), cost " << total(app.mst) << ":\n";
                    for (auto& e : app.mst) cout << "    " << edgeStr(app.g, e) << "\n";
                }
                break;
            case 9: app.traceFlow(); break;
            case 10: app.isolateLeak(); break;
            case 11: app.contamination(); break;
            case 12: app.registerSensor(); break;
            case 13: app.searchSensor(); break;
            case 14: app.pressureDrop(); break;
            case 15: app.deleteSensor(); break;
            case 16: app.showSensors(); break;
            case 17: runReportTests(); break;
            case 18: benchmark(); bstBalance(); break;
        }
        ask("\nPress Enter to continue...");
    }
}
