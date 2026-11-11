// Certificate-free exact check: BLIF netlist == [popcount(A) >= T].
// Reduced ordered BDDs, variable order A[0] < A[1] < ... ; canonical form => pointer equality.
// Uses no derivation and no Colony code.  Build: c++ -O2 -std=c++17 bdd_threshold_check.cpp -o bddcheck
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <string>
#include <vector>
#include <unordered_map>
#include <fstream>
#include <sstream>
#include <iostream>
using namespace std;
struct Node { uint32_t var, lo, hi; };
static vector<Node> N;                      // 0 = false, 1 = true
struct K3 { uint64_t a; uint32_t b; bool operator==(const K3&o) const { return a==o.a && b==o.b; } };
struct H3 { size_t operator()(const K3&k) const { return (k.a*0x9E3779B97F4A7C15ULL) ^ (uint64_t(k.b)*0xC2B2AE3D27D4EB4FULL); } };
static unordered_map<K3,uint32_t,H3> uniq, cache;
static uint32_t mk(uint32_t v, uint32_t lo, uint32_t hi) {
  if (lo == hi) return lo;
  K3 k{ (uint64_t(lo) << 32) | hi, v };
  auto it = uniq.find(k); if (it != uniq.end()) return it->second;
  N.push_back({v, lo, hi}); uint32_t id = N.size() - 1; uniq.emplace(k, id); return id;
}
static uint32_t ite(uint32_t f, uint32_t g, uint32_t h) {
  if (f == 1) return g; if (f == 0) return h; if (g == h) return g; if (g == 1 && h == 0) return f;
  K3 k{ (uint64_t(f) << 32) | g, h };
  auto it = cache.find(k); if (it != cache.end()) return it->second;
  uint32_t v = N[f].var; if (g > 1 && N[g].var < v) v = N[g].var; if (h > 1 && N[h].var < v) v = N[h].var;
  auto co = [&](uint32_t x, bool hi) { return (x > 1 && N[x].var == v) ? (hi ? N[x].hi : N[x].lo) : x; };
  uint32_t r = mk(v, ite(co(f,0), co(g,0), co(h,0)), ite(co(f,1), co(g,1), co(h,1)));
  cache.emplace(k, r); return r;
}
int main(int argc, char** argv) {
  if (argc != 4) { fprintf(stderr, "usage: bddcheck netlist.blif n T\n"); return 2; }
  int n = atoi(argv[2]), T = atoi(argv[3]);
  N.push_back({0xffffffffu,0,0}); N.push_back({0xffffffffu,1,1});
  ifstream in(argv[1]); string line, acc; vector<string> lines;
  while (getline(in, line)) { if (!line.empty() && line.back()=='\\') { line.pop_back(); acc += line + " "; continue; } lines.push_back(acc + line); acc.clear(); }
  unordered_map<string,uint32_t> val; vector<string> inputs, outputs;
  struct Tab { vector<string> ins; vector<string> rows; string out; }; vector<Tab> tabs;
  for (auto& l : lines) {
    istringstream ss(l); vector<string> t; string w; while (ss >> w) t.push_back(w);
    if (t.empty() || t[0][0]=='#') continue;
    if (t[0]==".inputs") inputs.insert(inputs.end(), t.begin()+1, t.end());
    else if (t[0]==".outputs") outputs.insert(outputs.end(), t.begin()+1, t.end());
    else if (t[0]==".names") { Tab b; b.out = t.back(); b.ins.assign(t.begin()+1, t.end()-1); tabs.push_back(b); }
    else if (t[0]==".model" || t[0]==".end") continue;
    else if (t[0][0]=='.') { fprintf(stderr, "unsupported %s\n", t[0].c_str()); return 2; }
    else { if (t.size()!=2 || t[1]!="1" || tabs.empty()) { fprintf(stderr, "only on-set rows supported\n"); return 2; } tabs.back().rows.push_back(t[0]); }
  }
  if ((int)inputs.size() != n || outputs.size() != 1) { fprintf(stderr, "interface mismatch\n"); return 2; }
  for (int i = 0; i < n; i++) { string nm = "A[" + to_string(i) + "]"; if (inputs[i] != nm) { fprintf(stderr, "input order\n"); return 2; } val[nm] = mk(i, 0, 1); }
  size_t maxfan = 0;
  for (auto& b : tabs) {                      // netlist is emitted in topological order; enforce it
    if (val.count(b.out)) { fprintf(stderr, "double driver %s\n", b.out.c_str()); return 2; }
    vector<uint32_t> f; for (auto& s : b.ins) { auto it = val.find(s); if (it == val.end()) { fprintf(stderr, "not topological at %s\n", b.out.c_str()); return 2; } f.push_back(it->second); }
    if (b.ins.size() > maxfan) maxfan = b.ins.size();
    size_t k = f.size(); if (k > 16) { fprintf(stderr, "fan-in > 16\n"); return 2; }
    vector<char> tt(size_t(1) << k, 0);
    for (auto& row : b.rows) {
      if (row.size() != k) { fprintf(stderr, "row width\n"); return 2; }
      size_t idx = 0; for (size_t i = 0; i < k; i++) { if (row[i]=='1') idx |= size_t(1) << i; else if (row[i]!='0') { fprintf(stderr, "row char\n"); return 2; } }
      tt[idx] = 1;
    }
    // Shannon expansion on the LUT inputs, last input outermost
    vector<uint32_t> lev(tt.begin(), tt.end());
    for (size_t i = 0; i < k; i++) { vector<uint32_t> up(lev.size() / 2); for (size_t j = 0; j < up.size(); j++) up[j] = ite(f[i], lev[2*j+1], lev[2*j]); lev.swap(up); }
    uint32_t r = lev[0];
    if (cache.size() > 20000000) cache.clear();
    val[b.out] = r;
  }
  // reference: thr[i][c] = BDD for "inputs i..n-1 supply at least c more ones"
  vector<uint32_t> nxt(T + 2, 0), cur(T + 2, 0);
  nxt[0] = 1;                                 // need 0 more: true
  for (int i = n - 1; i >= 0; i--) { cur[0] = 1; for (int c = 1; c <= T; c++) cur[c] = mk(i, nxt[c], nxt[c-1]); nxt = cur; }
  uint32_t ref = nxt[T], got = val.at(outputs[0]);
  printf("{\"equal\": %s, \"n\": %d, \"threshold\": %d, \"luts\": %zu, \"max_fanin\": %zu, \"bdd_nodes_total\": %zu, \"reference_root\": %u, \"netlist_root\": %u}\n",
         ref == got ? "true" : "false", n, T, tabs.size(), maxfan, N.size(), ref, got);
  return ref == got ? 0 : 1;
}
