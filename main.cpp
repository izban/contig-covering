#include <bits/stdc++.h>
using namespace std;
typedef long long ll;

const int IMPROVED = 1;

struct tedge {
  string u, v;
  int k;
  char t;
};
enum type {
  RED, BLACK
};
struct edge {
  int u, v;
  type t;
  ll len;
  int cnt;

  bool operator== (const edge &ed) const {
    return ((u == ed.u && v == ed.v) || (u == ed.v && v == ed.u));
  }

  int go(int x) {
    assert(x == u || x == v);
    return x ^ u ^ v;
  }
};
int common(edge e1, edge e2) {
  assert(!(e1 == e2));
  if (e2.u == e1.v || e2.v == e1.v) return e1.v;
  if (e2.u == e1.u || e2.v == e1.u) return e1.u;
  return -1;
}

struct dsu {
  int n;
  vector<int> p;

  dsu(int _n) {
    n = _n;
    p.resize(n);
    iota(p.begin(), p.end(), 0);
  }

  int get(int x) {
    return x == p[x] ? x : p[x] = get(p[x]);
  }

  void uni(int u, int v) {
    p[get(v)] = get(u);
  }
};

vector<edge> find_cycle(vector<edge> ed) {
  int n = 0;
  for (auto o : ed) {
    n = max(n, o.u + 1);
    n = max(n, o.v + 1);
  }
  int m = ed.size();

  vector<vector<vector<int>>> e(n, vector<vector<int>>(2));
  for (int i = 0; i < m; i++) {
    int t = ed[i].t == BLACK;
    e[ed[i].u][t].push_back(i);
    e[ed[i].v][t].push_back(i);
  }
  for (int i = 0; i < n; i++) assert(e[i][0].size() == e[i][1].size());

  vector<char> used(m);
  vector<int> ans;
  function<void(int, int)> go = [&](int v, int t) {
    while (1) {
      while (!e[v][t].empty() && used[e[v][t].back()]) e[v][t].pop_back();
      if (e[v][t].empty()) return;
      int id = e[v][t].back();
      used[id] = 1;
      go(ed[id].go(v), t ^ 1);
      ans.push_back(id);
    }
  };
  go(0, 0);
  for (int i = 0; i < m; i++) assert(used[i]);

  assert((int)ans.size() == m);
  vector<edge> res;
  for (int i = 0; i < m; i++) res.push_back(ed[ans[i]]);

  for (int i = 0; i < m; i++) {
    assert(common(res[i], res[(i + 1) % m]) != -1);
    assert(res[i].t != res[(i + 1) % m].t);
  }

  return res;
}

int count_paths;

vector<vector<edge>> solve_connected(vector<edge> ed) {
  if (ed.empty()) return vector<vector<edge>>();
  vector<int> v;
  for (auto o : ed) {
    v.push_back(o.u);
    v.push_back(o.v);
  }
  sort(v.begin(), v.end());
  v.resize(unique(v.begin(), v.end()) - v.begin());
  auto getId = [&](int x) {
    return (int)(lower_bound(v.begin(), v.end(), x) - v.begin());
  };
  int n = v.size();

  for (auto &o : ed) {
    o.u = getId(o.u);
    o.v = getId(o.v);
    if (o.u > o.v) swap(o.u, o.v);
  }

  set<pair<int, int>> st;
  for (auto o : ed) {
    if (o.t == RED) {
      st.insert({o.u, o.v});
    }
  }
  vector<edge> ned;
  for (auto o : ed) {
    if (o.t == BLACK && st.find({o.u, o.v}) != st.end()) {
      ned.push_back({o.u, n, BLACK, 0, 0});
      ned.push_back({n, n + 1, RED, o.len, o.cnt});
      ned.push_back({o.v, n + 1, BLACK, 0, 0});
      n += 2;
    } else ned.push_back(o);
  }
  ed = ned;

  vector<int> deg(n);
  for (auto o : ed) {
    if (o.t == RED) {
      deg[o.u]++;
      deg[o.v]++;
    } else {
      deg[o.u]--;
      deg[o.v]--;
    }
  }


  int sum = 0;
  for (int i = 0; i < n; i++) {
    assert(deg[i] >= 0);
    sum += deg[i];
  }

  if (sum) {
    n += 2;
    for (int i = 0; i < n - 2; i++) {
      for (int j = 0; j < deg[i]; j++) {
        ed.push_back({i, n - 2, BLACK, 0, 0});
      }
    }
    assert(sum % 2 == 0);
    for (int i = 0; i < sum / 2; i++) {
      ed.push_back({n - 2, n - 1, RED, 0, 0});
      ed.push_back({n - 2, n - 1, RED, 0, 0});
      ed.push_back({n - 1, n - 1, BLACK, 0, 0});
    }
  }
  count_paths += max(1, sum / 2);

  auto cycle = find_cycle(ed);
  for (int i = 0; i < (int)cycle.size(); i++) {
    int c = common(cycle[i], cycle[(i + 1) % cycle.size()]);
    assert(c != -1);
    if (cycle[i].v != c) swap(cycle[i].u, cycle[i].v);
    if (cycle[(i + 1) % cycle.size()].u != c) swap(cycle[(i + 1) % cycle.size()].u, cycle[(i + 1) % cycle.size()].v);
  }

  for (int any = 1; any;) {
    any = 0;
    for (int i = 0; i + 2 < (int)cycle.size(); i++) {
      if (cycle[i].t == BLACK) {
        assert(cycle[i + 1].t == RED);
        assert(cycle[i + 2].t == BLACK);

        int a = cycle[i].u;
        assert(cycle[i].v == cycle[i + 1].u);
        int b = cycle[i].v;
        assert(cycle[i + 1].v == cycle[i + 2].u);
        int c = cycle[i + 1].v;
        int D = cycle[i + 2].v;
        
        if (sum && (a == n - 2 || b == n - 2 || c == n - 2 || D == n - 2)) continue;

        int kx = 0;
        vector<edge> et;
        vector<edge> oth;
        int kz = 0;
        for (int j = 0; j < (int)cycle.size(); j++) {
          if (cycle[j] == cycle[i]) {
            kx++;
          } else {
            if (cycle[j].t == RED || cycle[j] == cycle[i + 2] || (cycle[j].u != c && cycle[j].v != c)) {
              kz += cycle[j] == cycle[i + 2];
              oth.push_back(cycle[j]);
            } else {
              et.push_back(cycle[j]);
            }
          }
        }
        int kt = et.size();
        int ky = 0;
        for (int j = 0; j < (int)cycle.size(); j++) {
          if (cycle[j].t == BLACK && !(cycle[j] == cycle[i]) && (cycle[j].u == b || cycle[j].v == b)) {
            ky++;
          }
        }
        if (!IMPROVED) {
          if (kt != 0 || ky != 0) continue;
        }
        
        bool can_compress = 0;

        if (kt < kx) {
          can_compress = 1;
        } else if (kt == kx) {
          for (auto o : et) {
            oth.push_back({a, o.go(c), BLACK, 0, 0});
          }
          dsu d(n);
          int k = kx;
          for (auto o : oth) {
            if (o == cycle[i + 1] && k-- > 0) continue;
            d.uni(o.u, o.v);
          }
          can_compress = 0;
          for (int j = 1; j < (int)oth.size(); j++) if (d.get(oth[j].u) != d.get(oth[0].u)) can_compress = 1;
        } else {
          dsu d(n);
          for (auto o : oth) d.uni(o.u, o.v);
          set<int> ss;
          for (auto o : oth) ss.insert(d.get(o.u));
          can_compress = (int)ss.size() >= (int)et.size() + 2;
        }

        if (can_compress) {
          any = 1;
          edge nw;
          nw.u = a;
          nw.v = D;
          nw.t = BLACK;
          nw.len = cycle[i].len + cycle[i + 1].len + cycle[i + 2].len;
          nw.cnt = cycle[i].cnt + cycle[i + 1].cnt + cycle[i + 2].cnt;

          cycle.erase(cycle.begin() + i);
          cycle.erase(cycle.begin() + i);
          cycle.erase(cycle.begin() + i);
          cycle.insert(cycle.begin() + i, nw);
          assert(cycle[i].u == cycle[(i - 1 + cycle.size()) % cycle.size()].v);
          assert(cycle[i].v == cycle[i + 1].u);
          i--;
        }
      }
    }
  }

  if (sum > 0) {
    int j = 0;
    while (j < (int)cycle.size() && cycle[j].u != n - 2 && cycle[j].v != n - 2) j++;
    rotate(cycle.begin(), cycle.begin() + j, cycle.end());
  }
  vector<vector<edge>> res;
  vector<edge> cur;
  for (auto o : cycle) {
    if (sum && (o.u >= n - 2 || o.v >= n - 2)) {
      if (!cur.empty()) {
        res.push_back(cur);
        cur.clear();
      }
    } else {
      cur.push_back(o);
    }
  }
  if (!cur.empty()) {
    res.push_back(cur);
    cur.clear();
  }
  return res;
}

void solve(string file) {
  ifstream in(file);
  string s;

  count_paths = 0;
  vector<tedge> ted;
  while (getline(in, s)) {
    stringstream ss;
    ss << s;
    
    string v, u;
    int k;
    char t;
    ss >> v >> u >> k >> t;
    ted.push_back({v, u, k, t});
  }
  auto getPos = [&](string t) {
    ll res = 0;
    for (char c : t) {
      if (c >= '0' && c <= '9') res = 10 * res + (c - '0');
      else res = 0;
    }
    return res;
  };
  vector<string> vct;
  for (auto o : ted) {
    vct.push_back(o.u);
    vct.push_back(o.v);
  }
  sort(vct.begin(), vct.end());
  vct.resize(unique(vct.begin(), vct.end()) - vct.begin());
  int n = vct.size();
  auto getId = [&](string ss) {
    return (int)(lower_bound(vct.begin(), vct.end(), ss) - vct.begin());
  };

  vector<edge> ed;
  for (auto o : ted) {
    edge ced;
    ced.u = getId(o.u);
    ced.v = getId(o.v);
    if (ced.u > ced.v) swap(ced.u, ced.v);
    ced.t = o.t == 'S' ? RED : BLACK;
    ced.len = abs(getPos(o.u) - getPos(o.v));
    if (ced.t == BLACK) ced.len = 0;
    ced.cnt = 1;
    while (o.k--) {
      ed.push_back(ced);
    }
  }

  vector<int> deg(n);
  for (auto o : ed) {
    int coef = o.t == RED ? +1 : -1;
    deg[o.u] += coef;
    deg[o.v] += coef;
  }
  int sumdeg = 0;
  for (auto x : deg) {
    assert(x >= 0);
    sumdeg += x;
  }
  assert(sumdeg % 2 == 0);

  dsu d(n);
  for (auto o : ed) {
    d.uni(o.u, o.v);
  }
  
  vector<vector<edge>> ned(n);
  for (auto o : ed) {
    ned[d.get(o.u)].push_back(o);
  }

  vector<int> lens;
  vector<ll> biglens;
  int cnt_paths = 0;
  for (auto v : ned) {
    auto paths = solve_connected(v);
    for (auto res : paths) {
      cnt_paths++;
      for (auto o : res) {
        if (o.cnt > 0) {
          lens.push_back(o.cnt);
          biglens.push_back(o.len);
        }
      }
    }
  }
  sort(lens.begin(), lens.end());
  sort(biglens.begin(), biglens.end());

  ll bigsum = 0;
  for (auto x : biglens) bigsum += x;
  ll cursum = 0;
  int ci = (int)biglens.size();
  while (cursum * 2 < bigsum) {
    cursum += biglens[--ci];
  }

  double av = 0;
  for (int x : lens) av += x;
  av /= lens.size();

  vector<int> nres;
  for (int x : lens) for (int i = 0; i < x; i++) nres.push_back(x);
  sort(nres.begin(), nres.end());
  int n50 = nres[nres.size() / 2];

  cout.precision(3); cout << fixed;
  /*cout << "solve test " << file << endl;
  cout << "number of edges: " << ed.size() << " -> " << lens.size() << endl;
  cout << "number of original edges in one compressed edge:" << endl;
  cout << "average: " << av << endl;
  cout << "N50: " << n50 << endl;
  cout << "lengths:" << endl;
  cout << "average: " << bigsum * 1.0 / biglens.size() << endl;
  cout << "median: " << biglens[biglens.size() / 2] << endl;
  cout << "N50: " << biglens[ci] << endl;
  cout << "max: " << biglens.back() << endl;
  cout << endl;*/
  cout << bigsum << endl;

  ll initsum = 0;
  for (auto o : ed) initsum += o.len;
  assert(bigsum == initsum);
}

int main(int argc, char* argv[]) {
  for (int i = 1; i < argc; i++) {
    solve(argv[i]);
  }
}
