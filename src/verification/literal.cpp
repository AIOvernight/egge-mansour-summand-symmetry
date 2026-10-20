#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <numeric>
#include <omp.h>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using U = uint64_t;
struct Pattern {
  vector<int> a, p;
  string name;
  int offset;
};
vector<Pattern> pats;
int width = 0, N;
void add(vector<int> a) {
  Pattern p;
  p.a = a;
  p.offset = width;
  width += a.size() + 1;
  int v = 0;
  for (int z : a) {
    for (int t = z; t; t--)
      p.p.push_back(v + t);
    v += z;
  }
  for (int z : a) {
    if (!p.name.empty())
      p.name += '-';
    p.name += to_string(z);
  }
  pats.push_back(p);
}
void comps(int rem, vector<int> &a) {
  if (!a.empty())
    add(a);
  for (int x = 1; x <= rem; x++) {
    a.push_back(x);
    comps(rem - x, a);
    a.pop_back();
  }
}
void setup(string mode) {
  if (mode == "A") {
    vector<int> a;
    comps(8, a);
  } else {
    for (vector<int> a : vector<vector<int>>{{1, 2, 3},
                                             {1, 1, 3},
                                             {1, 3, 3},
                                             {2, 3, 4},
                                             {1, 2, 2, 3},
                                             {1, 1, 1, 2}}) {
      sort(a.begin(), a.end());
      do {
        add(a);
      } while (next_permutation(a.begin(), a.end()));
    }
  }
}
// Independent generic classical-pattern detector: compare every selected pair.
bool generic(const vector<int> &p, const vector<int> &q) {
  int n = p.size(), m = q.size();
  vector<int> idx(m);
  function<bool(int, int)> go = [&](int t, int st) {
    if (t == m)
      return true;
    for (int j = st; j <= n - (m - t); j++) {
      bool ok = true;
      for (int i = 0; i < t; i++)
        if ((p[idx[i]] < p[j]) != (q[i] < q[t])) {
          ok = false;
          break;
        }
      if (ok) {
        idx[t] = j;
        if (go(t + 1, j + 1))
          return true;
      }
    }
    return false;
  };
  return go(0, 0);
}
bool bad3412(const vector<int> &p) {
  int n = p.size();
  for (int a = 0; a < n; a++)
    for (int b = a + 1; b < n; b++)
      for (int c = b + 1; c < n; c++)
        for (int d = c + 1; d < n; d++)
          if (p[c] < p[d] && p[d] < p[a] && p[a] < p[b])
            return true;
  return false;
}
struct Forest {
  vector<uint8_t> t;
  int h = 0;
  Forest() : t(width) {
    for (auto &p : pats)
      for (int i = 0; i <= (int)p.a.size(); i++)
        t[p.offset + i] = i;
  }
};
// A direct sum greedily consumes whole layers. A wrapped irreducible component
// can contain >=2 layers only inside; its longest decreasing subsequence
// gains 2.
Forest atom(const Forest &in, bool fixed) {
  Forest out = in;
  out.h = fixed ? 1 : in.h + 2;
  for (auto &p : pats)
    for (int i = 0; i < (int)p.a.size(); i++)
      if (p.a[i] <= out.h)
        out.t[p.offset + i] = max<int>(out.t[p.offset + i], i + 1);
  return out;
}
Forest append(const Forest &a, const Forest &b) {
  Forest z = a;
  z.h = max(a.h, b.h);
  for (auto &p : pats)
    for (int i = 0; i < (int)p.a.size(); i++)
      z.t[p.offset + i] = b.t[p.offset + a.t[p.offset + i]];
  return z;
}
Forest parse(const vector<int> &p, int l, int r) {
  Forest z;
  while (l < r) {
    if (p[l] == l + 1) {
      z = append(z, atom(Forest(), true));
      l++;
    } else {
      int j = p[l] - 1;
      z = append(z, atom(parse(p, l + 1, j), false));
      l = j + 1;
    }
  }
  return z;
}
void selftest() {
  for (int n = 0; n <= 10; n++) {
    vector<int> p(n);
    U tel = 0, mot = 0;
    vector<U> by(n / 2 + 1);
    function<void(int, int)> rec = [&](int i, int r) {
      while (i < n && p[i])
        i++;
      if (i == n) {
        tel++;
        if (bad3412(p))
          return;
        mot++;
        by[r]++;
        auto f = parse(p, 0, n);
        if (n <= 10)
          for (auto &q : pats) {
            bool fast = f.t[q.offset] == q.a.size();
            if (fast != generic(p, q.p))
              throw runtime_error("detector disagreement " + q.name);
          }
        return;
      }
      p[i] = i + 1;
      rec(i + 1, r);
      p[i] = 0;
      for (int j = i + 1; j < n; j++)
        if (!p[j]) {
          p[i] = j + 1;
          p[j] = i + 1;
          rec(i + 1, r + 1);
          p[i] = p[j] = 0;
        }
    };
    rec(0, 0);
    cout << "control," << n << "," << tel << "," << mot << "\n";
    U expected[] = {1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188};
    U telephone[] = {1, 1, 2, 4, 10, 26, 76, 232, 764, 2620, 9496};
    if (mot != expected[n] || tel != telephone[n])
      throw runtime_error("total disagreement");
  }
  cout << "SELFTEST PASS\n";
}
struct State {
  vector<Forest> stack;
  int pos = 0, r = 0;
  State() { stack.emplace_back(); }
};
void nexts(const State &s, vector<State> &out) {
  int dep = s.stack.size() - 1, remain = N - s.pos;
  if (remain <= 0)
    return;
  if (remain > dep) {
    State z = s;
    z.pos++;
    z.stack.back() = append(z.stack.back(), atom(Forest(), true));
    out.push_back(move(z));
  }
  if (remain >= dep + 2) {
    State z = s;
    z.pos++;
    z.stack.emplace_back();
    out.push_back(move(z));
  }
  if (dep) {
    State z = s;
    z.pos++;
    z.r++;
    Forest at = atom(z.stack.back(), false);
    z.stack.pop_back();
    z.stack.back() = append(z.stack.back(), at);
    out.push_back(move(z));
  }
}
void enumerate(string mode, int maxn, string path) {
  ofstream csv(path);
  csv << "mode,pattern,n,r,count\n";
  for (N = 0; N <= maxn; N++) {
    auto start = chrono::steady_clock::now();
    vector<State> front(1);
    int split = min(N, 9);
    for (int d = 0; d < split; d++) {
      vector<State> out;
      for (auto &s : front)
        nexts(s, out);
      front = move(out);
    }
    int nr = N / 2 + 1;
    vector<vector<U>> threadcounts(16, vector<U>(pats.size() * nr));
    vector<vector<U>> totals(16, vector<U>(nr));
#pragma omp parallel for schedule(dynamic, 1) num_threads(16)
    for (size_t j = 0; j < front.size(); j++) {
      int tid = omp_get_thread_num();
      auto &counts = threadcounts[tid];
      auto &total = totals[tid];
      function<void(const State &)> rec = [&](const State &s) {
        if (s.pos == N) {
          if (s.stack.size() != 1)
            return;
          total[s.r]++;
          auto &t = s.stack[0].t;
          for (int k = 0; k < (int)pats.size(); k++)
            if (t[pats[k].offset] < pats[k].a.size())
              counts[k * nr + s.r]++;
          return;
        }
        vector<State> out;
        nexts(s, out);
        for (auto &z : out)
          rec(z);
      };
      rec(front[j]);
    }
    vector<U> sum(pats.size() * nr), tot(nr);
    for (int t = 0; t < 16; t++) {
      for (int k = 0; k < (int)sum.size(); k++)
        sum[k] += threadcounts[t][k];
      for (int r = 0; r < nr; r++)
        tot[r] += totals[t][r];
    }
    for (int r = 0; r < nr; r++) {
      U bin = 1;
      for (int j = 1; j <= 2 * r; j++)
        bin = bin * (N - j + 1) / j;
      U cat = 1;
      for (int j = 0; j < r; j++)
        cat = cat * 2 * (2 * j + 1) / (j + 2);
      if (tot[r] != bin * cat)
        throw runtime_error("Motzkin coefficient disagreement");
    }
    map<vector<int>, vector<U>> orders;
    for (int k = 0; k < (int)pats.size(); k++) {
      auto key = pats[k].a;
      sort(key.begin(), key.end());
      vector<U> v(sum.begin() + k * nr, sum.begin() + (k + 1) * nr);
      if (orders.count(key) && orders[key] != v)
        throw runtime_error("order disagreement");
      orders[key] = v;
      for (int r = 0; r < nr; r++)
        csv << mode << "," << pats[k].name << "," << N << "," << r << ","
            << v[r] << "\n";
    }
    csv.flush();
    double sec =
        chrono::duration<double>(chrono::steady_clock::now() - start).count();
    cout << "n=" << N << " objects=" << accumulate(tot.begin(), tot.end(), U(0))
         << " patterns=" << pats.size() << " seconds=" << sec << endl;
  }
}
// General involutions: no structural restriction is used while generating.
void general(int maxn, string path) {
  ofstream csv(path);
  csv << "mode,pattern,n,r,count\n";
  U prev2 = 1, prev = 1;
  for (int n = 0; n <= maxn; n++) {
    auto start = chrono::steady_clock::now();
    int nr = n / 2 + 1;
    vector<vector<int>> front(1, vector<int>(n));
    for (int depth = 0; depth < min(n, 3); depth++) {
      vector<vector<int>> out;
      for (auto p : front) {
        int i = 0;
        while (i < n && p[i])
          i++;
        if (i == n) {
          out.push_back(p);
          continue;
        }
        p[i] = i + 1;
        out.push_back(p);
        p[i] = 0;
        for (int j = i + 1; j < n; j++)
          if (!p[j]) {
            p[i] = j + 1;
            p[j] = i + 1;
            out.push_back(p);
            p[i] = p[j] = 0;
          }
      }
      front = move(out);
    }
    vector<vector<U>> tc(16, vector<U>(pats.size() * nr));
    vector<U> tel(16), mot(16);
#pragma omp parallel for schedule(dynamic, 1) num_threads(16)
    for (size_t z = 0; z < front.size(); z++) {
      int tid = omp_get_thread_num();
      auto p = front[z];
      auto &count = tc[tid];
      function<void(int, int)> rec = [&](int i, int r) {
        while (i < n && p[i])
          i++;
        if (i == n) {
          tel[tid]++;
          if (bad3412(p))
            return;
          mot[tid]++;
          auto f = parse(p, 0, n);
          for (int k = 0; k < (int)pats.size(); k++)
            if (f.t[pats[k].offset] < pats[k].a.size())
              count[k * nr + r]++;
          return;
        }
        p[i] = i + 1;
        rec(i + 1, r);
        p[i] = 0;
        for (int j = i + 1; j < n; j++)
          if (!p[j]) {
            p[i] = j + 1;
            p[j] = i + 1;
            rec(i + 1, r + 1);
            p[i] = p[j] = 0;
          }
      };
      int r = 0;
      for (int i = 0; i < n; i++)
        if (p[i] > i + 1)
          r++;
      rec(0, r);
    }
    U telephone = accumulate(tel.begin(), tel.end(), U(0)),
      expected = n < 2 ? 1 : prev + (n - 1) * prev2;
    if (telephone != expected)
      throw runtime_error("telephone disagreement");
    if (n >= 2) {
      prev2 = prev;
      prev = expected;
    }
    vector<U> sum(pats.size() * nr);
    for (auto &v : tc)
      for (int k = 0; k < (int)v.size(); k++)
        sum[k] += v[k];
    for (int k = 0; k < (int)pats.size(); k++)
      for (int r = 0; r < nr; r++)
        csv << "G," << pats[k].name << "," << n << "," << r << ","
            << sum[k * nr + r] << "\n";
    csv.flush();
    cout
        << "n=" << n << " telephone=" << telephone
        << " avoiding=" << accumulate(mot.begin(), mot.end(), U(0))
        << " seconds="
        << chrono::duration<double>(chrono::steady_clock::now() - start).count()
        << endl;
  }
}
int main(int argc, char **argv) {
  try {
    string mode = argc > 1 ? argv[1] : "B";
    setup(mode == "selftest" || mode == "G" ? "A" : mode);
    if (mode == "selftest") {
      vector<int> a{2, 3, 4};
      do {
        add(a);
      } while (next_permutation(a.begin(), a.end()));
      selftest();
    } else {
      if (argc < 4)
        throw runtime_error(
            "usage: literal A|B maxn output.csv; literal selftest");
      if (mode == "G")
        general(stoi(argv[2]), argv[3]);
      else
        enumerate(mode, stoi(argv[2]), argv[3]);
    }
  } catch (exception &e) {
    cerr << e.what() << endl;
    return 1;
  }
}
