// gen7pd_eqf: gen7pd (distributed generation) over gen7p_eqf.h's equal-first-factor walk (--eqf; gen7pd_eqf.h = gen7pd.h + gen7p_eqf.h).
// gen7pd: distributed generation of one split leaf certificate (s443 EXT tools v4; gen7pd.h).  stdin: one leaf, "a1,..,an DOM"
// as gen7pc (terms as decimal 9-bit values; DOM all | E:e1,.. | M:HEX).  Options as gen7pc (--plane Q --pk K --maxnodes M --K
// --deadk), and one mode:
//   --top D [--expand FILE [--kexpand K]]  the tree down to depth D (and K levels below any path of FILE, one per line, and its
//                             ancestors), every
//                             unexpanded live node an external subtree item; finalized by attach only.  Output:
//                               MAIN <hex> <nbits> <nsat in the top> <number of items>
//                               EXT <path>            (one per item, in the main record's marker order = DFS order)
//                               END
//   --sub PATH [--maxsat L1] [--maxbits B1] [--split3part L2 B2 BMIN]
//                             the subtree at PATH (its state replayed from the path's steps), finalized (attach + hoist), as
//                             gen7pc --split3's PART block of the subtree item (PATH, 0): the part record with sub-records of at
//                             most L2 SAT leaves and B2 bits (BMIN as gen7pc's --splitB):
//                               PART <PATH> 0 <hex> <nbits> <nsat> <nsub>
//                               SUB <path> <count> <hex> <nbits> <nsat>
//                               END
//                             or TOOBIG <nsat> <bits> when the subtree has more than L1 SAT leaves or B1 bits (or passes maxnodes).
// A certificate whose fields overflow is regenerated with the fit fallback, as gen7pc.  The top's MAIN plus the parts of all its
// items (in EXT order) is exactly gen7pc --split3's output format, so S4.PLDrvR's modules check it unchanged.
#include <numeric>
#include "gen7pd_eqf.h"
// --sub PATH --dump FILE: the finalized subtree, serialized (preorder; N t sym cdir nNT NT.. nSL SL.. nkids | S swn words.. | O X skip);
// --top D ... --assemble DIR: the top with every ext node replaced by DIR/<sha-free name>.dump (gensplit names them by item order),
// then gen7pc_eqf's --split3 encoding of the whole tree (encNodeR with the part budgets; MAIN keeps a0): parallel generation, and
// gen7pc's grouped parts and small main record.
static void dumpCert(FILE* f, const g7::Cert* c) {
  if (c->sat) { fprintf(f, "S %zu", c->swn); for (size_t i = 0; i < (c->swn + 63) / 64; i++) fprintf(f, " %llx", (unsigned long long)c->sw[i]); fputc('\n', f); return; }
  if (c->over) { fprintf(f, "O %d %d\n", c->X, c->skip ? 1 : 0); return; }
  if (c->ext) throw std::runtime_error("dump: ext node");
  fprintf(f, "N %d %d %d %zu", c->t, c->sym ? 1 : 0, c->cdir ? 1 : 0, c->NT.size()); for (int X : c->NT) fprintf(f, " %d", X);
  fprintf(f, " %zu", c->SL.size()); for (int X : c->SL) fprintf(f, " %d", X);
  fprintf(f, " %zu\n", c->kids.size());
  for (auto* k : c->kids) dumpCert(f, k);
}
static g7::Cert* loadCert(FILE* f, g7::Leaf& L) {
  char ty[4]; if (fscanf(f, "%3s", ty) != 1) throw std::runtime_error("load: eof");
  g7::Cert* c = L.mk();
  if (ty[0] == 'S') { c->sat = true; size_t n; if (fscanf(f, "%zu", &n) != 1) throw std::runtime_error("load S"); c->swn = n; c->sw.resize((n + 63) / 64);
    for (auto& w : c->sw) { unsigned long long v; if (fscanf(f, "%llx", &v) != 1) throw std::runtime_error("load S w"); w = v; } return c; }
  if (ty[0] == 'O') { int x, sk; if (fscanf(f, "%d %d", &x, &sk) != 2) throw std::runtime_error("load O"); c->over = true; c->X = x; c->skip = sk != 0; return c; }
  int t, sy, cd; size_t n; if (fscanf(f, "%d %d %d %zu", &t, &sy, &cd, &n) != 4) throw std::runtime_error("load N");
  c->t = t; c->sym = sy; c->cdir = cd; c->NT.resize(n); for (auto& x : c->NT) if (fscanf(f, "%d", &x) != 1) throw std::runtime_error("load NT");
  if (fscanf(f, "%zu", &n) != 1) throw std::runtime_error("load nSL"); c->SL.resize(n); for (auto& x : c->SL) if (fscanf(f, "%d", &x) != 1) throw std::runtime_error("load SL");
  if (fscanf(f, "%zu", &n) != 1) throw std::runtime_error("load nkids"); c->kids.resize(n); for (auto& k : c->kids) k = loadCert(f, L);
  return c;
}
static void splice(g7::Cert* c, g7::Leaf& L, const std::string& dir, size_t& idx) {
  if (c->sat || c->over || c->ext) return;
  for (auto& k : c->kids) {
    if (k->ext) {
      std::string fn = dir + "/" + std::to_string(idx++) + ".dump";
      FILE* f = fopen(fn.c_str(), "r"); if (!f) throw std::runtime_error("assemble: no " + fn);
      k = loadCert(f, L); fclose(f);
    } else splice(k, L, dir, idx);
  }
}
// --top --group FILE ("<first ext path> <cnt>" per line): a run of cnt consecutive ext siblings starting at that path becomes ONE range
// item (marker with count cnt, as gen7pc --split3's encRunKids writes a range; its PART is the cnt subtrees' records in turn, built by
// gensplit from the single-subtree PARTs). Node and skip-run encoding as enc_cert / encKidsPlain.
static void encTopG(g7::BW& w, const g7::Cert* c, const std::string& path, const std::map<std::string, size_t>& groups,
                    std::vector<std::pair<std::string, size_t>>& exts) {
  if (c->ext) { g7::putMarker(w, 0); exts.push_back({path, 1}); return; }
  if (c->sat || c->over) { g7::enc_cert(w, c); return; }
  w.put(1, 1); w.put(c->t, 5); w.put(c->sym, 1); w.put(c->cdir, 1);
  w.put(c->NT.size(), 4); for (int X : c->NT) w.put(X, 9);
  w.put(c->SL.size(), 3); for (int X : c->SL) w.put(X, 9);
  std::string sp = g7::stepPrefix(c);
  size_t run = 0;
  for (size_t j = 0; j < c->kids.size(); j++) {
    const g7::Cert* k = c->kids[j];
    if (k->skip) { run++; continue; }
    g7::putSkip(w, run); run = 0;
    std::string kp = g7::childPath(path, sp, j);
    if (k->ext) {
      auto it = groups.find(kp); size_t cnt = it == groups.end() ? 1 : it->second;
      if (cnt < 1 || cnt > 32767 || j + cnt > c->kids.size()) throw std::runtime_error("group: bad count at " + kp);
      for (size_t q = 1; q < cnt; q++) if (!c->kids[j + q]->ext || c->kids[j + q]->skip) throw std::runtime_error("group: not an ext run at " + kp);
      g7::putMarker(w, cnt == 1 ? 0 : cnt); exts.push_back({kp, cnt}); j += cnt - 1; continue;
    }
    encTopG(w, k, kp, groups, exts);
  }
  g7::putSkip(w, run);
}
int main(int argc, char** argv) {
  int K = 4, deadk = 6, topD = -1; long long maxnodes = 2000000000LL, maxsat = 10368, maxbits = 3000000, L2 = 72, B2 = 40000, BM = 2000;
  std::string subPath, expandFile, groupFile, dumpFile, asmDir; bool sub = false; int kexp = 1; long long s3L1 = 10368, s3L2 = 72;
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    if (a == "--K") K = atoi(argv[++i]); else if (a == "--maxnodes") maxnodes = atoll(argv[++i]);
    else if (a == "--deadk") deadk = atoi(argv[++i]);
    else if (a == "--plane") { g7::Leaf::planeMode = true; sscanf(argv[++i], "%d,%d,%d", &g7p::PQ[0], &g7p::PQ[1], &g7p::PQ[2]);
      g7p::PTS.clear(); for (int x = 1; x < 8; x++) { int p = 0; for (int j = 0; j < 3; j++) if ((x >> j) & 1) p ^= g7p::PQ[j]; g7p::PTS.push_back(p); } }
    else if (a == "--pk") g7p::K = atoi(argv[++i]);
    else if (a == "--top") topD = atoi(argv[++i]);
    else if (a == "--expand") expandFile = argv[++i];
    else if (a == "--kexpand") kexp = atoi(argv[++i]);
    else if (a == "--sub") { sub = true; subPath = argv[++i]; }
    else if (a == "--maxsat") maxsat = atoll(argv[++i]);
    else if (a == "--maxbits") maxbits = atoll(argv[++i]);
    else if (a == "--split3part") { L2 = atoll(argv[++i]); B2 = atoll(argv[++i]); BM = atoll(argv[++i]); }
    else if (a == "--eqf") { g7::Leaf::eqOn = true; g7::gEqOn = true; }
    else if (a == "--group") groupFile = argv[++i];
    else if (a == "--dump") dumpFile = argv[++i];
    else if (a == "--assemble") asmDir = argv[++i];
    else if (a == "--split3") { s3L1 = atoll(argv[++i]); s3L2 = atoll(argv[++i]); }
    else if (a == "--splitB") { g7::gSplitB = atoll(argv[++i]); g7::gSplitBmin = atoll(argv[++i]); g7::gSplitB1 = atoll(argv[++i]); }
    else if (a == "--eqf-any-root") g7::Leaf::eqUnique = false;
    else { fprintf(stderr, "bad arg %s\n", a.c_str()); return 1; }
  }
  if ((topD < 0) == !sub) { fprintf(stderr, "exactly one of --top / --sub\n"); return 1; }
  g7::T();
  std::string line;
  if (!std::getline(std::cin, line)) return 1;
  std::istringstream ss(line); std::string ts, ds; ss >> ts >> ds;
  std::vector<int> terms; { std::stringstream s2(ts); std::string t; while (std::getline(s2, t, ',')) terms.push_back(std::stoi(t)); }
  std::vector<int> dom;
  if (ds == "all") { for (int X = 1; X < 512; X++) dom.push_back(X); }
  else if (ds.rfind("E:", 0) == 0) {
    std::vector<int> E; std::stringstream s2(ds.substr(2)); std::string t; while (std::getline(s2, t, ',')) E.push_back(std::stoi(t));
    for (int X = 1; X < 512; X++) { bool ok = true; for (int e : E) if (__builtin_popcount(X & e) & 1) { ok = false; break; } if (ok) dom.push_back(X); }
  } else if (ds.rfind("M:", 0) == 0) {
    std::string hx = ds.substr(2); int bitpos = 0;
    for (size_t k = hx.size(); k > 0; k--) { int v = std::stoi(hx.substr(k - 1, 1), nullptr, 16); for (int q = 0; q < 4; q++, bitpos++) if (((v >> q) & 1) && bitpos > 0 && bitpos < 512) dom.push_back(bitpos); }
    std::sort(dom.begin(), dom.end());
  } else { fprintf(stderr, "bad dom %s\n", ds.c_str()); return 1; }
  std::set<std::string> expand;
  if (!expandFile.empty()) { std::ifstream f(expandFile); std::string p; while (std::getline(f, p)) if (!p.empty()) expand.insert(p); }
  for (int att = 0; att < 2; att++) {   // att 1: the fit fallback after a field overflow
    g7::Leaf L(terms, dom, false);
    L.fit = att == 1; L.satmode = true;
    try {
      if (topD >= 0) {
        L.maxdepth = topD; L.expand = expand; L.kexpand = kexp;
        g7::Cert* c = L.gen_top(K, maxnodes, deadk);
        if (!asmDir.empty()) {      // assembled: the whole tree, gen7pc_eqf's --split3 encoding
          size_t idx = 0; splice(c, L, asmDir, idx);
          long long B2s = g7::gSplitB > 0 ? g7::gSplitB : 40000, Bms = g7::gSplitB > 0 ? g7::gSplitBmin : 2000;
          long long B1s = g7::gSplitB1 > 0 ? g7::gSplitB1 : 3000000, Bm1 = std::max(Bms, B2s / 4);
          g7::BW wm; std::vector<g7::RItem> parts;
          g7::encNodeR(wm, c, "", s3L1, B1s, Bm1, parts);
          if (g7::Leaf::eqOn) printf("MAIN %s %zu %lld %zu %d\n", g7::bwHex(wm).c_str(), wm.n, g7::satCount(c), parts.size(), L.eqA0 < 0 ? 0 : L.eqA0);
          else printf("MAIN %s %zu %lld %zu\n", g7::bwHex(wm).c_str(), wm.n, g7::satCount(c), parts.size());
          for (auto& pt : parts) {
            g7::BW wp; std::vector<g7::RItem> subs;
            g7::encItemR(wp, pt, s3L2, B2s, Bms, subs);
            printf("PART %s %zu %s %zu %lld %zu\n", g7::itemPath(pt).c_str(), pt.cnt == 1 ? (size_t)0 : pt.cnt, g7::bwHex(wp).c_str(), wp.n, pt.nsat, subs.size());
            for (auto& sb : subs) {
              g7::BW ws; g7::encItemPlain(ws, sb);
              printf("SUB %s %zu %s %zu %lld\n", g7::itemPath(sb).c_str(), sb.cnt == 1 ? (size_t)0 : sb.cnt, g7::bwHex(ws).c_str(), ws.n, sb.nsat);
            }
          }
          printf("END\n"); fflush(stdout);
          return 0;
        }
        if (!groupFile.empty()) {   // grouped top: range markers for the listed ext runs
          std::map<std::string, size_t> groups;
          { std::ifstream f(groupFile); std::string p; size_t n; while (f >> p >> n) groups[p] = n; }
          g7::BW wg; std::vector<std::pair<std::string, size_t>> gx;
          encTopG(wg, c, std::string(), groups, gx);
          std::string out = "MAIN " + g7::bwHex(wg) + " " + std::to_string(wg.n) + " " + std::to_string(g7::satCount(c)) + " " + std::to_string(gx.size())
                            + (g7::Leaf::eqOn ? " " + std::to_string(L.eqA0 < 0 ? 0 : L.eqA0) : std::string()) + "\n";
          for (auto& [p, n] : gx) out += "EXT " + p + " " + std::to_string(n) + "\n";
          out += "END\n";
          fputs(out.c_str(), stdout);
          fflush(stdout);
          return 0;
        }
        g7::BW w; g7::enc_cert(w, c);
        std::vector<std::string> exts;
        std::function<void(const g7::Cert*, const std::string&)> walk = [&](const g7::Cert* x, const std::string& p) {
          if (x->ext) { exts.push_back(p); return; }
          if (x->sat || x->over) return;
          std::string sp = g7::stepPrefix(x);
          for (size_t i = 0; i < x->kids.size(); i++) walk(x->kids[i], g7::childPath(p, sp, i));
        };
        walk(c, std::string());
        std::string out = "MAIN " + g7::bwHex(w) + " " + std::to_string(w.n) + " " + std::to_string(g7::satCount(c)) + " " + std::to_string(exts.size())
                          + (g7::Leaf::eqOn ? " " + std::to_string(L.eqA0 < 0 ? 0 : L.eqA0) : std::string()) + "\n";
        for (auto& p : exts) out += "EXT " + p + "\n";
        out += "END\n";
        fputs(out.c_str(), stdout);
      } else {
        L.maxsat = maxsat;
        g7::Cert* c = L.gen_sub(subPath, K, maxnodes, deadk);
        long long ns = g7::satCount(c), nb = g7::encBits(c);
        if (ns > maxsat || nb > maxbits) { printf("TOOBIG %lld %lld\n", ns, nb); return 0; }
        if (!dumpFile.empty()) {    // the finalized subtree for --assemble
          FILE* f = fopen((dumpFile + ".tmp").c_str(), "w"); dumpCert(f, c); fclose(f);
          std::rename((dumpFile + ".tmp").c_str(), dumpFile.c_str());
          printf("DUMPED %lld %lld\n", ns, nb); fflush(stdout); return 0;
        }
        // the item (subPath, 0): parent path, the parent's step prefix and the kid index from the last step
        size_t cut = subPath.rfind(';');
        std::string pn = cut == std::string::npos ? std::string() : subPath.substr(0, cut);
        std::string last = cut == std::string::npos ? subPath : subPath.substr(cut + 1);
        size_t k = last.rfind(':');
        g7::RItem it{pn, last.substr(0, k + 1), (size_t)std::stoul(last.substr(k + 1)), 1, {c}, ns, nb};
        g7::BW wp; std::vector<g7::RItem> subs;
        g7::encItemR(wp, it, L2, B2, BM, subs);
        std::string out = "PART " + g7::itemPath(it) + " 0 " + g7::bwHex(wp) + " " + std::to_string(wp.n) + " " + std::to_string(ns) + " " + std::to_string(subs.size()) + "\n";
        for (auto& sb : subs) {
          g7::BW ws; g7::encItemPlain(ws, sb);
          out += "SUB " + g7::itemPath(sb) + " " + std::to_string(sb.cnt == 1 ? (size_t)0 : sb.cnt) + " " + g7::bwHex(ws) + " " + std::to_string(ws.n) + " " + std::to_string(sb.nsat) + "\n";
        }
        out += "END\n";
        if (g7::itemPath(it) != subPath) { fprintf(stderr, "item path mismatch\n"); return 2; }
        fputs(out.c_str(), stdout);
      }
    } catch (g7::TooBig&) { printf("TOOBIG %lld -1\n", L.nsatgen); }
    catch (g7::Big&) { printf("TOOBIG -1 -1\n"); }
    catch (g7::Sat&) { printf("SAT\n"); }
    catch (std::runtime_error& e) {
      if (att == 0 && std::string(e.what()).find("overflow") != std::string::npos) continue;
      printf("ENC %s\n", e.what());
    }
    break;
  }
  fflush(stdout);
  return 0;
}
