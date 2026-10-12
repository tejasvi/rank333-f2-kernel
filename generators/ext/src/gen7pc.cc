#include <numeric>
// gen7c: v7 leaf certificates in C++ (gen7.h).  stdin: one leaf per line, "a1,a2,..,an DOM" with the terms as decimal 9-bit
// values and DOM = "all" (the nonzero functionals), "E:e1,e2,.." (X with <X, e> = 0 for every e) or "M:HEX" (a
// 512-bit domain mask).  stdout per leaf:
// "HEX NBITS NODES US" (certificate after finalize, enc_cert bits little-endian as a hex number; BIG past --maxnodes;
// SAT if a decomposition exists).  Options: --K 4 --maxnodes 300000 --deadk 6 --lg (Lemma G hook as run7.py --lg).
// A certificate whose NT/SL counts overflow enc_cert's fields is regenerated with the fit fallback (gen7.h) unless --nofit;
// --fit uses the fallback from the start.  --sat: decompositions become SAT leaves of the BC7L (gen7.h satmode), so a
// SAT leaf gets a NoLift3 certificate for `BC7L.leafSL S7L.liftTest` (the line then has a 6th field: the SAT-leaf count).
#include "gen7p.h"
static long long splitL = 0, splitL1 = 0, split3L1 = 0, split3L2 = 0;
int main(int argc, char** argv) {
  int K = 4, deadk = 6; long long maxnodes = 300000; bool lg = false, shape = false, nofit = false, satm = false; int fitf = 0;
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    if (a == "--K") K = atoi(argv[++i]); else if (a == "--maxnodes") maxnodes = atoll(argv[++i]);
    else if (a == "--deadk") deadk = atoi(argv[++i]); else if (a == "--lg") lg = true; else if (a == "--shape") shape = true;
    else if (a == "--fit") fitf = 1; else if (a == "--nofit") nofit = true; else if (a == "--sat") satm = true;
    else if (a == "--plane") { satm = true; g7::Leaf::planeMode = true; sscanf(argv[++i], "%d,%d,%d", &g7p::PQ[0], &g7p::PQ[1], &g7p::PQ[2]);
      g7p::PTS.clear(); for (int x = 1; x < 8; x++) { int p = 0; for (int j = 0; j < 3; j++) if ((x >> j) & 1) p ^= g7p::PQ[j]; g7p::PTS.push_back(p); } }
    else if (a == "--pk") g7p::K = atoi(argv[++i]);
    else if (a == "--blocks") g7::Leaf::witMode = false;
    else if (a == "--split") splitL = atoll(argv[++i]);
    else if (a == "--split2") { splitL1 = atoll(argv[++i]); splitL = atoll(argv[++i]); }
    else if (a == "--split3") { split3L1 = atoll(argv[++i]); split3L2 = atoll(argv[++i]); }
    else if (a == "--splitB") { g7::gSplitB = atoll(argv[++i]); g7::gSplitBmin = atoll(argv[++i]); g7::gSplitB1 = atoll(argv[++i]); }
    else { fprintf(stderr, "bad arg %s\n", a.c_str()); return 1; }
  }
  g7::T();   // build the tables
  std::string line;
  while (std::getline(std::cin, line)) {
    if (line.empty()) continue;
    std::istringstream ss(line); std::string ts, ds; ss >> ts >> ds;
    int K1 = K, deadk1 = deadk; long long maxnodes1 = maxnodes; bool lg1 = lg;   // per-line overrides: K= deadk= maxnodes= lg=
    for (std::string kv; ss >> kv; ) {
      auto eq = kv.find('='); if (eq == std::string::npos) continue;
      std::string k = kv.substr(0, eq), v = kv.substr(eq + 1);
      if (k == "K") K1 = std::stoi(v); else if (k == "deadk") deadk1 = std::stoi(v); else if (k == "maxnodes") maxnodes1 = std::stoll(v); else if (k == "lg") lg1 = v == "1";
    }
    std::vector<int> terms; { std::stringstream s2(ts); std::string t; while (std::getline(s2, t, ',')) terms.push_back(std::stoi(t)); }
    std::vector<int> dom;
    if (ds == "all") { for (int X = 1; X < 512; X++) dom.push_back(X); }
    else if (ds.rfind("E:", 0) == 0) {
      std::vector<int> E; std::stringstream s2(ds.substr(2)); std::string t; while (std::getline(s2, t, ',')) E.push_back(std::stoi(t));
      for (int X = 1; X < 512; X++) { bool ok = true; for (int e : E) if (__builtin_popcount(X & e) & 1) { ok = false; break; } if (ok) dom.push_back(X); }
    } else if (ds.rfind("M:", 0) == 0) {   // a 512-bit domain mask in hex
      std::string hx = ds.substr(2); int bitpos = 0;
      for (size_t k = hx.size(); k > 0; k--) { int v = std::stoi(hx.substr(k - 1, 1), nullptr, 16); for (int q = 0; q < 4; q++, bitpos++) if (((v >> q) & 1) && bitpos > 0 && bitpos < 512) dom.push_back(bitpos); }
      std::sort(dom.begin(), dom.end());
    } else { fprintf(stderr, "bad dom %s\n", ds.c_str()); return 1; }
    for (int att = fitf; att < 2; att++) {   // att 1: the fit fallback (gen7.h), after a field overflow
    auto t0 = std::chrono::steady_clock::now();
    g7::Leaf L(terms, dom, lg1 && dom.size() == 511);   // run7: Lemma G only on the full domain
    L.fit = att == 1; L.satmode = satm;
    try {
      if (lg1 && dom.size() == 511 && !L.lg) { printf("NONE 0 0 0\n"); fflush(stdout); continue; }   // Delta < 0: no certificate needed
      g7::Cert* c = L.gen(K1, maxnodes1, deadk1);
      long long nodes0 = 0; g7::stats(c, nodes0);
      c = L.finalize(c);
      if (getenv("G7_TREESTAT")) {   // debug: per depth (to 8), the branch nodes' kid counts and kid sizes (bits)
        std::vector<const g7::Cert*> lvl{c};
        for (int d = 0; d < 8 && !lvl.empty(); d++) {
          std::vector<const g7::Cert*> nx; std::vector<long long> ks; long long nk = 0, mxk = 0;
          for (auto* x : lvl) { if (x->sat || x->over) continue; nk++; mxk = std::max<long long>(mxk, x->kids.size()); for (auto* y : x->kids) { ks.push_back(g7::encBits(y)); nx.push_back(y); } }
          std::sort(ks.begin(), ks.end());
          if (!ks.empty()) fprintf(stderr, "TREESTAT d=%d branch=%lld maxkids=%lld kids=%zu bits min=%lld med=%lld p90=%lld max=%lld sum=%lld\n", d, nk, mxk, ks.size(), ks[0], ks[ks.size()/2], ks[ks.size()*9/10], ks.back(), std::accumulate(ks.begin(), ks.end(), 0LL));
          lvl = nx;
        }
      }
      if (split3L1 > 0) {   // sibling ranges: PL.leafSXR main record; parts PL.subMainOKR / PL.forestOK; sub-records PL.subOKL / PL.forestOK
        long long B2 = g7::gSplitB > 0 ? g7::gSplitB : 40000, Bm = g7::gSplitB > 0 ? g7::gSplitBmin : 2000;
        long long B1 = g7::gSplitB1 > 0 ? g7::gSplitB1 : 3000000, Bm1 = std::max(Bm, B2 / 4);
        g7::BW wm; std::vector<g7::RItem> parts;
        g7::encNodeR(wm, c, "", split3L1, B1, Bm1, parts);
        printf("MAIN %s %zu %lld %zu\n", g7::bwHex(wm).c_str(), wm.n, g7::satCount(c), parts.size());
        for (auto& pt : parts) {
          g7::BW wp; std::vector<g7::RItem> subs;
          g7::encItemR(wp, pt, split3L2, B2, Bm, subs);
          printf("PART %s %zu %s %zu %lld %zu\n", g7::itemPath(pt).c_str(), pt.cnt == 1 ? (size_t)0 : pt.cnt, g7::bwHex(wp).c_str(), wp.n, pt.nsat, subs.size());
          for (auto& sb : subs) {
            g7::BW ws; g7::encItemPlain(ws, sb);
            printf("SUB %s %zu %s %zu %lld\n", g7::itemPath(sb).c_str(), sb.cnt == 1 ? (size_t)0 : sb.cnt, g7::bwHex(ws).c_str(), ws.n, sb.nsat);
          }
        }
        printf("END\n"); fflush(stdout); break;
      }
      if (splitL1 > 0) {   // nested: PL.leafSXL main record, PL.subMainOK parts, PL.subOKL sub-records
        g7::BW wm; std::string path; std::vector<g7::SplitPart> parts;
        g7::encSplit1(wm, c, path, splitL1, parts, true);
        printf("MAIN %s %zu %lld %zu\n", g7::bwHex(wm).c_str(), wm.n, g7::satCount(c), parts.size());
        for (auto& pt : parts) {
          g7::BW wp; std::string pp = pt.path; std::vector<g7::SplitSub> subs;
          g7::encSplit(wp, pt.c, pp, splitL, subs, true);
          printf("PART %s %s %zu %lld %zu\n", pt.path.empty() ? "-" : pt.path.c_str(), g7::bwHex(wp).c_str(), wp.n, pt.nsat, subs.size());
          for (auto& sb : subs) { g7::BW ws; g7::enc_cert(ws, sb.c); printf("SUB %s %s %zu %lld\n", sb.path.empty() ? "-" : sb.path.c_str(), g7::bwHex(ws).c_str(), ws.n, sb.nsat); }
        }
        printf("END\n"); fflush(stdout); break;
      }
      if (splitL > 0) {   // PL.leafSXL main record + PL.subOKL sub-records
        g7::BW wm; std::string path; std::vector<g7::SplitSub> subs;
        g7::encSplit(wm, c, path, splitL, subs, true);
        printf("MAIN %s %zu %lld %zu\n", g7::bwHex(wm).c_str(), wm.n, g7::satCount(c), subs.size());
        for (auto& sb : subs) { g7::BW ws; g7::enc_cert(ws, sb.c); printf("SUB %s %s %zu %lld\n", sb.path.empty() ? "-" : sb.path.c_str(), g7::bwHex(ws).c_str(), ws.n, sb.nsat); }
        printf("END\n"); fflush(stdout); break;
      }
      g7::BW w; g7::enc_cert(w, c);
      long long us = std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::steady_clock::now() - t0).count();
      std::string hex; char buf[17];
      for (size_t i = (w.n + 63) / 64; i > 0; i--) { snprintf(buf, sizeof buf, hex.empty() ? "%llx" : "%016llx", (unsigned long long)w.w[i - 1]); if (hex.empty() && w.w[i - 1] == 0) continue; hex += buf; }
      if (hex.empty()) hex = "0";
      if (shape) {   // kid counts of the branch nodes in pre-order (enc_cert order), OVER nodes skipped; bytes, 255 + 2-byte LE escape
        std::string sh; char b2[3];
        std::function<void(const g7::Cert*)> walk = [&](const g7::Cert* x) {
          if (x->over || x->sat) return;
          size_t k = x->kids.size();
          if (k < 255) { snprintf(b2, sizeof b2, "%02x", (unsigned)k); sh += b2; }
          else { if (k > 65535) throw std::runtime_error("kid count over 65535"); snprintf(b2, sizeof b2, "%02x", 255u); sh += b2; snprintf(b2, sizeof b2, "%02x", (unsigned)(k & 255)); sh += b2; snprintf(b2, sizeof b2, "%02x", (unsigned)(k >> 8)); sh += b2; }
          for (auto* y : x->kids) walk(y);
        };
        walk(c);
        printf("%s %zu %lld %lld %s\n", hex.c_str(), w.n, nodes0, us, sh.empty() ? "-" : sh.c_str());
      } else if (g7::Leaf::planeMode) { printf("%s %zu %lld %lld %lld fail=%lld facts=%lld vfree=%lld trans=%lld l3=%lld l3fail=%lld l3uf=%lld l3surv=%lld l3vf=%lld\n", hex.c_str(), w.n, nodes0, us, g7::count_sat(c), g7p::nfail, g7p::nfacts, g7p::nvfree, g7p::ntrans, g7p::nl3, g7p::nl3fail, g7p::nl3uf, g7p::nl3surv, g7p::nl3vf); g7p::nfail = g7p::nfacts = g7p::nvfree = g7p::ntrans = g7p::nsat = 0; g7p::nl3 = g7p::nl3fail = g7p::nl3uf = g7p::nl3surv = g7p::nl3vf = 0; }
      else if (satm) printf("%s %zu %lld %lld %lld\n", hex.c_str(), w.n, nodes0, us, g7::count_sat(c));
      else printf("%s %zu %lld %lld\n", hex.c_str(), w.n, nodes0, us);
    } catch (g7::Big&) { printf("BIG 0 %lld 0\n", L.cnt); }
    catch (g7::Sat&) { printf("SAT 0 0 0\n"); }
    catch (std::runtime_error& e) {
      if (att == 0 && !nofit && std::string(e.what()).find("overflow") != std::string::npos) continue;
      printf("ENC 0 %lld 0\n", L.cnt); fprintf(stderr, "leaf not encodable: %s\n", e.what());
    }
    break;
    }
    fflush(stdout);
  }
  return 0;
}
