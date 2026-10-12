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
int main(int argc, char** argv) {
  int K = 4, deadk = 6, topD = -1; long long maxnodes = 2000000000LL, maxsat = 10368, maxbits = 3000000, L2 = 72, B2 = 40000, BM = 2000;
  std::string subPath, expandFile; bool sub = false; int kexp = 1;
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
