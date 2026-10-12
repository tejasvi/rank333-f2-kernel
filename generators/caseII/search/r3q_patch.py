#!/usr/bin/env python3
"""r3q_patch.py BASE_R3.cc BLOCK.cc OUT.cc: prof7R3q = prof7R3 (BASE) + the item-queue client of prof7L92/L93 + per-item certificate segments
(r22/lean/rerun/r3/QUEUE.md).  Anchored edits, each asserted unique, so a newer R3 batch can be patched again; BLOCK.cc replaces R3's
frontier driver block (from `if(JOURNALF){ gJF=fopen(JOURNALF,"a");` to `return 0; }`)."""
import sys, hashlib
base,blockf,outf=sys.argv[1:4]
s=open(base).read()
R3BASE=hashlib.md5(s.encode()).hexdigest()[:12]   # the R3 source merged: part of the compat fingerprint (no mixing of builds in one queue)
def rep(old,new,cnt=1):
    global s
    n=s.count(old)
    if n!=cnt: sys.exit('anchor %r found %d times (want %d)'%(old[:90],n,cnt))
    s=s.replace(old,new)

HEADER='''// prof7R3q = prof7R3 + the item queue of prof7L92 / prof7L93 (r22/xq/DESIGN.md) + per-item certificate segments (r22/lean/rerun/r3/QUEUE.md).
// The search, the --pcert stream of a run without hand-offs, the journal and its fingerprint are prof7R3's.  New:
//  - Items (J job root, P piece, Q range) as in prof7L92: GIVE -> hand-off of queued pieces (with the donor's dead mask), W -> import,
//    spill (spill file, SIGUSR1, SIGTERM while connected, the server's SPILL) -> explored counts + open items, atomic SP message.
//  - Stream (QUEUE.md 2): an exported piece is the donation R3 already writes (DON); a re-leased item writes DON at its earlier child
//    items and never adds, donates or enters them; a spill writes 2C RNG l at each interrupted node (no END there), and the range
//    item's runner writes a kind-3 segment (header + u16 l + u16 p): a copy of the node's data records (VROWS, XROWS, XPN; no NODE,
//    no OPEN), the node's child records from l on (delta base p), END.
//  - Item segments (QUEUE.md 3): at completion (and at a spill) the unit's canonical own part (local pieces, SKR, SKP inlined; DON of
//    queue items and RNG kept) goes to --xqseg (default <pcert>.xq) with its sha256; the report names file:offset:length:sha256.
//  - Compat fingerprint (pairs producers and consumers): search options and every certificate option (--pcxp, --pcexp5, --pcfk*,
//    --xpkinds, ...), pcert and cert mode; only launch-specific options and the frontier are left out.
//  - Journals (read and written) for list jobs only; imported items never use them.
'''
s=HEADER+s

# includes
rep('#include <sys/mman.h>\n','''#include <sys/mman.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <netdb.h>
#include <poll.h>
#include <fcntl.h>
#include <sys/stat.h>
#include "xq_r3.h"   // prof7R3q: sha256, record walker, item assembler
#define R3Q_BASE "'''+R3BASE+'''"   // md5 of the merged prof7R3.cc (r3q_patch.py)
static std::string gRecipeSha;   // sha256 of --xqrecipe's flags (empty without it)
static std::string gCompatExtra;   // the effective generator parameters R3's search fingerprint mixes (batch 5: pcnorep node limit, xp2 incl. P2_* from the environment)
''')

# Job struct: range start and imported-root flag (R3 already has the donor's dead mask dinh and, batch 12, its witness rows win)
rep('static std::mutex qmu; static std::condition_variable qcv; struct Job { std::vector<int> seq; double w; int ix=-1; std::array<uint64_t,8> dinh{}; std::vector<int32_t> win; };',
    '// prof7R3q: Job.rs = first child label of a range item, Job.root = an imported item\'s own root\nstatic std::mutex qmu; static std::condition_variable qcv; struct Job { std::vector<int> seq; double w; int ix=-1; std::array<uint64_t,8> dinh{}; std::vector<int32_t> win; int rs=-1; bool root=false; };')

# globals after the Job line
anchor_job='int rs=-1; bool root=false; };'
i=s.index(anchor_job); j=s.index('\n',i)+1
GLOB='''// prof7R3q: item queue (--xq) and spill (prof7L92); units 0..gNF-1 are the list jobs, gNF..gNU-1 imported item slots.
static const char* XQADDR=nullptr; static const char* XQNAMEO=nullptr; static const char* XQPOOLO=nullptr; static const char* XQOUTP=nullptr; static const char* XQSTOPF=nullptr; static const char* XQSEGP=nullptr; static const char* XQRECIPE=nullptr; static int XQPUNCH=-1; static const char* XQRECOVER=nullptr; static const char* XQPAUSE=nullptr;   // --xqpause FILE: no new items while FILE exists (checkd's backpressure)   // --xqrecipe FILE: the recipe's flags (sha256 into compat); --xqpunch: free pcert blocks of finished units (default: helpers)
static const char* SPILLF=nullptr; static const char* SPILLOUT=nullptr; static bool XQEXPORT=true, XQIMPORT=true, XQHELPER=false, XQSPILLTERM=true;
static double XQLINGER=0, XQTERMWAIT=20.0, XQDOWN=900.0; static int XQMAXD=99, XQKEEP=4, XQSLOTS=0, SPILLD=19; static FILE* XOUT=nullptr;
static long long XQCAP=0, XQCAPB=0; static int XQCAPD=-1; static std::atomic<long long> gXsplit{0};   // --xqcap N [--xqcapd D]: an imported unit whose own part reaches N nodes is split at its open nodes of depth <= D (default --spilld); --xqcapb MB: or its record bytes reach MB
static std::atomic<int> gSpill{0}; static volatile std::sig_atomic_t gUsr1=0; static void onUsr1(int){ gUsr1=1; }
static unsigned long long gOptFP=0, gCompat=0; static size_t gNF=0, gNU=0; static std::mutex gRm;
struct SpillRec { int u; std::vector<int> seq; int l; int p; std::array<uint64_t,8> D; std::vector<int32_t> win; };   // node prefix, first child label not explored, delta base, dead mask inherited by the node, its witness rows (--pcwit)
struct XUnit {   // mutable fields under gRm
  int kind=0; long long item=0; int ix=-1; std::vector<int> seq; int rs=-1, rp=-1;   // imported: kind P/Q/J, server id, job index, prefix, range start and delta base (labels)
  std::array<uint64_t,8> din{};   // imported: dead mask inherited by the item's root node (vector bits)
  std::vector<int32_t> win;   // imported (--pcwit): the witness rows of din (batch 12), as the item line carries them
  bool tracked=false, noexp=false, active=false, rcut=false, rgive=false; std::atomic<bool> exempt{false};   // rcut: a job root cut at replay (kind-2 segment); rgive: a range given back at a spill
  int pexp=0, nexp=0; std::atomic<char> intr{0};
  unsigned long long skmask=0; std::unordered_set<std::string> sk; mutable std::atomic<int> skHit{0};   // skip list (label keys); entries met (reported as skh=, checked by the queue)
  bool regen=false; std::unordered_map<std::string,int> rstop; unsigned long long rsmask=0; mutable std::atomic<int> rsHit{0};   // regeneration of a reported item: its range children (node key -> first label), met (rsh=)
  unsigned long long rootSeg=0; std::unordered_map<std::string,unsigned long long> pcs;   // this run's segments of the unit: root, local pieces (prefix key -> id)
  std::atomic<long long> live{0}, bytes{0}; std::atomic<bool> split{false}; std::vector<SpillRec> srecs; std::vector<Job> spieces;   // --xqcap: nodes (and pcert record bytes) of the own part so far; split; its range records and its queued pieces (P items)
};
static thread_local XUnit* tlXU=nullptr;   // --xqcapb: the imported unit this worker thread runs (its pcert chunks count toward the unit's bytes)
static std::unique_ptr<XUnit[]> gU;
static std::mutex gSpmu; static std::vector<SpillRec> gSpillRecs; static std::atomic<long long> gXexp{0}, gXimp{0}, gXskipT{0};
static std::unordered_set<int> gHanded;
static std::mutex gXmu; static std::deque<std::string> gXout; static std::map<long long,std::string> gXrep; static std::map<long long,int> gXrepIx;
static void xqSendAfterSync(std::vector<std::string>& L){ std::lock_guard<std::mutex> lk(gXmu); for(auto& x:L){ long long c=0; if(sscanf(x.c_str(),"R %lld",&c)==1 || sscanf(x.c_str(),"SP %lld",&c)==1) gXrep[c]=x; gXout.push_back(x+"\\n"); } }   // reports and --xqcap split reports: kept until answered (resent after a reconnect)
static inline std::string pkey(const std::vector<int>& seq){ std::string k; k.resize(2*seq.size()); for(size_t i=0;i<seq.size();i++){ uint16_t x=(uint16_t)seq[i]; memcpy(&k[2*i],&x,2); } return k; }   // labels (as the assembler's keys)
static xqr3::OwnIndex gOwn; static long long gPcFileOff=0; static FILE* gXqSeg=nullptr; static std::mutex gXqSegMu; static long long gXqSegOff=0; static std::string gXqSegPath;
static std::atomic<long long> gXqSegN{0}, gXqSegB{0}, gXqAsmErr{0}, gXqSegWErr{0};   // gXqSegWErr: segment writes that failed (not reported)
static std::string dhex(const std::array<uint64_t,8>& m){ char b[17]; std::string o; for(int k=0;k<8;k++){ snprintf(b,sizeof b,"%016llx",(unsigned long long)m[k]); o+=b; } return o; }
static bool undhex(const std::string& h,std::array<uint64_t,8>& m){ if(h.size()!=128) return false; for(int k=0;k<8;k++){ m[k]=std::stoull(h.substr(16*k,16),nullptr,16); } return true; }
static void winBytes(std::string& o,const std::vector<int32_t>& w){ auto pv=[&](unsigned long long x){ do{ unsigned char c=x&127; x>>=7; if(x) c|=128; o.push_back((char)c); } while(x); }; pv(w.size()); int32_t pr=0; for(int32_t r:w){ pv((unsigned long long)(r-pr)); pr=r; } }   // batch 12 header witness: varint n, n x varint delta
static std::string whex(const std::vector<int32_t>& w){ std::string b; winBytes(b,w); static const char* X="0123456789abcdef"; std::string o; for(unsigned char c:b){ o+=X[c>>4]; o+=X[c&15]; } return o; }   // win= of item lines, exports and spills
static bool unwhex(const std::string& h,std::vector<int32_t>& w){ w.clear(); if(h.empty() || h.size()%2) return false; std::string b; for(size_t i=0;i<h.size();i+=2){ int v=0; for(int k=0;k<2;k++){ char c=h[i+k]; v=v*16+(c>='0'&&c<='9'?c-'0':(c>='a'&&c<='f'?c-'a'+10:-1000)); } if(v<0) return false; b.push_back((char)v); }
  size_t q=0; auto rv=[&](unsigned long long& x)->bool{ x=0; int sh=0; while(q<b.size()){ unsigned char c=(unsigned char)b[q++]; x|=(unsigned long long)(c&127)<<sh; if(!(c&128)) return true; sh+=7; if(sh>63) return false; } return false; };
  unsigned long long n; if(!rv(n) || n>100000) return false; long long pr=0; for(unsigned long long j=0;j<n;j++){ unsigned long long d; if(!rv(d)) return false; pr+=(long long)d; if(pr>INT32_MAX || (j && d==0)) return false; w.push_back((int32_t)pr); } return q==b.size(); }
'''
s=s[:j]+GLOB+s[j:]

# jcommit: reports after the profiles, the stream and the item segments are synced
rep('''static void jcommit(){   // prof7L84: swap out the pending records, fdatasync the profiles they refer to, then write them
  std::vector<std::string> J,S; { std::lock_guard<std::mutex> lk(gJmu); J.swap(gJpend); S.swap(gSpend); }
  if(J.empty() && S.empty()) return;
  if(OUT){ { std::lock_guard<std::mutex> lk(outmu); fflush(OUT); } fdatasync(fileno(OUT)); }
  certSyncR2(); pcSync();   // prof7R2: the certificate lines of the records are on disk before the records (prof7R3: and the pcert bytes)
  jwrite(J,S,nullptr); gJsyncs++; }''','''static std::vector<std::string> gRpend; static void xqSendAfterSync(std::vector<std::string>& L);   // prof7R3q: reports, sent after the syncs
static FILE* gXOUTsync=nullptr; static void xqSegSync();
static std::mutex gJcm;
static void jcommit(){   // prof7L84: swap out the pending records, fdatasync the profiles they refer to, then write them
  std::lock_guard<std::mutex> lkc(gJcm);
  std::vector<std::string> J,S,Rr; { std::lock_guard<std::mutex> lk(gJmu); J.swap(gJpend); S.swap(gSpend); Rr.swap(gRpend); }
  if(J.empty() && S.empty() && Rr.empty()) return;
  if(OUT){ { std::lock_guard<std::mutex> lk(outmu); fflush(OUT); } fdatasync(fileno(OUT)); }
  if(gXOUTsync && gXOUTsync!=OUT){ { std::lock_guard<std::mutex> lk(outmu); fflush(gXOUTsync); } fdatasync(fileno(gXOUTsync)); }
  certSyncR2(); pcSync(); xqSegSync();   // prof7R2: the certificate lines of the records are on disk before the records (prof7R3: and the pcert bytes; prof7R3q: and the item segments)
  jwrite(J,S,nullptr); gJsyncs++;
  if(!Rr.empty()) xqSendAfterSync(Rr); }''')

# pcChunk: index this run's chunks (file offset of the record bytes) for the item assembler
rep('''  { std::lock_guard<std::mutex> lk(pcmu); fwrite(h,4,3,PCF); fwrite(p.data(),1,p.size(),PCF); fflush(PCF); }''',
    '''  { std::lock_guard<std::mutex> lk(pcmu); fwrite(h,4,3,PCF); fwrite(p.data(),1,p.size(),PCF); fflush(PCF);
    const long long roff=gPcFileOff+12+13+(S.chunk==0?(long long)S.hdr.size():0); gOwn.addChunk(S.id,S.chunk,roff,(uint32_t)S.buf.size(),last); gPcFileOff+=12+(long long)p.size(); }   // prof7R3q
  if(XQCAPB>0 && tlXU){ const long long nb=(long long)S.buf.size(); if(tlXU->bytes.fetch_add(nb,std::memory_order_relaxed)+nb>=XQCAPB && !tlXU->regen && !tlXU->split.exchange(true)) gXsplit++; }   // prof7R3q --xqcapb: the own part's record bytes reached the bound''')
rep('''static void pcOpen(int job,int kind,const std::vector<int>& seqLab,const uint64_t* dinhVec,const std::vector<int32_t>* win=nullptr){   // dinhVec: inherited dead mask indexed by vector''',
    '''static void pcOpen(int job,int kind,const std::vector<int>& seqLab,const uint64_t* dinhVec,const std::vector<int32_t>* win=nullptr,int rl=-1,int rpl=-1){   // dinhVec: inherited dead mask indexed by vector (prof7R3q: kind 3 appends u16 l, u16 p after the witness)''')
rep('''  if(PCWIT){ const size_t n=win?win->size():0; pcVar(S.hdr,(unsigned long long)n); int32_t pr=0; if(win) for(int32_t r:*win){ pcVar(S.hdr,(unsigned long long)(r-pr)); pr=r; } } }   // batch 12''',
    '''  if(PCWIT){ const size_t n=win?win->size():0; pcVar(S.hdr,(unsigned long long)n); int32_t pr=0; if(win) for(int32_t r:*win){ pcVar(S.hdr,(unsigned long long)(r-pr)); pr=r; } }   // batch 12
  if(kind==3){ pcU16(S.hdr,(unsigned)rl); pcU16(S.hdr,(unsigned)rpl); } }   // prof7R3q: a range's start and delta base''')
rep('''static void certSyncR2(){''','''static void xqSegSync(){ if(!gXqSeg) return; { std::lock_guard<std::mutex> lk(gXqSegMu); fflush(gXqSeg); } fdatasync(fileno(gXqSeg)); }   // prof7R3q
static void certSyncR2(){''')

# batch >= 5: the effective generator parameters go into the compat fingerprint too
if s.count('    if(PCNOREP){ char b[48]; snprintf(b,sizeof b,"pcnorep-xplim=%lld",XPLIM); mix(b); }')==1: rep('    if(PCNOREP){ char b[48]; snprintf(b,sizeof b,"pcnorep-xplim=%lld",XPLIM); mix(b); }','    if(PCNOREP){ char b[48]; snprintf(b,sizeof b,"pcnorep-xplim=%lld",XPLIM); mix(b); gCompatExtra+=b; gCompatExtra+=\';\'; }')
if s.count('P.exclPrune,P.l1Node,P.prune,P.pruneC2,P.fullOnly,P.allExcl,P.verify,P.agg,P.pruneSteps,P.pruneStepsKind,P.cChild,P.cStep,P.cBr,P.amort1,P.cPair,P.cBrH,P.cLab); mix(b); }')==1: rep('P.exclPrune,P.l1Node,P.prune,P.pruneC2,P.fullOnly,P.allExcl,P.verify,P.agg,P.pruneSteps,P.pruneStepsKind,P.cChild,P.cStep,P.cBr,P.amort1,P.cPair,P.cBrH,P.cLab); mix(b); }','P.exclPrune,P.l1Node,P.prune,P.pruneC2,P.fullOnly,P.allExcl,P.verify,P.agg,P.pruneSteps,P.pruneStepsKind,P.cChild,P.cStep,P.cBr,P.amort1,P.cPair,P.cBrH,P.cLab); mix(b); gCompatExtra+=b; }')
# Search members
rep('''  int pcD0=0; BS pcDin{};   // depth of the open segment's root node; dead mask inherited by it''','''  int pcD0=0; BS pcDin{};   // depth of the open segment's root node; dead mask inherited by it
  const XUnit* xu=nullptr; int rngD=-1, rngL=-1, rngP=-1, rngSeen=0; long long nIntr=0; std::vector<SpillRec> sp; bool spillAt[64]={0};   // prof7R3q: imported unit (skips), range item (node depth, first label, delta base), spill records''')
rep('''  void emit(){ std::lock_guard<std::mutex> lk(outmu); ++nprof; ++myProf; if(OUT){''','''  bool xskip() const { return xu->sk.count(pkey(seq))>0; }   // keys are label prefixes (pkey), as the I-line parser stores them
  bool xskipChild(int l) const { const size_t n=seq.size()+1; if(n>=64 || !((xu->skmask>>n)&1)) return false; std::string k; k.resize(2*n); for(size_t i=0;i<n;i++){ uint16_t x=(uint16_t)(i+1<n?seq[i]:l); memcpy(&k[2*i],&x,2); }
    if(!xu->sk.count(k)) return false; xu->skHit.fetch_add(1,std::memory_order_relaxed); return true; }
  bool xstop(int l) const { auto it=xu->rstop.find(pkey(seq)); if(it==xu->rstop.end() || it->second!=l) return false; xu->rsHit.fetch_add(1,std::memory_order_relaxed); return true; }
  void spillHere(int d,int l){   // prof7R3q: node seq, children from label l on unexplored: RNG record, no END for this node
    if(gJab && gJab[curJob].load(std::memory_order_relaxed)) return;
    SpillRec r{curJob,seq,l,PCF?pcLast[d]:-1,{},{}}; const BS& Dp=(d>pcD0)?pcD[d-1]:pcDin; for(int k=0;k<8;k++) r.D[k]=Dp[k];
    if(PCF && PCWIT){ r.win=pcWin; for(int k=pcD0;k<d;k++) r.win.insert(r.win.end(),pcVr[k].begin(),pcVr[k].end()); std::sort(r.win.begin(),r.win.end()); r.win.erase(std::unique(r.win.begin(),r.win.end()),r.win.end()); }   // batch 12: pcWin + pcVr[pcD0..d-1]
    sp.push_back(std::move(r)); gU[curJob].intr.store(1); nIntr++;
    if(PCF && !collecting){ pcU8(tlPc.buf,0x2C); pcU16(tlPc.buf,(unsigned)l); gPcN[0x2C&63]++; spillAt[d]=true; } }
  void pcBeginQ(int job,int kind,const std::vector<int>& sq,const std::array<uint64_t,8>& dinh,int rl,int rpl,const std::vector<int32_t>* win){ if(!PCF) return; pcOpen(job,kind,sq,dinh.data(),win,rl,rpl); if(PCWIT){ if(win) pcWin=*win; else pcWin.clear(); } pcD0=(int)sq.size(); for(int k=0;k<8;k++) pcDin[k]=dinh[k]; pcNval=-1; }   // batch 12: as pcBegin
  void emit(){ std::lock_guard<std::mutex> lk(outmu); ++nprof; ++myProf; FILE* OUTF=(XOUT && curJob>=(int)gNF)?XOUT:OUT; if(OUTF){''')
# emit body uses OUT: switch to OUTF inside emit only
i=s.index('FILE* OUTF=(XOUT && curJob>=(int)gNF)?XOUT:OUT; if(OUTF){'); j=s.index('\n',i)
line=s[i:j]; line2=line.replace('fprintf(OUT,','fprintf(OUTF,').replace('fflush(OUT)','fflush(OUTF)'); s=s[:i]+line2+s[j:]

# range node: no NODE record (pcEnter) and no OPEN byte (pcOpenNode); node data is written (the copy QUEUE.md asks for)
rep('''    const int lab=seq.empty()?0:seq.back(); std::string& B=tlPc.buf; pcU8(B,0x01); pcU16(B,(unsigned)((d<<9)|lab)); gPcN[1]++;''',
    '''    const int lab=seq.empty()?0:seq.back(); std::string& B=tlPc.buf; if(d!=rngD){ pcU8(B,0x01); pcU16(B,(unsigned)((d<<9)|lab)); gPcN[1]++; }   // prof7R3q: a range's node has its NODE in the spiller's segment''')
rep('''    std::string& B=tlPc.buf; pcU8(B,0x04); gPcN[4]++; const int lab=seq.back(); pcLast[d]=lab;''',
    '''    std::string& B=tlPc.buf; if(d!=rngD){ pcU8(B,0x04); gPcN[4]++; } const int lab=seq.back(); pcLast[d]=lab;   // prof7R3q: a range copies the node data, not OPEN''')

# --xqcap: the node count of an imported unit's own part (dfs entry = one node, as `visited`)
rep('''    int d=seq.size(); cDepth[d]++;
''','''    int d=seq.size(); cDepth[d]++;
    if(XQCAP>0 && curJob>=(int)gNF && !collecting && !shadow){ XUnit& Uc=gU[curJob]; if(Uc.live.fetch_add(1,std::memory_order_relaxed)+1==XQCAP && !Uc.regen && !Uc.split.exchange(true)) gXsplit++; }   // prof7R3q --xqcap: the own part reached the cap (a regeneration never splits)
''')
# dfs: journals for list jobs only; an earlier child item reached at entry would be a bug (counted as an internal check failure)
rep('''  void dfs(int pos,int need,double w){
''','''  void dfs(int pos,int need,double w){
    if(xu && xu->skmask && seq.size()<64 && ((xu->skmask>>seq.size())&1) && xskip()){ gPcErr++; *doneP+=w; return; }   // prof7R3q: never happens (children are skipped before add)
''')
rep('''    if(gJdmask && d<64 && ((gJdmask>>d)&1) && curJob>=0 && !shadow){   // prof7L84 --skipjournal: a piece finished by an earlier run''',
    '''    if(gJdmask && d<64 && ((gJdmask>>d)&1) && curJob>=0 && curJob<(int)gNF && !shadow){   // prof7L84 --skipjournal: a piece finished by an earlier run (prof7R3q: list jobs only)''')
rep('''    if(gJrmask && d<64 && ((gJrmask>>d)&1) && curJob>=0 && !shadow){''','''    if(gJrmask && d<64 && ((gJrmask>>d)&1) && curJob>=0 && curJob<(int)gNF && !shadow){''')
rep('''    const bool jon=gJF && curJob>=0 && !collecting && d>=JDEPTH && d<64 && !shadow; if(jon) jacc[d]=JAcc();''',
    '''    const bool jon=gJF && curJob>=0 && curJob<(int)gNF && !collecting && d>=JDEPTH && d<64 && !shadow; if(jon) jacc[d]=JAcc();   // prof7R3q: list jobs only''')
rep('''    if(pc) pcOpenNode(d,pos);   // prof7R3: OPEN, V rows, row table, W-blocked / subspace-blocked candidates''',
    '''    if(pc) pcOpenNode(d,pos);   // prof7R3: OPEN, V rows, row table, W-blocked / subspace-blocked candidates
    if(pc && d==rngD) pcLast[d]=rngP;   // prof7R3q: a range item's first child record is delta-coded from the spiller's last one
    if(d<64) spillAt[d]=false;''')
# child loop: range start, spill, earlier child items
rep('''    for(int i=0;i<na;i++){ if(suf[i]<need) break; int l=avl[i];
      if(gSkipP && curJob>=0 && gSkipP[curJob].load(std::memory_order_relaxed)){ gJab[curJob].store(1); if(pc){ pcU8(tlPc.buf,0x06); gPcN[6]++; } break; }   // prof7L48 --abortdone''',
    '''    for(int i=0;i<na;i++){ if(suf[i]<need) break; int l=avl[i];
      if(d==rngD && l<rngL) continue;   // prof7R3q: a range item explores this node's children from label rngL on
      if(gSkipP && curJob>=0 && gSkipP[curJob].load(std::memory_order_relaxed)){ gJab[curJob].store(1); if(pc){ pcU8(tlPc.buf,0x06); gPcN[6]++; } break; }   // prof7L48 --abortdone''')
rep('''      if(collecting && !UNDER.empty() && !underOK(d,l)) continue;   // --under: skip subtrees outside the listed prefixes
      if(pff){ int v=vecOf[l], nn=need-1; const auto& SH=sufHits[l]; bool cut=false; int pcode=0;''',
    '''      if(xu && xu->rsmask && d<64 && ((xu->rsmask>>d)&1) && !collecting && !shadow && xstop(l)){ if(PCF){ pcU8(tlPc.buf,0x2C); pcU16(tlPc.buf,(unsigned)l); gPcN[0x2C&63]++; spillAt[d]=true; } break; }   // prof7R3q regeneration: the item's range child starts here (the RNG its spill wrote)
      if(gSpill.load(std::memory_order_relaxed)?(d<=SPILLD && !collecting && !shadow && curJob>=0):((XQCAP>0 || XQCAPB>0) && curJob>=(int)gNF && d<=XQCAPD && !collecting && !shadow && gU[curJob].split.load(std::memory_order_relaxed))){
        if(d==rngD && rngSeen==0){ if(gSpill.load(std::memory_order_relaxed)){ gU[curJob].rgive=true; gU[curJob].intr.store(1); nIntr++; if(d<64) spillAt[d]=true; break; } }   // a range not yet started is given back, never re-spilled (RNG l' > l at a range root: the Lean side's SegOKO); a split explores its first child first
        else { spillHere(d,l); break; } }   // prof7R3q: the rest of this node becomes a range item (spill, or --xqcap split)
      if(d==rngD) rngSeen++;
      if(collecting && !UNDER.empty() && !underOK(d,l)) continue;   // --under: skip subtrees outside the listed prefixes
      if(pff){ int v=vecOf[l], nn=need-1; const auto& SH=sufHits[l]; bool cut=false; int pcode=0;''')
rep('''      if(lateC && !canonCheck(l)){ if(d<32) st[7][d]++; if(pc && !pcInD(d,vecOf[l])) pcCanon(d,l); *doneP+=wc; continue; }''',
    '''      if(lateC && !canonCheck(l)){ if(d<32) st[7][d]++; if(pc && !pcInD(d,vecOf[l])) pcCanon(d,l); *doneP+=wc; continue; }
      if(xu && xu->skmask && xskipChild(l)){ if(pc) pcChild(d,l,0x28); *doneP+=wc; continue; }   // prof7R3q: an earlier holder's child item: the DON it wrote; never added, donated or entered''')
rep('''          if(donN!=cd0 || (gJab && gJab[curJob].load(std::memory_order_relaxed)) || nprof>=MAXPROF) A=JAcc();''',
    '''          if(donN!=cd0 || (gJab && gJab[curJob].load(std::memory_order_relaxed)) || nprof>=MAXPROF || nIntr!=ci0) A=JAcc();   // prof7R3q: nor a subtree a spill interrupted''')
rep('''        else { const long long cv0=visited, cl0=myLeaf, cp0=myProf, cd0=donN; const long long po0=pc?pcOff():-1; dfs(l,need-1,wc);''',
    '''        else { const long long cv0=visited, cl0=myLeaf, cp0=myProf, cd0=donN, ci0=nIntr; const long long po0=pc?pcOff():-1; dfs(l,need-1,wc);''')
rep('''    if(pc){ pcU8(tlPc.buf,0x05); gPcN[5]++; pcMaybe(); }   // prof7R3: END''',
    '''    if(pc && !(d<64 && spillAt[d])){ pcU8(tlPc.buf,0x05); gPcN[5]++; pcMaybe(); }   // prof7R3: END (prof7R3q: not for a node a spill cut: its END is in the range item)
    if(d<64) spillAt[d]=false;''')

# options
rep('''    else if(a=="--pcert"){''','''    else if(a=="--xq") XQADDR=argv[++i]; else if(a=="--xqname") XQNAMEO=argv[++i]; else if(a=="--xqpool") XQPOOLO=argv[++i]; else if(a=="--xqout") XQOUTP=argv[++i]; else if(a=="--xqstop") XQSTOPF=argv[++i]; else if(a=="--xqseg") XQSEGP=argv[++i]; else if(a=="--xqrecipe") XQRECIPE=argv[++i]; else if(a=="--xqrecover") XQRECOVER=argv[++i]; else if(a=="--xqpause") XQPAUSE=argv[++i]; else if(a=="--xqpunch") XQPUNCH=std::stoi(argv[++i]); else if(a=="--xqcap") XQCAP=std::stoll(argv[++i]); else if(a=="--xqcapd") XQCAPD=std::stoi(argv[++i]); else if(a=="--xqcapb") XQCAPB=(long long)(std::stod(argv[++i])*1e6);   // prof7R3q
    else if(a=="--xqnoexport") XQEXPORT=false; else if(a=="--xqnoimport") XQIMPORT=false; else if(a=="--xqhelper") XQHELPER=true; else if(a=="--xqlinger") XQLINGER=std::stod(argv[++i]); else if(a=="--xqmaxd") XQMAXD=std::stoi(argv[++i]); else if(a=="--xqkeep") XQKEEP=std::stoi(argv[++i]);
    else if(a=="--xqslots") XQSLOTS=std::stoi(argv[++i]); else if(a=="--xqtermwait") XQTERMWAIT=std::stod(argv[++i]); else if(a=="--xqdown") XQDOWN=std::stod(argv[++i]); else if(a=="--xqnospillterm") XQSPILLTERM=false; else if(a=="--spillfile") SPILLF=argv[++i]; else if(a=="--spillout") SPILLOUT=argv[++i]; else if(a=="--spilld") SPILLD=std::stoi(argv[++i]);
    else if(a=="--pcert"){''')
# journal fingerprint: the queue options are run-specific (as in prof7L92); compat fingerprint: its own list
i=s.index('    static const char* RUN1[]={"--threads"'); j=s.index('nullptr};',i)
s=s[:j]+'"--xq","--xqname","--xqpool","--xqout","--xqstop","--xqseg","--xqrecipe","--xqpunch","--xqrecover","--xqpause","--xqcap","--xqcapd","--xqcapb","--xqlinger","--xqmaxd","--xqkeep","--xqslots","--xqtermwait","--xqdown","--spillfile","--spillout","--spilld",'+s[j:]
i=s.index('    static const char* RUN0[]={"--abortdone"'); j=s.index('nullptr};',i)
s=s[:j]+'"--xqnoexport","--xqnoimport","--xqhelper","--xqnospillterm",'+s[j:]
rep('''    gFP=h; gFP84=h84;''','''    gFP=h; gFP84=h84;
    { // prof7R3q: compat = search + certificate options (order-independent groups), pcert / cert mode; launch-specific options and the frontier left out
      static const char* C1[]={"--threads","--jobsfile","--state","--out","--journal","--jdepth","--jmin","--jsync","--skipjournal","--skipfile","--skipevery","--drainfile","--agedonate","--agedepth","--pfd","--donate_depth","--cert","--jcompat","--pcert",
        "--xq","--xqname","--xqpool","--xqout","--xqstop","--xqseg","--xqrecipe","--xqpunch","--xqrecover","--xqpause","--xqcap","--xqcapd","--xqcapb","--xqlinger","--xqmaxd","--xqkeep","--xqslots","--xqtermwait","--xqdown","--spillfile","--spillout","--spilld","--frontier","--frontierfile","--under","--dumpfrontier","--jobs","--jobprefix","--doneprefixes",nullptr};
      static const char* C0[]={"--abortdone","--verbose","--jforce","--jcompat84","--pcchk","--xqnoexport","--xqnoimport","--xqhelper","--xqnospillterm","--dumponly","--reverse",nullptr};
      unsigned long long hc=1469598103934665603ULL; auto mixc=[&](const char* t){ for(;*t;t++){ hc^=(unsigned char)*t; hc*=1099511628211ULL; } hc^=0xff; hc*=1099511628211ULL; };
      std::vector<std::string> grp; for(int i=1;i<argc;i++){ bool s1=false, s0=false; for(int k=0;C1[k];k++) if(!strcmp(argv[i],C1[k])) s1=true; for(int k=0;C0[k];k++) if(!strcmp(argv[i],C0[k])) s0=true;
        if(s1){ i++; continue; } if(s0) continue; if(argv[i][0]=='-' && argv[i][1]=='-') grp.push_back(argv[i]); else if(!grp.empty()){ grp.back()+=' '; grp.back()+=argv[i]; } else grp.push_back(argv[i]); }
      std::stable_sort(grp.begin(),grp.end(),[](const std::string& a,const std::string& b){ return a.substr(0,a.find(' '))<b.substr(0,b.find(' ')); }); mixc("prof7R3q"); mixc(R3Q_BASE);   // by option name; a repeated option keeps its order (the last value wins); the merged R3 source
      if(PCF) mixc("pcertmode"); if(CERTF) mixc("certmode"); for(auto& g:grp) mixc(g.c_str()); mixc(gCompatExtra.c_str());
      if(XQRECIPE){   // the recipe file (r22/lean/rerun/RECIPE.txt): its flag tokens (lines not starting with '#') must stand on the command line as one
        // contiguous run; the sha256 of those tokens, single-space joined, goes into compat (every run of a queue uses the same recipe)
        std::string rpath=XQRECIPE, rkey="FLAGS"; { auto c=rpath.rfind(':'); if(c!=std::string::npos && c+1<rpath.size() && isupper((unsigned char)rpath[c+1])){ rkey=rpath.substr(c+1); rpath=rpath.substr(0,c); } }   // FILE[:KEY], KEY = FLAGS / FLAGS_I / FLAGS_I13
        std::ifstream rf(rpath); if(!rf){ fprintf(stderr,"R3q: cannot read --xqrecipe %s\\n",XQRECIPE); return 2; }
        std::vector<std::string> rt, rall; std::string ln; bool hasF=false;   // r22/lean/rerun/RECIPE.txt: the line "FLAGS ..."; a file without one: every line not starting with '#'
        while(std::getline(rf,ln)){ size_t a0=ln.find_first_not_of(" \\t\\r"); if(a0==std::string::npos || ln[a0]=='#') continue; std::istringstream is(ln); std::string t; is>>t;
          if(t==rkey){ hasF=true; rt.clear(); while(is>>t) rt.push_back(t); } else if(!hasF && t.compare(0,5,"FLAGS")!=0 && t!="PHASE0" && t!="ENV" && t!="BINARY" && t!="BUILD" && t!="READER" && t!="CONVERTER" && t!="DATA" && t.compare(0,4,"JOBS")!=0){ rall.push_back(t); while(is>>t) rall.push_back(t); } }
        if(!hasF){ if(rkey!="FLAGS"){ fprintf(stderr,"R3q: --xqrecipe %s has no line %s\\n",rpath.c_str(),rkey.c_str()); return 2; } rt=rall; }
        if(rt.empty()){ fprintf(stderr,"R3q: --xqrecipe %s has no flags\\n",XQRECIPE); return 2; }
        bool found=false; for(int i=1;i+(int)rt.size()<=argc && !found;i++){ bool ok=true; for(size_t k=0;k<rt.size() && ok;k++) if(rt[k]!=argv[i+k]) ok=false; found=ok; }
        if(!found){ fprintf(stderr,"R3q: the flags of --xqrecipe %s are not on the command line as one run (stale run script?)\\n",XQRECIPE); return 2; }
        std::string js=(rkey=="FLAGS"?std::string():rkey+" "); for(size_t k=0;k<rt.size();k++){ if(k) js+=' '; js+=rt[k]; } uint8_t raw[32]; gRecipeSha=xqr3::sha256hex(js,raw); mixc("recipe"); mixc(gRecipeSha.c_str()); }   // the key is hashed too: a FLAGS_I run never pairs with a FLAGS run
      gOptFP=hc; }''')
# table identity
rep('''  { FILE* f=fopen(tabpath,"rb"); fseek(f,0,SEEK_END); long sz=ftell(f); fseek(f,0,SEEK_SET); size_t n=sz/24; std::vector<char> buf(sz); if(fread(buf.data(),1,sz,f)!=(size_t)sz) return 3; fclose(f);''',
    '''  static unsigned long long gTabHash=0;   // prof7R3q: table identity for the compat fingerprint
  { FILE* f=fopen(tabpath,"rb"); fseek(f,0,SEEK_END); long sz=ftell(f); fseek(f,0,SEEK_SET); size_t n=sz/24; std::vector<char> buf(sz); if(fread(buf.data(),1,sz,f)!=(size_t)sz) return 3; fclose(f);
    { unsigned long long th=0x9E3779B97F4A7C15ULL^(unsigned long long)sz; size_t nw=buf.size()/8; const char* bp=buf.data(); for(size_t i=0;i<nw;i++){ unsigned long long x; memcpy(&x,bp+8*i,8); th=(th^x)*0xBF58476D1CE4E5B9ULL; th^=th>>31; } gTabHash=th; }''')
# helper mode and H records
rep('''  if(FRONTIER_D>=0){
    auto t0=std::chrono::steady_clock::now();
    if(FRONTF){''','''  if(XQHELPER){ if(!XQADDR){ fprintf(stderr,"--xqhelper needs --xq\\n"); return 2; } if(FRONTIER_D<0) FRONTIER_D=99; }   // prof7R3q: a helper has no frontier
  if(FRONTIER_D>=0){
    auto t0=std::chrono::steady_clock::now();
    if(XQHELPER){ fprintf(stderr,"R3q: helper (no frontier jobs)\\n"); }
    else if(FRONTF){''')
rep('''          if(!hdr){ fprintf(stderr,"journal %s: no header\\n",fn.c_str()); return 2; }
''','''          if(!hdr){ fprintf(stderr,"journal %s: no header\\n",fn.c_str()); return 2; }
          if(line[0]=='H'){ long long hx=-1; if(sscanf(line.c_str(),"H %lld",&hx)==1 && hx>=0 && (size_t)hx<frontier.size()){ gHanded.insert((int)hx); nrec++; } else nbad++; continue; }   // prof7R3q: a job handed to the queue
''')

# the frontier driver block
blk=open(blockf).read()
a=s.index('    if(JOURNALF){ gJF=fopen(JOURNALF,"a");')
b=s.index('\n    return 0; }\n',a)+len('\n    return 0; }\n')
s=s[:a]+blk+s[b:]
open(outf,'w').write(s); print('wrote',outf)
