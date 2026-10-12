// r3qglue.cc: the glue of the item queue's certificate segments (r22/lean/rerun/r3/QUEUE.md section 4).  For every complete queue job,
// assembles its canonical certificate stream from the prof7R3q item segments named by the manifest, and checks the glue.
//   r3qglue PLAN [--map HOST=DIR]... [--emit DIR] [--ref MD5FILE]... [--normcut]
//   r3qglue --md5bin HDRFILE STREAM... [--normcut]     md5 of assembled streams (r3cat job output; flags from HDRFILE's header)
//   r3qglue --itemtext SEGFILE OFF LEN | --itembin SEGFILE OFF LEN OUT   one item segment as text / as its verified binary block
//   r3qglue --itemkey SEGFILE OFF LEN   the item's interface: root prefix and lo, child pieces and jobs (ext), range children (rng)
//   r3qglue --mktop PCERT DUMP OUT.xq [HOST]   a --pctop run's kind-4 segments as item blocks + a listing for xqctl addtop
// PLAN: `xqaudit.py MANIFEST --plan PLAN` (complete jobs only; xqaudit checks the manifest's tree, totals and regions first).
// A segment reference is HOST:FILE:OFFSET:LENGTH:SHA256; FILE is read at DIR/FILE for a host given with --map, else at FILE.
// Checks: per segment, the block's magic and length, the sha256 of its record bytes (= the stored hash = the manifest's), and its
// header against the manifest (job, kind, prefix, inherited dead mask, range start, delta base, item id); the segment files of a job
// agree on compat (search + certificate options and table), #lab, #typecut, #leafx, #cutx.  Assembly (as r3cat job): a DON not inlined by its run is replaced by the
// child item of kind P with that prefix; an RNG l at node S by the child item of kind Q with prefix S and start l, whose delta base
// must equal S's last child label and whose leading node-data copy must equal S's node data (VROWS / XROWS / WB / BLK / XPN after
// S's OPEN; the copy is dropped).  Every child item is referenced exactly once and the stream closes.  Not checked here (the Lean
// side's frame check): that a child's dead mask is the one its parent computes at the reference.  With #pcwit 1 (batch 12, --pcwit) every
// header carries the witness rows of its mask after the 64 bytes; a piece's must equal the VROWS rows cited at the donor node and its
// ancestors in the job, a range's those of its node's ancestors (as r3cat_k12 wit recomputes them), and the manifest's win=.
// Output: one line per job "pool ix md5 bytes items P Q" (md5 of the stream, as r3cat md5); with --ref (r3cat md5 output of a
// single-process run, "ix md5 bytes ...") the md5s are compared; --emit writes DIR/<pool>_<ix>.r3j (r3cat textbin reads it with any
// segment file as LABFILE).  Exit 0 iff every job glues (and matches its reference).
// Build: g++ -O2 -std=c++17 -I. -I../../lean/rerun/r3 r3qglue.cc -o r3qglue -lcrypto
#include "xq_r3.h"
#include <openssl/md5.h>
using namespace std;
using xqr3::Rd; using xqr3::fail; using xqr3::QErr;

// pread of any length (one pread returns at most ~2 GB on Linux; item segments of heavy jobs are bigger)
static bool preadAll(int fd,char* p,size_t n,long long off){ while(n){ ssize_t r=pread(fd,p,n,off); if(r<=0) return false; p+=r; n-=(size_t)r; off+=r; } return true; }
static string md5hex(const string& s){ unsigned char h[16]; MD5((const unsigned char*)s.data(),s.size(),h); char b[40]; for(int i=0;i<16;i++) sprintf(b+2*i,"%02x",h[i]); return string(b,32); }
// --normcut: node cuts 5/6 written as uncertified (u8 ok = 0, no payload), on both sides of a comparison: the batch-2 node-cut
// certificate depends on segment boundaries (QUEUE.md section 7) until the R3 fix
static bool NORMCUT=false; static vector<int> TOPROOT;   // --root CODES: the one top segment no JOB points at (case II: the code of label 0)
static string normCut(const string& s){ if(!NORMCUT || !xqr3::gCutx) return s; string o; o.reserve(s.size()); Rd r(s);
  while(r.more()){ const size_t a=r.i; uint8_t t; xqr3::skipRec(r,t);
    if(t==0x03){ Rd q(s); q.i=a+1; const int k=q.u8(); if(k==5||k==6){ q.var(); o.append(s,a,q.i-a); o.push_back('\0'); continue; } }
    o.append(s,a,r.i-a); }
  return o; }
static string key(const vector<int>& p){ string k(2*p.size(),'\0'); for(size_t i=0;i<p.size();i++){ uint16_t x=(uint16_t)p[i]; memcpy(&k[2*i],&x,2); } return k; }

struct SegFile { string path; int fd=-1; string fp, compat, typecut; vector<int> lab; bool leafx=false, cutx=false, pcwit=false, leafv7=false; vector<int> labOf; };
static map<string,unique_ptr<SegFile>> FILES;
static map<string,string> MAPS;
static SegFile& segFile(const string& host,const string& file){
  auto mi=MAPS.find(host); const string path=(mi==MAPS.end()?string():mi->second)+file;
  auto it=FILES.find(path); if(it!=FILES.end()) return *it->second;
  auto F=make_unique<SegFile>(); F->path=path; F->fd=open(path.c_str(),O_RDONLY); if(F->fd<0) fail("cannot open segment file "+path);
  FILE* f=fopen(path.c_str(),"rb"); char line[1<<16]; bool end=false;
  while(fgets(line,sizeof line,f)){ string s(line); if(s.rfind("#end",0)==0){ end=true; break; } istringstream is(s); string t; is>>t;
    if(t=="#R3XQ"){ string w; is>>w; while(is>>w){ if(w.rfind("fp=",0)==0) F->fp=w.substr(3); else if(w.rfind("compat=",0)==0) F->compat=w.substr(7); } }
    else if(t=="#lab"){ int n; is>>n; F->lab.resize(n); for(int i=0;i<n;i++) is>>F->lab[i]; }
    else if(t=="#typecut") is>>F->typecut; else if(t=="#leafx") F->leafx=true; else if(t=="#cutx") F->cutx=true; else if(t=="#pcwit") F->pcwit=true; else if(t=="#leafv7") F->leafv7=true; }
  fclose(f); if(!end) fail(path+": no #end header line"); if(F->lab.empty()) fail(path+": no #lab line");
  F->labOf.assign(512,-1); for(size_t l=0;l<F->lab.size();l++){ int v=F->lab[l]; if(v<1 || v>511) fail(path+": bad #lab"); F->labOf[v]=(int)l; }
  SegFile& r=*F; FILES[path]=move(F); return r; }

struct Item { long long id=0, parent=0; char kind='?'; int rsV=0, rpV=0; vector<int> preV; string dinh, win, seg, chk; vector<long long> kids; vector<long long> W;   // win: the manifest's witness (hex); W: the header's
  string recs; size_t ndEnd=0; int hkind=-1, hl=0, hp=0; unsigned long long hid=0, hjob=0; vector<int> preL; uint64_t D[8]={0}; bool used=false;
  unordered_map<string,long long> pk; map<pair<string,int>,long long> qk; SegFile* F=nullptr; };
struct Job { string pool, space; int ix=0; long long root=0, n=0, l=0, p=0; vector<long long> items; };

static void loadSeg(Item& X,int jix){
  // HOST:FILE:OFF:LEN:SHA (FILE has no ':')
  vector<string> f; { string t; for(char c:X.seg){ if(c==':'){ f.push_back(t); t.clear(); } else t+=c; } f.push_back(t); }
  if(f.size()!=5) fail("item "+to_string(X.id)+": bad segment reference "+X.seg);
  SegFile& F=segFile(f[0],f[1]); X.F=&F; const long long off=stoll(f[2]), len=stoll(f[3]);
  if(len<8+8+32 || len>(1LL<<40)) fail("item "+to_string(X.id)+": bad segment length");
  string b((size_t)len,'\0'); if(!preadAll(F.fd,&b[0],(size_t)len,off)) fail("item "+to_string(X.id)+": segment beyond the end of "+F.path);
  uint32_t mg, hl; memcpy(&mg,&b[0],4); memcpy(&hl,&b[4],4); if(mg!=0x49583352u) fail("item "+to_string(X.id)+": no segment block at "+F.path+":"+f[2]);
  if(8+(long long)hl+8+32>len) fail("item "+to_string(X.id)+": header longer than the block");
  uint64_t n; memcpy(&n,&b[8+hl],8); if(8+(long long)hl+8+(long long)n+32!=len) fail("item "+to_string(X.id)+": block length mismatch");
  X.recs=b.substr(8+hl+8,(size_t)n); uint8_t raw[32]; const string hex=xqr3::sha256hex(X.recs,raw);
  if(memcmp(raw,&b[8+hl+8+n],32)!=0) fail("item "+to_string(X.id)+": record bytes do not match the stored sha256");
  if(hex!=f[4]) fail("item "+to_string(X.id)+": sha256 differs from the manifest's");
  const string hs=b.substr(8,hl); Rd h(hs); X.hid=h.var(); X.hjob=h.var(); X.hkind=h.u8(); int d0=h.u8(); X.preL.resize(d0); for(int i=0;i<d0;i++) X.preL[i]=(int)h.u16();
  for(int k=0;k<8;k++){ uint64_t w=0; for(int j=0;j<8;j++) w|=(uint64_t)h.u8()<<(8*j); X.D[k]=w; }
  X.W.clear(); if(F.pcwit){ const auto n=h.var(); long long pr=0; for(unsigned long long j=0;j<n;j++){ pr+=(long long)h.var(); X.W.push_back(pr); } }   // batch 12
  X.hl=(int)h.u16(); X.hp=(int)h.u16(); if(h.more()) fail("item "+to_string(X.id)+": header has extra bytes");
  // header = manifest
  auto lab=[&](int v){ if(v<1 || v>511 || F.labOf[v]<0) fail("item "+to_string(X.id)+": vector "+to_string(v)+" is not a label"); return F.labOf[v]; };
  if(X.hid && (long long)X.hid!=X.id) fail("item "+to_string(X.id)+": segment written for item "+to_string(X.hid));
  if((long long)X.hjob!=jix) fail("item "+to_string(X.id)+": segment of job "+to_string(X.hjob));
  const int wantKind=X.kind=='J'?0:(X.kind=='P'?1:(X.kind=='Q'?3:-1));   // a job root cut at replay has R3's kind-2 segment (CUT 11)
  if(X.hkind!=wantKind && !(X.kind=='J' && X.hkind==2)) fail("item "+to_string(X.id)+": segment kind "+to_string(X.hkind)+" for a "+X.kind+" item");
  if((int)X.preV.size()!=d0) fail("item "+to_string(X.id)+": prefix depth differs"); for(int i=0;i<d0;i++) if(lab(X.preV[i])!=X.preL[i]) fail("item "+to_string(X.id)+": prefix differs");
  uint64_t Dm[8]={0};
  if(!X.dinh.empty()){ if(X.dinh.size()!=128) fail("item "+to_string(X.id)+": bad dinh"); for(int k=0;k<8;k++){ const uint64_t w=stoull(X.dinh.substr(16*k,16),nullptr,16); for(int j=0;j<64;j++) if((w>>j)&1){ const int v=64*k+j; Dm[lab(v)>>6]|=1ULL<<(lab(v)&63); } } }
  if(memcmp(Dm,X.D,64)!=0) fail("item "+to_string(X.id)+": inherited dead mask differs from the manifest's");
  if(F.pcwit){ if(X.kind=='J'){ if(!X.W.empty()) fail("item "+to_string(X.id)+": a job root's header has witness rows"); if(!X.win.empty() && X.win!="00") fail("item "+to_string(X.id)+": the manifest has witness rows for a job root"); }
    else { if(X.win.empty()) fail("item "+to_string(X.id)+": the manifest has no witness (win=) for this #pcwit segment");
      string b; for(size_t i=0;i+1<X.win.size();i+=2) b.push_back((char)stoi(X.win.substr(i,2),nullptr,16)); Rd q(b); vector<long long> M; const auto n=q.var(); long long pr=0; for(unsigned long long j=0;j<n;j++){ pr+=(long long)q.var(); M.push_back(pr); }
      if(q.more() || M!=X.W) fail("item "+to_string(X.id)+": header witness differs from the manifest's"); } }
  else if(!X.win.empty()) fail("item "+to_string(X.id)+": the manifest has a witness, the segment file no #pcwit");
  if(X.kind=='Q'){ if(X.hl!=lab(X.rsV)) fail("item "+to_string(X.id)+": range start differs"); if(X.hp!=lab(X.rpV)) fail("item "+to_string(X.id)+": delta base differs"); }
  else if(X.hl || X.hp) fail("item "+to_string(X.id)+": l/p set outside a range");
  // a range starts with its node's node-data copy
  if(X.kind=='Q'){ Rd r(X.recs); while(r.more()){ const size_t a=r.i; const uint8_t t=r.p[r.i]; if(!(t==0x10||t==0x11||t==0x12||t==0x13||t==0x2B)){ r.i=a; break; } uint8_t t2; xqr3::skipRec(r,t2); } X.ndEnd=r.i; } }

struct Frame { int depth, label, last; string nd; bool ndOpen; vector<long long> vr; };   // vr: the VROWS rows cited at the node (#pcwit checks)
// r3cat.cc's toText (one record per line, absolute labels), plus "RG l" for 0x2C RNG; st0 = the frames open at the start (a range: its node)
struct TF { int depth, label, last; };
static void toTextQ(const string& s,FILE* o,vector<TF> st){
  Rd r(s); TF pend{0,0,0}; bool hp=false; using xqr3::gLeafx; using xqr3::gCutx; using xqr3::gLeafv7;
  while(r.more()){ uint8_t t=r.u8();
    auto child=[&](){ if(st.empty()) fail("child record outside a node"); st.back().last+=(int)r.var(); return st.back().last; };
    switch(t){
      case 0x01: { unsigned x=r.u16(); int d=x>>9, l=x&511; if(!st.empty()) st.back().last=l; pend={d,l,l}; hp=true; fprintf(o,"N %d %d\n",d,l); break; }
      case 0x02: { int c=r.u8(); fprintf(o,"L %d",c); if(gLeafx){ if(c==5) fprintf(o," row %llu",r.var()); else if(c==6||c==7){ int n=r.u8(); fprintf(o," wl"); for(int k=0;k<n;k++) fprintf(o," %u",r.u16()); fprintf(o," cap %d",(int)r.u8()-1); } }
        if(gLeafv7 && c==0){ auto nb=r.var(); fprintf(o," v7 %llu ",nb); for(unsigned long long k=0;k<(nb+7)/8;k++) fprintf(o,"%02x",r.u8()); } fprintf(o,"\n"); hp=false; break; }   // batch 13: the v7 leaf record (as r3cat_k13)
      case 0x03: { int k=r.u8(); fprintf(o,"C %d",k); if(k==1) fprintf(o," %u",r.u16()); else if(k==2||k==4||k==5||k==6||k==10){ fprintf(o," %llu",r.var()); if(gCutx && (k==5||k==6)){ int ok=r.u8(); fprintf(o," xp %d",ok); if(ok){ auto ne=r.var(); fprintf(o," ex"); for(unsigned long long j=0;j<ne;j++) fprintf(o," %llu",r.var()); auto L1=r.var(); fprintf(o," node "); for(unsigned long long j=0;j<L1;j++) fprintf(o,"%02x",r.u8()); auto L2=r.var(); fprintf(o," cert "); for(unsigned long long j=0;j<L2;j++) fprintf(o,"%02x",r.u8()); } } } else if(k==3) fprintf(o," %d",r.u8());
        else if(k==11){ int p=r.u8(), ak=r.u8(); fprintf(o," %d %d",p,ak); if(ak==1||ak==2){ int dm=r.u8(); fprintf(o," %d",dm); for(int j=0;j<dm;j++) fprintf(o," %u",r.u16()); } else fprintf(o," %d",r.u8()); }
        fprintf(o,"\n"); hp=false; break; }
      case 0x04: fprintf(o,"O\n"); if(!hp) fail("OPEN without NODE"); st.push_back(pend); hp=false; break;
      case 0x05: fprintf(o,"E\n"); if(st.empty()) fail("END"); st.pop_back(); break;
      case 0x06: fprintf(o,"A\n"); break;
      case 0x10: { auto n=r.var(); long long p=0; fprintf(o,"V"); for(unsigned long long j=0;j<n;j++){ p+=(long long)r.var(); fprintf(o," %lld",p); } fprintf(o,"\n"); break; }
      case 0x11: { auto a=r.var(), b=r.var(), c=r.var(), e=r.var(); fprintf(o,"XR %llu %llu %llu %llu :",a,b,c,e); for(unsigned long long j=0;j<a+b+c+e;j++) fprintf(o," %llu",r.var()); fprintf(o,"\n"); break; }
      case 0x12: { auto n=r.var(); int pl=st.empty()?0:st.back().label; fprintf(o,"WB"); for(unsigned long long j=0;j<n;j++){ pl+=(int)r.var(); fprintf(o," %d:%d",pl,r.u8()); } fprintf(o,"\n"); break; }
      case 0x13: { auto n=r.var(); int pl=st.empty()?0:st.back().label; fprintf(o,"BK"); for(unsigned long long j=0;j<n;j++){ pl+=(int)r.var(); int dm=r.u8(); fprintf(o," %d:%d",pl,dm); for(int k=0;k<dm;k++) fprintf(o,",%u",r.u16()); } fprintf(o,"\n"); break; }
      case 0x20: { int l=child(); int x=r.u8(); fprintf(o,"T %d :",l); for(int j=0;j<x;j++) fprintf(o," %llu",r.var()); fprintf(o,"\n"); break; }
      case 0x21: { int l=child(); int x=r.u8(), c=r.u8(); fprintf(o,"CV %d %d %d :",l,x,c); for(int j=0;j<x+c;j++) fprintf(o," %llu",r.var()); fprintf(o,"\n"); break; }
      case 0x22: { int l=child(); int k=r.u8(); unsigned long long bb=r.var(); int ch=r.u8(); fprintf(o,"X %d %d %llu %d",l,k,bb,ch);
        if(ch==1 || ch==3){ int ne=(int)r.var(); fprintf(o," ex"); for(int j=0;j<ne;j++) fprintf(o," %llu",r.var()); auto nc=r.var(); fprintf(o," con %llu",nc);
          for(unsigned long long j=0;j<nc;j++){ int t2=r.u8(); fprintf(o," | %d",t2); if(t2==0){ auto L=r.var(); int pl=l; for(unsigned long long q=0;q<L;q++){ pl+=(int)r.var(); fprintf(o," %d",pl); } } else if(t2<=3) fprintf(o," %llu",r.var()); else fprintf(o," %u",r.u16()); fprintf(o," * %llu",r.var()); }
          unsigned long long z=r.var(); long long w=(long long)(z>>1)^-(long long)(z&1); fprintf(o," | w %lld",w); }
        else if(ch==5){ auto ne=r.var(); fprintf(o," ex"); for(unsigned long long j=0;j<ne;j++) fprintf(o," %llu",r.var()); auto L=r.var(); fprintf(o," cert "); for(unsigned long long j=0;j<L;j++) fprintf(o,"%02x",r.u8()); }
        else if(ch!=0 && ch!=2) fail("X choice "+to_string(ch));
        fprintf(o,"\n"); break; }
      case 0x23: { int l=child(); int ty=r.u8(); unsigned g=r.u8(); g|=r.u8()<<8; g|=r.u8()<<16; fprintf(o,"CN %d %d %u %u %u\n",l,ty,g>>18,(g>>9)&511,g&511); break; }
      case 0x24: { int l=child(); fprintf(o,"P %d %u\n",l,r.u16()); break; }
      case 0x25: fprintf(o,"TY %d\n",child()); break; case 0x26: fprintf(o,"DM %d\n",child()); break; case 0x28: fprintf(o,"DN %d\n",child()); break;
      case 0x27: { int l=child(); int ak=r.u8(); fprintf(o,"AF %d %d",l,ak); if(ak==1||ak==2){ int dm=r.u8(); fprintf(o," %d",dm); for(int j=0;j<dm;j++) fprintf(o," %u",r.u16()); } else fprintf(o," %d",r.u8()); fprintf(o,"\n"); break; }
      case 0x29: case 0x2A: fail("SKR / SKP in an item segment");
      case 0x2B: { auto L=r.var(); fprintf(o,"XPN "); for(unsigned long long j=0;j<L;j++) fprintf(o,"%02x",r.u8()); fprintf(o,"\n"); break; }
      case 0x2C: { unsigned l=r.u16(); fprintf(o,"RG %u\n",l); if(st.empty()) fail("RNG outside a node"); st.pop_back(); break; }
      case 0x2D: { int l=child(); fprintf(o,"JB %d %llu\n",l,r.var()); break; }   // a frontier job of a top segment (kind 4; r3cat.cc batch 8)   // the node's children from l on (and its END) are a range item
      default: fail("unknown tag "+to_string(t)); } } }
struct Glue {
  map<long long,Item>& I; string out; vector<Frame> st; Frame pend{0,0,0,string(),false,{}}; bool havePend=false; vector<int> base; long long nP=0, nQ=0, nW=0; bool wit=false;
  vector<long long> witAbove(size_t nf) const { vector<long long> W; for(size_t i=0;i<nf && i<st.size();i++) W.insert(W.end(),st[i].vr.begin(),st[i].vr.end()); sort(W.begin(),W.end()); W.erase(unique(W.begin(),W.end()),W.end()); return W; }   // rows of the first nf open frames
  explicit Glue(map<long long,Item>& m):I(m){}
  vector<int> prefixNow() const { vector<int> p=base; for(const Frame& f:st) if((int)p.size()<f.depth) p.push_back(f.label); return p; }
  void run(Item& X,size_t start,int depth){
    if(depth>200) fail("reference depth > 200");
    const string& bytes=X.recs; Rd r(bytes); r.i=start;
    while(r.more()){ const size_t a=r.i; const uint8_t tag=r.p[r.i];
      if(tag==0x28){ r.u8(); if(st.empty()) fail("item "+to_string(X.id)+": DON outside a node"); Frame& fr=st.back(); fr.ndOpen=false; const int c=fr.last+(int)r.var(); fr.last=c;
        vector<int> pk=prefixNow(); pk.push_back(c); auto it=X.pk.find(key(pk));
        if(it==X.pk.end()) fail("item "+to_string(X.id)+": DON at depth "+to_string(pk.size())+" label "+to_string(c)+" has no child piece in the manifest");
        Item& C=I.at(it->second); if(C.used) fail("item "+to_string(C.id)+" referenced twice"); C.used=true; nP++;
        if(wit){ if(witAbove(st.size())!=C.W) fail("item "+to_string(C.id)+": header witness differs from the VROWS rows at its donor node and the node's ancestors"); nW++; }   // r3cat_k12 wit
        run(C,0,depth+1); continue; }
      if(tag==0x29 || tag==0x2A) fail("item "+to_string(X.id)+": SKR / SKP in an item segment");
      if(tag==0x2C){ r.u8(); const int l=(int)r.u16(); if(st.empty()) fail("item "+to_string(X.id)+": RNG outside a node"); Frame& fr=st.back(); fr.ndOpen=false;
        const vector<int> S=prefixNow(); if((int)S.size()!=fr.depth) fail("item "+to_string(X.id)+": RNG below an unopened node");
        auto it=X.qk.find({key(S),l}); if(it==X.qk.end()) fail("item "+to_string(X.id)+": RNG at depth "+to_string(S.size())+" start "+to_string(l)+" has no child range in the manifest");
        Item& C=I.at(it->second); if(C.used) fail("item "+to_string(C.id)+" referenced twice"); C.used=true; nQ++;
        if(C.hp!=fr.last) fail("item "+to_string(C.id)+": delta base "+to_string(C.hp)+" != its node's last child label "+to_string(fr.last));
        if(X.kind=='Q' && (int)S.size()==(int)X.preL.size() && l<=X.hl) fail("item "+to_string(X.id)+": RNG "+to_string(l)+" at its own range root does not pass its start "+to_string(X.hl));   // SegOKO (c)
        if(C.recs.compare(0,C.ndEnd,fr.nd)!=0) fail("item "+to_string(C.id)+": node-data copy differs from its node's node data");
        if(wit){ if(witAbove(st.size()-1)!=C.W) fail("item "+to_string(C.id)+": header witness differs from the VROWS rows at its node's ancestors"); nW++; }   // the rows behind the node's inherited mask
        const size_t keep=st.size(); run(C,C.ndEnd,depth+1);
        if(st.size()!=keep-1) fail("item "+to_string(C.id)+": the range does not close its node");
        continue; }
      uint8_t t2; xqr3::skipRec(r,t2); out.append(bytes,a,r.i-a);
      if(t2==0x10 && wit && !havePend && !st.empty()){ Rd v(bytes); v.i=a+1; const auto n=v.var(); long long pr=0; st.back().vr.clear(); for(unsigned long long j=0;j<n;j++){ pr+=(long long)v.var(); st.back().vr.push_back(pr); } }   // VROWS after OPEN (r3cat_k12's rule)
      if(t2==0x10||t2==0x11||t2==0x12||t2==0x13||t2==0x2B){ if(!st.empty() && st.back().ndOpen) st.back().nd.append(bytes,a,r.i-a); continue; }
      if(!st.empty()) st.back().ndOpen=false;
      Rd q(bytes); q.i=a; q.u8();
      if(t2==0x01){ const unsigned x=q.u16(); const int d=(int)(x>>9), l=(int)(x&511); if(!st.empty() && st.back().depth>=d) fail("item "+to_string(X.id)+": NODE inside an unclosed node");
        if(!st.empty()){ if(st.back().depth!=d-1) fail("item "+to_string(X.id)+": NODE depth jump"); st.back().last=l; } pend=Frame{d,l,l,string(),false,{}}; havePend=true; }
      else if(t2==0x04){ if(!havePend) fail("item "+to_string(X.id)+": OPEN without NODE"); pend.ndOpen=true; st.push_back(pend); havePend=false; }
      else if(t2==0x05){ if(st.empty()) fail("item "+to_string(X.id)+": END without OPEN"); st.pop_back(); }
      else if(t2==0x02 || t2==0x03){ havePend=false; }
      else if(t2>=0x20 && t2<=0x27){ if(st.empty()) fail("item "+to_string(X.id)+": child record outside a node"); st.back().last+=(int)q.var(); } } } };

int main(int argc,char** argv){
  if(argc<2){ fprintf(stderr,"usage: r3qglue PLAN [--map HOST=DIR]... [--emit DIR] [--ref MD5FILE]... [--normcut] | r3qglue --md5bin HDRFILE STREAM... [--normcut]\n"); return 2; }
  string plan=argv[1], emit; map<int,string> ref;
  for(int a=(plan=="--md5bin" || plan=="--itemtext" || plan=="--text" || plan=="--mktop" || plan=="--itembin" || plan=="--itemkey"?1:2);a<argc;a++){ string s=argv[a];
    if(s=="--map" && a+1<argc){ string m=argv[++a]; auto e=m.find('='); if(e==string::npos){ fprintf(stderr,"--map HOST=DIR\n"); return 2; } MAPS[m.substr(0,e)]=m.substr(e+1); }
    else if(s=="--emit" && a+1<argc) emit=argv[++a];
    else if(s=="--normcut") NORMCUT=true;
    else if(s=="--root" && a+1<argc){ string v=argv[++a]; for(char& c:v) if(c==',') c=' '; istringstream is(v); int x; while(is>>x) TOPROOT.push_back(x); }
    else if(s=="--itemtext" && a+3<argc){   // --itemtext SEGFILE OFFSET LENGTH: one item segment as text: header lines of the segment file, then
      // #item ID kind K job J, #root J K labels... (as r3cat text), #dinh HEX (inherited dead mask, label bits, 8 x %016llx), #win N ROWS... (#pcwit files), #range L P (kind 3),
      // then the records (r3cat's text, plus "RG l" for a reference to a range child; "DN l" lines are references to child pieces)
      Item X; X.seg=string("-:")+argv[a+1]+":"+argv[a+2]+":"+argv[a+3]+":"; X.id=0; try{
        vector<string> f={"-",argv[a+1],argv[a+2],argv[a+3]}; SegFile& F=segFile("-",f[1]); const long long off=stoll(f[2]), len=stoll(f[3]);
        string b((size_t)len,'\0'); if(!preadAll(F.fd,&b[0],(size_t)len,off)) fail("segment beyond the end of the file");
        uint32_t mg, hl; memcpy(&mg,&b[0],4); memcpy(&hl,&b[4],4); if(mg!=0x49583352u) fail("no segment block at that offset");
        uint64_t n; memcpy(&n,&b[8+hl],8); if(8+(long long)hl+8+(long long)n+32!=len) fail("block length mismatch");
        const string recs=b.substr(8+hl+8,(size_t)n); uint8_t raw[32]; const string hex=xqr3::sha256hex(recs,raw); if(memcmp(raw,&b[8+hl+8+n],32)!=0) fail("records do not match the stored sha256");
        const string hs=b.substr(8,hl); Rd h(hs); unsigned long long iid=h.var(), job=h.var(); int kind=h.u8(), d0=h.u8(); vector<int> pre(d0); for(int i=0;i<d0;i++) pre[i]=(int)h.u16();
        uint64_t D[8]; for(int k=0;k<8;k++){ uint64_t w=0; for(int j=0;j<8;j++) w|=(uint64_t)h.u8()<<(8*j); D[k]=w; }
        vector<long long> W; if(F.pcwit){ const auto n=h.var(); long long pr=0; for(unsigned long long j=0;j<n;j++){ pr+=(long long)h.var(); W.push_back(pr); } } int rl=(int)h.u16(), rp=(int)h.u16();
        xqr3::gLeafx=F.leafx; xqr3::gCutx=F.cutx; xqr3::gLeafv7=F.leafv7;
        // the segment file's header lines (#lab, #table, #kept, #typecut, #leafx, #cutx), as r3cat text prints them
        { FILE* hf=fopen(F.path.c_str(),"rb"); char line[1<<16]; while(fgets(line,sizeof line,hf)){ string t(line); if(t.rfind("#end",0)==0) break; if(t.rfind("#R3XQ",0)==0) continue; fputs(line,stdout); } fclose(hf); }
        printf("#item %llu kind %d job %llu sha256 %s\n#root %llu %d",iid,kind,job,hex.c_str(),job,kind); for(int l:pre) printf(" %d",l);
        printf("\n#dinh"); for(int k=0;k<8;k++) printf("%s%016llx",k?"":" ",(unsigned long long)D[k]); printf("\n");
        if(F.pcwit){ printf("#win %zu",W.size()); for(long long x:W) printf(" %lld",x); printf("\n"); }   // batch 12: the witness rows of #dinh (row ids, ascending)
        vector<TF> st0; if(kind==3){ printf("#range %d %d\n",rl,rp); if(pre.empty()) fail("range without a node"); st0.push_back(TF{d0,pre.back(),rp}); }
        fflush(stdout); toTextQ(recs,stdout,st0); return 0;
      } catch(const exception& e){ fprintf(stderr,"r3qglue --itemtext: %s\n",e.what()); return 1; } }
    else if(s=="--itemkey" && a+3<argc){   // --itemkey SEGFILE OFFSET LENGTH: the item's interface (native track's key): "root LABELS lo L" (lo = the range
      // start for kind 3, else 0), one "ext LABELS" per DN child piece and per JB job (the child node's full prefix), one "rng LABELS L" per RG
      // (the node's prefix and the first label of its range child); labels as in the item header (u16 label indices)
      try{ SegFile& F=segFile("-",argv[a+1]); const long long off=stoll(argv[a+2]), len=stoll(argv[a+3]); string b((size_t)len,'\0');
        if(!preadAll(F.fd,&b[0],(size_t)len,off)) fail("segment beyond the end of the file"); uint32_t mg, hl; memcpy(&mg,&b[0],4); memcpy(&hl,&b[4],4); if(mg!=0x49583352u) fail("no segment block at that offset");
        uint64_t n; memcpy(&n,&b[8+hl],8); if(8+(long long)hl+8+(long long)n+32!=len) fail("block length mismatch"); const string recs=b.substr(8+hl+8,(size_t)n); uint8_t raw[32]; xqr3::sha256hex(recs,raw);
        if(memcmp(raw,&b[8+hl+8+n],32)!=0) fail("records do not match the stored sha256");
        const string hs=b.substr(8,hl); Rd h(hs); h.var(); h.var(); const int kind=h.u8(), d0=h.u8(); vector<int> pre(d0); for(int i=0;i<d0;i++) pre[i]=(int)h.u16();
        for(int k=0;k<64;k++) h.u8(); if(F.pcwit){ const auto nw=h.var(); for(unsigned long long j=0;j<nw;j++) h.var(); } const int rl=(int)h.u16(), rp=(int)h.u16();
        xqr3::gLeafx=F.leafx; xqr3::gCutx=F.cutx; xqr3::gLeafv7=F.leafv7; string o; auto put=[&](const char* t,const vector<int>& p,int x){ o+=t; for(int l:p){ o+=' '; o+=to_string(l); } if(x>=0){ o+=' '; o+=to_string(x); } o+='\n'; };
        o+="root"; for(int l:pre){ o+=' '; o+=to_string(l); } o+=" lo "+to_string(kind==3?rl:0)+"\n";
        vector<int> base(pre.begin(),pre.end()); if(!base.empty()) base.pop_back(); vector<TF> st; TF pend{0,0,0}; bool hp=false;
        if(kind==3){ if(pre.empty()) fail("range without a node"); st.push_back(TF{d0,pre.back(),rp}); }
        auto pfx=[&](){ vector<int> p=base; for(const TF& f:st) if((int)p.size()<f.depth) p.push_back(f.label); return p; };
        Rd r(recs);
        while(r.more()){ const size_t a0=r.i; const uint8_t t=r.p[r.i];
          if(t==0x28){ r.u8(); if(st.empty()) fail("DN outside a node"); st.back().last+=(int)r.var(); vector<int> p=pfx(); p.push_back(st.back().last); put("ext",p,-1); continue; }
          if(t==0x2C){ r.u8(); const int l=(int)r.u16(); if(st.empty()) fail("RG outside a node"); put("rng",pfx(),l); st.pop_back(); continue; }
          uint8_t t2; xqr3::skipRec(r,t2); Rd q(recs); q.i=a0; q.u8();
          if(t2==0x01){ const unsigned x=q.u16(); const int d=(int)(x>>9), l=(int)(x&511); if(!st.empty()) st.back().last=l; pend=TF{d,l,l}; hp=true; }
          else if(t2==0x04){ if(!hp) fail("OPEN without NODE"); st.push_back(pend); hp=false; }
          else if(t2==0x05){ if(st.empty()) fail("END without OPEN"); st.pop_back(); }
          else if(t2==0x02 || t2==0x03){ hp=false; }
          else if((t2>=0x20 && t2<=0x27) || t2==0x2D){ if(st.empty()) fail("child record outside a node"); st.back().last+=(int)q.var(); if(t2==0x2D){ vector<int> p=pfx(); p.push_back(st.back().last); put("ext",p,-1); } } }
        if(!st.empty()) fail("the item does not close its nodes");
        fwrite(o.data(),1,o.size(),stdout); return 0;
      } catch(const exception& e){ fprintf(stderr,"r3qglue --itemkey: %s\n",e.what()); return 1; } }
    else if(s=="--itembin" && a+4<argc){   // --itembin SEGFILE OFFSET LENGTH OUT: the item's block as stored ([u32 'R3XI'][u32 hlen][header][u64 n][records]
      // [sha256]), after checking magic, length and sha256 (for checkers that read the binary records directly; QUEUE.md §3 layout)
      try{ SegFile& F=segFile("-",argv[a+1]); const long long off=stoll(argv[a+2]), len=stoll(argv[a+3]); string b((size_t)len,'\0');
        if(!preadAll(F.fd,&b[0],(size_t)len,off)) fail("segment beyond the end of the file"); uint32_t mg, hl; memcpy(&mg,&b[0],4); memcpy(&hl,&b[4],4); if(mg!=0x49583352u) fail("no segment block at that offset");
        uint64_t n; memcpy(&n,&b[8+hl],8); if(8+(long long)hl+8+(long long)n+32!=len) fail("block length mismatch"); uint8_t raw[32]; xqr3::sha256hex(b.substr(8+hl+8,(size_t)n),raw);
        if(memcmp(raw,&b[8+hl+8+n],32)!=0) fail("records do not match the stored sha256");
        FILE* o=fopen(argv[a+4],"wb"); if(!o) fail(string("cannot write ")+argv[a+4]); fwrite(b.data(),1,b.size(),o); fclose(o); return 0;
      } catch(const exception& e){ fprintf(stderr,"r3qglue --itembin: %s\n",e.what()); return 1; } }
    else if(s=="--mktop" && a+3<argc){   // --mktop PCERT DUMP OUT.xq [HOST]: every complete kind-4 segment of a --pctop run's pcert becomes an item block in
      // OUT.xq (header kind 4, job = PFILE line, prefix, zero mask); each JOB's path is checked against its DUMP line; listing on stdout, one line
      // per segment: "T i d v1..vd seg=HOST:OUT:OFF:LEN:SHA256 dump=FIRST:COUNT nodes=N" (prefix as codes; input of xqctl addtop)
      const string pc=argv[a+1], dumpf=argv[a+2], outf=argv[a+3], host=(a+4<argc?argv[a+4]:"-");
      try{ FILE* hf=fopen(pc.c_str(),"rb"); if(!hf) fail("cannot open "+pc); char line[1<<16]; string hdrl, fp="0"; vector<int> lab; bool lx=false, cx=false;
        bool pw=false, l7=false;
        while(fgets(line,sizeof line,hf)){ string t(line); if(t.rfind("#end",0)==0) break; istringstream is(t); string k; is>>k;
          if(k=="#R3PC"){ string v,f2; is>>v>>f2; if(f2.rfind("fp=",0)==0) fp=f2.substr(3); continue; }
          if(k=="#lab"){ int n; is>>n; lab.resize(n); for(int i=0;i<n;i++) is>>lab[i]; } else if(k=="#leafx") lx=true; else if(k=="#cutx") cx=true; else if(k=="#pcwit") pw=true; else if(k=="#leafv7") l7=true; else if(k=="#src") continue;
          hdrl+=t; }
        fclose(hf); if(lab.empty()) fail(pc+": no #lab line"); xqr3::gLeafx=lx; xqr3::gCutx=cx; xqr3::gLeafv7=l7;
        map<long long,vector<int>> dump; { ifstream df(dumpf); string ln; while(getline(df,ln)){ istringstream is(ln); long long ix; if(!(is>>ix)) continue; vector<int> v; int x; while(is>>x) v.push_back(x); dump[ix]=v; } }
        xqr3::PFileQ G; G.open_(pc); vector<pair<int,unsigned long long>> segs;
        for(auto& kv:G.seg) if(kv.second.kind==4){ if(!kv.second.last) fail("kind-4 segment "+to_string(kv.first)+" (PFILE line "+to_string(kv.second.job)+") is incomplete"); segs.push_back({kv.second.job,kv.first}); }
        sort(segs.begin(),segs.end()); for(size_t i=1;i<segs.size();i++) if(segs[i].first==segs[i-1].first) fail("two kind-4 segments for PFILE line "+to_string(segs[i].first));
        FILE* o=fopen(outf.c_str(),"ab"); if(!o) fail("cannot write "+outf); if(ftell(o)==0){ fprintf(o,"#R3XQ 1 fp=%s compat=0 run=pctop pcert=%s\n%s#end\n",fp.c_str(),pc.c_str(),hdrl.c_str()); }
        long long njob=0;
        for(auto& sg:segs){ const xqr3::Seg& S=G.seg.at(sg.second); const string recs=G.all(S);
          // walk: JOB paths against DUMP, the JOB index range, the node count
          vector<int> base(S.pre.begin(),S.pre.end()); if(base.empty()) fail("kind-4 segment with an empty prefix"); base.pop_back();
          vector<TF> st; TF pend{0,0,0}; bool hp=false; long long lo=-1, hi=-1, cnt=0, nodes=0; Rd r(recs);
          while(r.more()){ const size_t a0=r.i; uint8_t t2; xqr3::skipRec(r,t2); Rd q(recs); q.i=a0; q.u8();
            if(t2==0x01){ unsigned x=q.u16(); int d=x>>9, l=x&511; if(!st.empty()) st.back().last=l; pend={d,l,l}; hp=true; nodes++; }
            else if(t2==0x04){ if(!hp) fail("OPEN without NODE"); st.push_back(pend); hp=false; } else if(t2==0x05){ if(st.empty()) fail("END without OPEN"); st.pop_back(); }
            else if(t2==0x02 || t2==0x03){ hp=false; }
            else if(t2==0x28 || t2==0x29 || t2==0x2A || t2==0x2C) fail("DON / SKR / SKP / RNG in a top segment");
            else if((t2>=0x20 && t2<=0x27) || t2==0x2D){ if(st.empty()) fail("child record outside a node"); st.back().last+=(int)q.var();
              if(t2==0x2D){ const long long ix=(long long)q.var(); vector<int> pv=base; for(const TF& f:st) if((int)pv.size()<f.depth) pv.push_back(f.label); pv.push_back(st.back().last);
                auto di=dump.find(ix); if(di==dump.end()) fail("JOB "+to_string(ix)+" is not in "+dumpf); if(di->second.size()!=pv.size()) fail("JOB "+to_string(ix)+": depth differs from its DUMP line");
                for(size_t k=0;k<pv.size();k++) if(lab[pv[k]]!=di->second[k]) fail("JOB "+to_string(ix)+": path differs from its DUMP line");
                if(lo<0 || ix<lo) lo=ix; if(ix>hi) hi=ix; cnt++; } } }
          if(!st.empty()) fail("top segment of PFILE line "+to_string(sg.first)+" does not close");
          if(cnt && hi-lo+1!=cnt) fail("JOB indices of PFILE line "+to_string(sg.first)+" are not one range");
          string hdr; auto pv=[&](unsigned long long x){ do{ unsigned char c=x&127; x>>=7; if(x) c|=128; hdr.push_back((char)c); } while(x); };
          pv(0); pv((unsigned long long)S.job); hdr.push_back((char)4); hdr.push_back((char)S.pre.size()); for(int l:S.pre){ hdr.push_back((char)(l&255)); hdr.push_back((char)(l>>8)); }
          hdr.append(64,'\0'); if(pw) hdr.push_back('\0'); hdr.append(4,'\0');   // #pcwit: no witness rows (n = 0)
          uint8_t raw[32]; const string hex=xqr3::sha256hex(recs,raw); const long long off=ftell(o); const uint32_t h2[2]={0x49583352u,(uint32_t)hdr.size()}; const uint64_t n=recs.size();
          fwrite(h2,4,2,o); fwrite(hdr.data(),1,hdr.size(),o); fwrite(&n,8,1,o); fwrite(recs.data(),1,recs.size(),o); fwrite(raw,1,32,o);
          const long long len=8+(long long)hdr.size()+8+(long long)recs.size()+32;
          char abspath[4096]; const string ap=realpath(outf.c_str(),abspath)?string(abspath):outf;
          printf("T %d %zu",S.job,S.pre.size()); for(int l:S.pre) printf(" %d",lab[l]); printf(" seg=%s:%s:%lld:%lld:%s dump=%lld:%lld nodes=%lld\n",host.c_str(),ap.c_str(),off,len,hex.c_str(),lo<0?0:lo,cnt,nodes); njob+=cnt; }
        fflush(o); fsync(fileno(o)); fclose(o); fprintf(stderr,"r3qglue --mktop: %zu top segments, %lld JOBs, written to %s\n",segs.size(),njob,outf.c_str()); return 0;
      } catch(const exception& e){ fprintf(stderr,"r3qglue --mktop: %s\n",e.what()); return 1; } }
    else if(s=="--text" && a+2<argc){   // --text HDRFILE STREAM: an assembled stream (--emit, r3cat job) as text (for comparisons with r3cat textbin)
      try{ SegFile& F=segFile("-",argv[a+1]); xqr3::gLeafx=F.leafx; xqr3::gCutx=F.cutx; xqr3::gLeafv7=F.leafv7; ifstream g(argv[a+2],ios::binary); string x((istreambuf_iterator<char>(g)),istreambuf_iterator<char>());
        printf("#lab"); for(int v:F.lab) printf(" %d",v); printf("\n"); toTextQ(x,stdout,{}); return 0; }
      catch(const exception& e){ fprintf(stderr,"r3qglue --text: %s\n",e.what()); return 1; } }
    else if(s=="--md5bin" && a+1<argc){   // --md5bin HDRFILE STREAM...: md5 of assembled binary streams (r3cat job output), after --normcut if given
      FILE* f=fopen(argv[++a],"rb"); if(!f){ fprintf(stderr,"cannot open %s\n",argv[a]); return 2; } char line[1<<16];
      while(fgets(line,sizeof line,f)){ string h(line); if(h.rfind("#end",0)==0) break; if(h.rfind("#leafx",0)==0) xqr3::gLeafx=true; if(h.rfind("#cutx",0)==0) xqr3::gCutx=true; if(h.rfind("#leafv7",0)==0) xqr3::gLeafv7=true; } fclose(f);
      for(int b=a+1;b<argc;b++){ if(string(argv[b])=="--normcut"){ NORMCUT=true; continue; } }
      for(int b=a+1;b<argc;b++){ if(string(argv[b])=="--normcut") continue; ifstream g(argv[b],ios::binary); string x((istreambuf_iterator<char>(g)),istreambuf_iterator<char>());
        try{ const string y=normCut(x); printf("%s %s %zu\n",argv[b],md5hex(y).c_str(),y.size()); } catch(const exception& e){ printf("%s FAIL %s\n",argv[b],e.what()); } }
      return 0; }
    else if(s=="--ref" && a+1<argc){ ifstream f(argv[++a]); string line; while(getline(f,line)){ istringstream is(line); int ix; string m; if(is>>ix>>m && m.size()==32) ref[ix]=m; } }
    else { fprintf(stderr,"unknown option %s\n",s.c_str()); return 2; } }
  // plan
  struct Top { string pool, space, seg, dump; int i=0; long long id=0; vector<int> preV; };
  vector<Top> tops;   // top segments (--pctop, xqctl addtop): each JOB resolves to the top segment or job root at its prefix
  vector<Job> jobs; map<long long,Item> I; { ifstream f(plan); string line; bool hdr=false;
    while(getline(f,line)){ if(line.rfind("#r3qplan 1",0)==0){ hdr=true; continue; } istringstream is(line); string t; if(!(is>>t)) continue;
      if(t=="J"){ Job J; is>>J.pool>>J.space>>J.ix>>J.root>>J.n>>J.l>>J.p; if(!is){ fprintf(stderr,"bad plan line: %s\n",line.c_str()); return 2; } jobs.push_back(J); }
      else if(t=="T"){ Top T; int d; is>>T.pool>>T.space>>T.i>>T.id>>d; T.preV.resize(d); for(int k=0;k<d;k++) is>>T.preV[k]; string w; while(is>>w){ if(w.rfind("seg=",0)==0) T.seg=w.substr(4); else if(w.rfind("dump=",0)==0) T.dump=w.substr(5); }
        if(T.seg.empty() || T.dump.empty()){ fprintf(stderr,"bad plan line: %s\n",line.c_str()); return 2; } tops.push_back(T); }
      else if(t=="I"){ if(jobs.empty()){ fprintf(stderr,"plan: item before a job\n"); return 2; } Item X; int d; is>>X.id>>X.parent>>X.kind>>X.rsV>>X.rpV>>d; X.preV.resize(d); for(int i=0;i<d;i++) is>>X.preV[i];
        string w; while(is>>w){ if(w.rfind("dinh=",0)==0) X.dinh=w.substr(5); else if(w.rfind("win=",0)==0) X.win=w.substr(4); else if(w.rfind("seg=",0)==0) X.seg=w.substr(4); else if(w.rfind("chk=",0)==0) X.chk=w.substr(4); }
        if(!is.eof() || X.seg.empty()){ fprintf(stderr,"bad plan line: %s\n",line.c_str()); return 2; }
        jobs.back().items.push_back(X.id); I[X.id]=X; } }
    if(!hdr){ fprintf(stderr,"%s: not an r3qglue plan (xqaudit.py --plan)\n",plan.c_str()); return 2; } }
  int bad=0, refOK=0, refBad=0, noRef=0; long long totB=0, totI=0, totW=0;
  for(Job& J:jobs){
    try{
      for(long long id:J.items){ Item& X=I.at(id); if(X.parent && id!=J.root) I.at(X.parent).kids.push_back(id); }
      SegFile* F0=nullptr;
      for(long long id:J.items){ Item& X=I.at(id); loadSeg(X,J.ix);
        if(!F0){ F0=X.F; xqr3::gLeafx=F0->leafx; xqr3::gCutx=F0->cutx; xqr3::gLeafv7=F0->leafv7; }
        else if(X.F!=F0 && (X.F->compat!=F0->compat || X.F->lab!=F0->lab || X.F->typecut!=F0->typecut || X.F->leafx!=F0->leafx || X.F->cutx!=F0->cutx || X.F->pcwit!=F0->pcwit || X.F->leafv7!=F0->leafv7))
          fail("item "+to_string(id)+": its segment file "+X.F->path+" has another header than "+F0->path); }
      for(long long id:J.items){ Item& X=I.at(id);
        for(long long c:X.kids){ Item& C=I.at(c);
          if(C.kind=='P'){ if(!X.pk.emplace(key(C.preL),c).second) fail("item "+to_string(id)+": two child pieces with one prefix"); }
          else if(C.kind=='Q'){ if(!X.qk.emplace(make_pair(key(C.preL),C.hl),c).second) fail("item "+to_string(id)+": two child ranges at one node and start"); }
          else fail("item "+to_string(c)+": child of kind "+C.kind); } }
      Item& R=I.at(J.root); if(R.kind!='J') fail("job root "+to_string(J.root)+" is not a J item");
      Glue G(I); G.base=R.preL; if(!G.base.empty()) G.base.pop_back(); R.used=true; G.wit=F0 && F0->pcwit;
      G.run(R,0,0); if(!G.st.empty()) fail("unclosed node at the end of the job");
      for(long long id:J.items) if(!I.at(id).used) fail("item "+to_string(id)+" is never referenced");
      if(NORMCUT) G.out=normCut(G.out);
      const string m=md5hex(G.out); totB+=G.out.size(); totI+=J.items.size();
      string rs; auto ri=ref.find(J.ix); if(!ref.empty()){ if(ri==ref.end()){ rs=" ref -"; noRef++; } else if(ri->second==m){ rs=" ref identical"; refOK++; } else { rs=" ref DIFFERS "+ri->second; refBad++; } }
      printf("%s %d %s %zu items %zu P %lld Q %lld%s%s\n",J.pool.c_str(),J.ix,m.c_str(),G.out.size(),J.items.size(),G.nP,G.nQ,G.wit?(" wit "+to_string(G.nW)).c_str():"",rs.c_str()); totW+=G.nW;
      if(!emit.empty()){ const string p=emit+"/"+J.pool+"_"+to_string(J.ix)+".r3j"; FILE* o=fopen(p.c_str(),"wb"); if(!o) fail("cannot write "+p); fwrite(G.out.data(),1,G.out.size(),o); fclose(o); }
      for(long long id:J.items){ Item& X=I.at(id); string().swap(X.recs); }
    } catch(const exception& e){ bad++; printf("%s %d FAIL %s\n",J.pool.c_str(),J.ix,e.what()); for(long long id:J.items){ string().swap(I.at(id).recs); } }
    fflush(stdout); }
  // top segments: every JOB resolves to exactly one job root (kind 0, not a replay cut) or top segment at its prefix; checks of the kernel track:
  // prefix = parent prefix ||| u with u = the JOB's label, an open node (job root or top segment) of <= 21 labels; ix in the segment's DUMP range,
  // DUMP line = the path; every job root and every top segment but the root referenced exactly once
  int tbad=0; long long tjobs=0; map<long long,int> tref; map<vector<int>,pair<char,long long>> rootAt;   // codes -> (J|T, id)
  for(Job& J:jobs){ Item& R=I.at(J.root); rootAt[R.preV]={'J',J.root}; }
  for(Top& T:tops){ if(rootAt.count(T.preV)){ printf("TOP %s %d FAIL prefix also roots item %lld\n",T.pool.c_str(),T.i,rootAt[T.preV].second); tbad++; } else rootAt[T.preV]={'T',T.id}; }
  map<string,map<long long,vector<int>>> dumps;
  for(Top& T:tops){
    try{
      vector<string> f; { string q; for(char c:T.seg){ if(c==':'){ f.push_back(q); q.clear(); } else q+=c; } f.push_back(q); } if(f.size()!=5) fail("bad segment reference");
      SegFile& F=segFile(f[0],f[1]); const long long off=stoll(f[2]), len=stoll(f[3]); string b((size_t)len,'\0'); if(!preadAll(F.fd,&b[0],(size_t)len,off)) fail("segment beyond the end of "+F.path);
      uint32_t mg, hl; memcpy(&mg,&b[0],4); memcpy(&hl,&b[4],4); if(mg!=0x49583352u) fail("no segment block"); uint64_t n; memcpy(&n,&b[8+hl],8);
      const string recs=b.substr(8+hl+8,(size_t)n); uint8_t raw[32]; if(xqr3::sha256hex(recs,raw)!=f[4] || memcmp(raw,&b[8+hl+8+n],32)!=0) fail("sha256 mismatch");
      const string hs=b.substr(8,hl); Rd h(hs); h.var(); const long long job=(long long)h.var(); const int kind=h.u8(), d0=h.u8(); vector<int> pre(d0); for(int k=0;k<d0;k++) pre[k]=(int)h.u16();
      if(kind!=4 || job!=T.i) fail("not the kind-4 segment of PFILE line "+to_string(T.i)); if((int)T.preV.size()!=d0) fail("prefix depth differs");
      for(int k=0;k<d0;k++) if(F.lab[pre[k]]!=T.preV[k]) fail("prefix differs from the manifest's");
      // DUMP range PATH:SHA:FIRST:COUNT
      const size_t c3=T.dump.rfind(':'), c2=T.dump.rfind(':',c3-1), c1=T.dump.rfind(':',c2-1); const string dpath=T.dump.substr(0,c1); const long long first=stoll(T.dump.substr(c2+1,c3-c2-1)), count=stoll(T.dump.substr(c3+1));
      if(!dumps.count(dpath)){ ifstream df(dpath); if(!df) fail("cannot read DUMP "+dpath); string ln; auto& dm=dumps[dpath]; while(getline(df,ln)){ istringstream is(ln); long long ix; if(!(is>>ix)) continue; vector<int> v; int x; while(is>>x) v.push_back(x); dm[ix]=v; } }
      auto& dm=dumps[dpath]; xqr3::gLeafx=F.leafx; xqr3::gCutx=F.cutx; xqr3::gLeafv7=F.leafv7;
      vector<int> base(pre.begin(),pre.end()); base.pop_back(); vector<TF> st; TF pend{0,0,0}; bool hp=false; long long nj=0; Rd r(recs);
      while(r.more()){ const size_t a0=r.i; uint8_t t2; xqr3::skipRec(r,t2); Rd q(recs); q.i=a0; q.u8();
        if(t2==0x01){ unsigned x=q.u16(); int d=x>>9, l=x&511; if(!st.empty()) st.back().last=l; pend={d,l,l}; hp=true; }
        else if(t2==0x04){ if(!hp) fail("OPEN without NODE"); st.push_back(pend); hp=false; } else if(t2==0x05){ if(st.empty()) fail("END without OPEN"); st.pop_back(); }
        else if(t2==0x02 || t2==0x03){ hp=false; }
        else if(t2==0x28 || t2==0x29 || t2==0x2A || t2==0x2C) fail("DON / SKR / SKP / RNG in a top segment");
        else if((t2>=0x20 && t2<=0x27) || t2==0x2D){ if(st.empty()) fail("child record outside a node"); st.back().last+=(int)q.var();
          if(t2==0x2D){ const long long ix=(long long)q.var(); const int u=st.back().last; vector<int> pl=base; for(const TF& fr:st) if((int)pl.size()<fr.depth) pl.push_back(fr.label); pl.push_back(u);
            if(pl.size()>21) fail("JOB "+to_string(ix)+" below depth 21"); vector<int> pv; for(int l:pl) pv.push_back(F.lab[l]);
            if(ix<first || ix>=first+count) fail("JOB "+to_string(ix)+" outside the segment's DUMP range");
            auto di=dm.find(ix); if(di==dm.end() || di->second!=pv) fail("JOB "+to_string(ix)+": path differs from its DUMP line");
            auto ri=rootAt.find(pv); if(ri==rootAt.end()) fail("JOB "+to_string(ix)+" at depth "+to_string(pv.size())+" has no job root or top segment");
            if(ri->second.first=='J'){ Item& R=I.at(ri->second.second); if(R.hkind<0){ vector<string> g; string w; for(char c:R.seg){ if(c==':'){ g.push_back(w); w.clear(); } else w+=c; } g.push_back(w);
                SegFile& G=segFile(g[0],g[1]); char hb[64]; if(!preadAll(G.fd,hb,sizeof hb,stoll(g[2]))) fail("job root segment unreadable"); string hh(hb+8,56); Rd hr(hh); hr.var(); hr.var(); R.hkind=hr.u8(); }
              if(R.hkind!=0) fail("JOB "+to_string(ix)+" resolves to job root "+to_string(R.id)+" of segment kind "+to_string(R.hkind)+" (a replay cut is not an open node)"); }
            tref[ri->second.second]++; nj++; } } }
      if(!st.empty()) fail("the segment does not close"); if(nj!=count) fail("its JOBs ("+to_string(nj)+") are not its DUMP range ("+to_string(count)+")");
      tjobs+=nj; printf("TOP %s %d %s %zu JOBs %lld\n",T.pool.c_str(),T.i,md5hex(recs).c_str(),recs.size(),nj);
    } catch(const exception& e){ tbad++; printf("TOP %s %d FAIL %s\n",T.pool.c_str(),T.i,e.what()); } }
  if(!tops.empty()){ int nroot=0;
    for(Job& J:jobs){ int k=tref[J.root]; if(k!=1){ tbad++; printf("TOP: job %s %d (item %lld) has %d JOBs pointing at it\n",J.pool.c_str(),J.ix,J.root,k); } }
    for(Top& T:tops){ int k=tref[T.id]; if(k>1){ tbad++; printf("TOP: top segment %s %d has %d JOBs pointing at it\n",T.pool.c_str(),T.i,k); } if(k==0){ nroot++;
        if(!TOPROOT.empty() && T.preV!=TOPROOT){ tbad++; printf("TOP: top segment %s %d is not referenced and is not the root\n",T.pool.c_str(),T.i); } } }
    if(!TOPROOT.empty() && nroot!=1){ tbad++; printf("TOP: %d unreferenced top segments, expected the root alone\n",nroot); }
    printf("TOPS %zu top segments, %lld JOBs, %d roots, %d failures\n",tops.size(),tjobs,nroot,tbad); bad+=tbad; }
  printf("GLUE %zu jobs, %d failed, %lld items, %lld bytes",jobs.size(),bad,totI,totB); if(totW) printf(", %lld header witnesses equal to the recomputed ones",totW);
  if(!ref.empty()) printf("; reference: %d identical, %d differ, %d without a reference line",refOK,refBad,noRef);
  printf("\n"); return (bad || refBad)?1:0; }
