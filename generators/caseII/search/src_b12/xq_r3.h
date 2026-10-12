// xq_r3.h: certificate-stream side of prof7R3q (prof7R3 + the item queue; r22/lean/rerun/r3/QUEUE.md).  Included once, by prof7R3q.cc.
//  - sha256 (FIPS 180-4), for the item segments' hashes in the manifest;
//  - the record walker r3rec.h (shared with r3cat.cc: every tag's length, including 0x2C RNG u16 l);
//  - PFileQ: r3cat's reader of an earlier --pcert file (journal skip references SKR / SKP of resumed list jobs);
//  - the item assembler: an item's canonical own-part segment = its root segment's records with the run's local pieces (DON whose
//    piece ran here), SKR and SKP inlined; DON of queue items and RNG stay as references (glued by prefix through the manifest).
#pragma once
#include <bits/stdc++.h>
#include <unistd.h>
#include <fcntl.h>
#include <dirent.h>
#include <nmmintrin.h>
namespace xqr3 {

// ---------------- sha256 ----------------
struct Sha256 { uint32_t h[8]; uint64_t len=0; uint8_t buf[64]; size_t bl=0;
  Sha256(){ static const uint32_t H0[8]={0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19}; memcpy(h,H0,32); }
  static uint32_t ror(uint32_t x,int n){ return (x>>n)|(x<<(32-n)); }
  void block(const uint8_t* p){ static const uint32_t K[64]={0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
      0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,
      0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,
      0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,
      0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,
      0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};
    uint32_t w[64]; for(int i=0;i<16;i++) w[i]=(uint32_t)p[4*i]<<24|(uint32_t)p[4*i+1]<<16|(uint32_t)p[4*i+2]<<8|p[4*i+3];
    for(int i=16;i<64;i++){ uint32_t s0=ror(w[i-15],7)^ror(w[i-15],18)^(w[i-15]>>3), s1=ror(w[i-2],17)^ror(w[i-2],19)^(w[i-2]>>10); w[i]=w[i-16]+s0+w[i-7]+s1; }
    uint32_t a=h[0],b=h[1],c=h[2],d=h[3],e=h[4],f=h[5],g=h[6],k=h[7];
    for(int i=0;i<64;i++){ uint32_t S1=ror(e,6)^ror(e,11)^ror(e,25), ch=(e&f)^(~e&g), t1=k+S1+ch+K[i]+w[i], S0=ror(a,2)^ror(a,13)^ror(a,22), mj=(a&b)^(a&c)^(b&c), t2=S0+mj;
      k=g; g=f; f=e; e=d+t1; d=c; c=b; b=a; a=t1+t2; }
    h[0]+=a; h[1]+=b; h[2]+=c; h[3]+=d; h[4]+=e; h[5]+=f; h[6]+=g; h[7]+=k; }
  void add(const void* data,size_t n){ const uint8_t* p=(const uint8_t*)data; len+=n;
    while(n){ size_t t=std::min(n,64-bl); memcpy(buf+bl,p,t); bl+=t; p+=t; n-=t; if(bl==64){ block(buf); bl=0; } } }
  void fin(uint8_t out[32]){ uint64_t bits=len*8; uint8_t pad=0x80; add(&pad,1); uint8_t z=0; while(bl!=56) add(&z,1);
    uint8_t L[8]; for(int i=0;i<8;i++) L[i]=(uint8_t)(bits>>(56-8*i)); add(L,8); for(int i=0;i<8;i++){ out[4*i]=h[i]>>24; out[4*i+1]=h[i]>>16; out[4*i+2]=h[i]>>8; out[4*i+3]=h[i]; } } };
static std::string sha256hex(const std::string& s,uint8_t raw[32]){ Sha256 S; S.add(s.data(),s.size()); S.fin(raw); static const char* X="0123456789abcdef"; std::string o; for(int i=0;i<32;i++){ o+=X[raw[i]>>4]; o+=X[raw[i]&15]; } return o; }

// ---------------- record walker: r22/lean/rerun/r3/r3rec.h (shared with r3cat.cc; every tag, 2C RNG, #leafx / #cutx extras) ----------------
struct QErr : std::runtime_error { using std::runtime_error::runtime_error; };
[[noreturn]] static void fail(const std::string& m){ throw QErr(m); }
[[noreturn]] static void die(const std::string& m){ throw QErr(m); }   // r3rec.h's error hook: an assembly error, not an exit
using std::string; using std::to_string;
#include "r3rec.h"   // Rd, skipFk, skipRec, gLeafx, gCutx (set from the run's options before any assembly)

// ---------------- an earlier --pcert file (r3cat's PFile, for SKR / SKP) ----------------
static uint32_t crc32c(const void* p,size_t n){ uint64_t c=0xFFFFFFFFu; const uint8_t* b=(const uint8_t*)p; size_t i=0;
  for(;i+8<=n;i+=8){ uint64_t x; memcpy(&x,b+i,8); c=_mm_crc32_u64(c,x); } for(;i<n;i++) c=_mm_crc32_u8((uint32_t)c,b[i]); return (uint32_t)c^0xFFFFFFFFu; }
struct Chunk { uint32_t idx; long long off; uint32_t len; };
struct Seg { unsigned long long id=0; int job=-1, kind=-1, d0=0; std::vector<int> pre; std::vector<long long> win; int rl=0, rp=0; std::vector<Chunk> ch; bool last=false; long long bytes=0; };   // win: header witness (#pcwit); rl, rp: a range's start and delta base (kind 3)
struct PFileQ { std::string path; int fd=-1; std::map<int,std::string> src; std::unordered_map<unsigned long long,Seg> seg; long long fsize=0, nskip=0; bool pcwit=false;
  void open_(const std::string& p){ path=p; fd=::open(p.c_str(),O_RDONLY); if(fd<0) fail("cannot open "+p); fsize=lseek(fd,0,SEEK_END);
    FILE* f=fopen(p.c_str(),"rb"); if(!f) fail("cannot open "+p); char line[1<<16]; long long pos=0; bool end=false, lx=false, cx=false;
    while(fgets(line,sizeof line,f)){ pos+=strlen(line); std::string s(line); if(s.rfind("#end",0)==0){ end=true; break; } std::istringstream is(s); std::string t; is>>t; if(t=="#src"){ int k; std::string q; is>>k>>q; src[k]=q; } else if(t=="#leafx") lx=true; else if(t=="#cutx") cx=true; else if(t=="#pcwit") pcwit=true; }
    fclose(f); if(!end) fail(p+": no #end header line");
    if(lx!=gLeafx || cx!=gCutx) fail(p+": its #leafx / #cutx flags differ from this run's");
    long long o=pos; std::vector<uint8_t> buf;
    while(o+12<=fsize){ uint32_t h[3]; if(pread(fd,h,12,o)!=12) break; if(h[0]!=0x31423352u || o+12+(long long)h[1]>fsize) break;
      buf.resize(h[1]); if(pread(fd,buf.data(),h[1],o+12)!=(ssize_t)h[1]) break;
      if(crc32c(buf.data(),h[1])!=h[2]){ nskip++; o+=12+h[1]; continue; }   // a punched block (a helper frees a finished unit's records, --xqpunch) or a damaged one: skipped, its segment stays incomplete
      unsigned long long id; uint32_t ci; memcpy(&id,&buf[0],8); memcpy(&ci,&buf[8],4); uint8_t fl=buf[12]; size_t q=13; Seg& S=seg[id]; S.id=id;
      if(fl&1){ auto rv=[&](){ unsigned long long x=0; int sh=0; while(true){ uint8_t c=buf[q++]; x|=(unsigned long long)(c&127)<<sh; if(!(c&128)) break; sh+=7; } return x; };
        S.job=(int)rv(); S.kind=buf[q++]; S.d0=buf[q++]; S.pre.resize(S.d0); for(int i=0;i<S.d0;i++){ S.pre[i]=buf[q]|(buf[q+1]<<8); q+=2; } q+=64;
        if(pcwit){ auto n=rv(); long long pr=0; S.win.clear(); for(unsigned long long j=0;j<n;j++){ pr+=(long long)rv(); S.win.push_back(pr); } }   // batch 12: the witness rows of the mask
        if(S.kind==3){ S.rl=buf[q]|(buf[q+1]<<8); S.rp=buf[q+2]|(buf[q+3]<<8); q+=4; } }   // prof7R3q: a range's u16 l, u16 p (R3's own files have no kind 3)
      S.ch.push_back({ci,o+12+(long long)q,(uint32_t)(h[1]-q)}); S.bytes+=h[1]-q; if(fl&2) S.last=true; o+=12+h[1]; }
    for(auto& kv:seg){ auto& c=kv.second.ch; std::sort(c.begin(),c.end(),[](const Chunk& a,const Chunk& b){ return a.idx<b.idx; }); for(size_t i=0;i<c.size();i++) if(c[i].idx!=i){ kv.second.last=false; break; } } }
  std::string read(const Seg& S,long long b,long long e) const { std::string out; long long p=0;
    for(const Chunk& c:S.ch){ long long cb=p, ce=p+c.len; p=ce; if(ce<=b || cb>=e) continue; long long s0=std::max(b,cb), s1=std::min(e,ce); size_t n=(size_t)(s1-s0), o0=out.size(); out.resize(o0+n);
      if(pread(fd,&out[o0],n,c.off+(s0-cb))!=(ssize_t)n) fail("read error in "+path); }
    if((long long)out.size()!=e-b) fail(path+": segment "+std::to_string(S.id)+" is shorter than the referenced range"); return out; }
  std::string all(const Seg& S) const { return read(S,0,S.bytes); } };

// ---------------- this run's own --pcert file: chunk index and reads ----------------
struct OwnSeg { std::vector<Chunk> ch; bool last=false; long long bytes=0; };
struct OwnIndex { std::mutex mu; std::unordered_map<unsigned long long,OwnSeg> seg; int fd=-1, fdw=-1;   // fdw: read-write fd for punch()
  long long punched=0;
  // free the disk blocks of a segment that only this run could read (helpers: no list job of this run is ever read from the file)
  void punch(unsigned long long id){ if(fdw<0) return; std::vector<Chunk> ch; { std::lock_guard<std::mutex> lk(mu); auto it=seg.find(id); if(it==seg.end()) return; ch=it->second.ch; }
    for(const Chunk& c:ch) if(c.len && fallocate(fdw,FALLOC_FL_PUNCH_HOLE|FALLOC_FL_KEEP_SIZE,c.off,c.len)==0){ std::lock_guard<std::mutex> lk(mu); punched+=c.len; } }
  void addChunk(unsigned long long id,uint32_t idx,long long off,uint32_t len,bool last){ std::lock_guard<std::mutex> lk(mu); OwnSeg& S=seg[id]; S.ch.push_back({idx,off,len}); S.bytes+=len; if(last) S.last=true; }
  bool complete(unsigned long long id){ std::lock_guard<std::mutex> lk(mu); auto it=seg.find(id); return it!=seg.end() && it->second.last; }
  std::string all(unsigned long long id){ OwnSeg S; { std::lock_guard<std::mutex> lk(mu); auto it=seg.find(id); if(it==seg.end()) fail("own segment "+std::to_string(id)+" unknown"); S=it->second; }
    if(!S.last) fail("own segment "+std::to_string(id)+" incomplete"); std::sort(S.ch.begin(),S.ch.end(),[](const Chunk& a,const Chunk& b){ return a.idx<b.idx; });
    std::string out; for(size_t i=0;i<S.ch.size();i++){ const Chunk& c=S.ch[i]; if(c.idx!=i) fail("own segment "+std::to_string(id)+" has a chunk gap"); size_t o0=out.size(); out.resize(o0+c.len);
      if(c.len && pread(fd,&out[o0],c.len,c.off)!=(ssize_t)c.len) fail("read error in own pcert file"); }
    return out; }
  void drop(unsigned long long id){ std::lock_guard<std::mutex> lk(mu); seg.erase(id); }
  void fromPFile(const PFileQ& F){ std::lock_guard<std::mutex> lk(mu); fd=F.fd; fdw=-1; seg.clear();   // the segments of an earlier launch's pcert (read-only)
    for(auto& kv:F.seg){ OwnSeg& S=seg[kv.first]; S.ch=kv.second.ch; S.bytes=kv.second.bytes; S.last=kv.second.last; } } };

// ---------------- assembler of an item's canonical own-part segment ----------------
struct Frame { int depth, label, last; };
struct Assembler {
  OwnIndex* own=nullptr; const std::unordered_map<std::string,unsigned long long>* pieces=nullptr;   // local pieces of this unit: prefix key (u16 labels) -> own segment id
  const std::vector<std::string>* srcPaths=nullptr;   // SKR / SKP source k -> earlier pcert file
  std::map<std::string,std::unique_ptr<PFileQ>> files; std::string out; long long nInl=0, nRef=0, nSkip=0, nRng=0;
  std::vector<int> base; std::vector<Frame> st; Frame pend{0,0,0}; bool havePend=false;
  static std::string key(const std::vector<int>& p){ std::string k; k.resize(2*p.size()); for(size_t i=0;i<p.size();i++){ uint16_t x=(uint16_t)p[i]; memcpy(&k[2*i],&x,2); } return k; }
  std::vector<int> prefixNow() const { std::vector<int> p=base; for(const Frame& f:st) if((int)p.size()<f.depth) p.push_back(f.label); return p; }
  PFileQ& file(const std::string& p){ auto it=files.find(p); if(it!=files.end()) return *it->second; auto f=std::make_unique<PFileQ>(); f->open_(p); PFileQ& r=*f; files[p]=std::move(f); return r; }
  void run(const std::string& bytes,int depth){
    Rd r(bytes); if(depth>64) fail("reference depth > 64");
    while(r.more()){ size_t a=r.i; uint8_t tag=r.p[r.i];
      if(tag==0x28){ r.u8(); if(st.empty()) fail("DON outside a node"); Frame& fr=st.back(); int c=fr.last+(int)r.var(); fr.last=c;
        std::vector<int> pk=prefixNow(); pk.push_back(c); auto it=pieces?pieces->find(key(pk)):pieces->end();
        if(pieces && it!=pieces->end()){ nInl++; run(own->all(it->second),depth+1); }
        else { nRef++; out.append(bytes,a,r.i-a); }   // a queue item: the reference stays (glued by prefix through the manifest)
        continue; }
      if(tag==0x29){ r.u8(); if(st.empty()) fail("SKR outside a node"); Frame& fr=st.back(); int lo=fr.last+(int)r.var(); int hi=lo+(int)r.var(); int k=(int)r.var(); unsigned long long sg=r.var(); long long b=(long long)r.var(), e=(long long)r.var(); (void)lo;
        if(!srcPaths || k<0 || k>=(int)srcPaths->size() || (*srcPaths)[k]=="-") fail("SKR: unknown source "+std::to_string(k)); PFileQ& G=file((*srcPaths)[k]); auto it=G.seg.find(sg); if(it==G.seg.end()) fail("SKR: no segment "+std::to_string(sg)+" in "+G.path);
        nSkip++; run(G.read(it->second,b,e),depth+1); st.back().last=hi; continue; }
      if(tag==0x2A){ r.u8(); int lab=(int)r.u16(); int k=(int)r.var(); unsigned long long sg=r.var();
        if(!srcPaths || k<0 || k>=(int)srcPaths->size() || (*srcPaths)[k]=="-") fail("SKP: unknown source "+std::to_string(k)); PFileQ& G=file((*srcPaths)[k]); auto it=G.seg.find(sg); if(it==G.seg.end()) fail("SKP: no segment "+std::to_string(sg)+" in "+G.path); if(!it->second.last) fail("SKP: segment incomplete");
        nSkip++; if(!st.empty()) st.back().last=lab; run(G.all(it->second),depth+1); continue; }
      if(tag==0x2C){ r.u8(); r.u16(); if(st.empty()) fail("RNG outside a node"); nRng++; out.append(bytes,a,r.i-a); st.pop_back(); continue; }   // the node's rest (and END) is the range item
      uint8_t t2; skipRec(r,t2); out.append(bytes,a,r.i-a);
      Rd q(bytes); q.i=a; q.u8();
      if(t2==0x01){ unsigned x=q.u16(); int d=(int)(x>>9), l=(int)(x&511); if(!st.empty() && st.back().depth>=d) fail("NODE inside an unclosed node"); if(!st.empty()){ if(st.back().depth!=d-1) fail("NODE depth jump"); st.back().last=l; } pend={d,l,l}; havePend=true; }
      else if(t2==0x04){ if(!havePend) fail("OPEN without NODE"); st.push_back(pend); havePend=false; }
      else if(t2==0x05){ if(st.empty()) fail("END without OPEN"); st.pop_back(); }
      else if(t2==0x02 || t2==0x03){ havePend=false; }
      else if((t2>=0x20 && t2<=0x27) || t2==0x2D){ if(st.empty()) fail("child record outside a node"); st.back().last+=(int)q.var(); } } }   // 0x2D JOB (top segments)
  // kind 0/1: the root segment starts with the root node's NODE record; kind 3 (range of node S): with S's child records, delta base p
  std::string unit(unsigned long long rootSeg,int kind,const std::vector<int>& prefix,int p){
    out.clear(); st.clear(); havePend=false; nInl=nRef=nSkip=nRng=0;
    if(kind==3){ base=prefix; base.pop_back(); st.push_back(Frame{(int)prefix.size(),prefix.back(),p}); }
    else { base=prefix; if(!base.empty()) base.pop_back(); }
    run(own->all(rootSeg),0);
    if(!st.empty()) fail("unclosed node at the end of the unit"); return out; } };
} // namespace xqr3
