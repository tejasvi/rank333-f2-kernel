    if(JOURNALF){ gJF=fopen(JOURNALF,"a"); if(!gJF){ fprintf(stderr,"cannot open journal %s\n",JOURNALF); return 2; } gJSF=SF;
      char hb[2048]; snprintf(hb,sizeof hb,"# prof7R3q journal fp=%016llx out=%s state=%s cert=%s pcert=%s jdepth=%d jmin=%lld pid=%d\n",gFP,outpath,STATEPATH?STATEPATH:"-",CERTPATH?CERTPATH:"-",PCPATH?PCPATH:"-",JDEPTH,JMIN,(int)getpid()); fputs(hb,gJF); fflush(gJF);
      fprintf(stderr,"L84: journal %s jdepth %d jmin %lld jsync %.0f fingerprint %016llx\n",JOURNALF,JDEPTH,JMIN,JSYNC,gFP); }
    { struct sigaction sa{}; sa.sa_handler=onTerm; sigemptyset(&sa.sa_mask); sigaction(SIGTERM,&sa,nullptr); }
    { struct sigaction sa{}; sa.sa_handler=onUsr1; sigemptyset(&sa.sa_mask); sigaction(SIGUSR1,&sa,nullptr); }   // prof7L92: SIGUSR1 = spill
    xqr3::gLeafx=PCLEAFX; xqr3::gCutx=(XPS!=nullptr); xqr3::gLeafv7=LEAFV7;   // prof7R3q: the record flags of this run's stream (header #leafx / #cutx / #leafv7)
    if(XQCAPD<0) XQCAPD=SPILLD; if(XQCAP>0 || XQCAPB>0) fprintf(stderr,"R3q: item-size cap: an imported unit is split when its own part reaches %lld nodes or %.0f MB of records (0 = no bound; at open nodes of depth <= %d)\n",XQCAP,XQCAPB/1e6,XQCAPD);
    if(XQRECIPE) fprintf(stderr,"R3q: recipe %s sha256 %s (part of the compat fingerprint)\n",XQRECIPE,gRecipeSha.c_str());
    if(PCF){ fflush(PCF); gPcFileOff=ftell(PCF); gOwn.fd=open(PCPATH,O_RDONLY); if(XQPUNCH<0) XQPUNCH=XQHELPER?1:0; if(XQPUNCH>0 && XQHELPER) gOwn.fdw=open(PCPATH,O_RDWR);   // a helper has no list job: its pcert is scratch if(gOwn.fd<0){ fprintf(stderr,"R3q: cannot reread %s\n",PCPATH); return 2; }   // prof7R3q: item assembly reads this run's stream back
      if(XQSEGP) gXqSegPath=XQSEGP; else gXqSegPath=std::string(PCPATH)+".xq";
      if(gXqSegPath[0]!='/'){ char cwd[4096]; if(getcwd(cwd,sizeof cwd)) gXqSegPath=std::string(cwd)+"/"+gXqSegPath; } }
    // prof7L92: work units = the list jobs (0..NF-1) and, with --xq, import slots (NF..NU-1)
    gNF=frontier.size(); const size_t NF=gNF;
    const size_t MS=XQADDR?(size_t)(XQSLOTS>0?XQSLOTS:4*THREADS+64):0; gNU=NF+MS; const size_t NU=gNU;
    gU.reset(new XUnit[NU>0?NU:1]); for(size_t u=0;u<NF;u++) gU[u].ix=(int)u;
    std::string xqName, xqPool="-", xqStateDir="-", xqOutPath="-", xqHost;
    { char hn[256]={0}; gethostname(hn,sizeof hn-1); xqHost=hn;
      std::string base="helper"; if(STATEPATH){ base=STATEPATH; auto sl=base.rfind('/'); if(sl!=std::string::npos){ xqStateDir=base.substr(0,sl); base=base.substr(sl+1); } else xqStateDir=".";
        if(base.compare(0,6,"state_")==0) base=base.substr(6); if(base.size()>4 && base.substr(base.size()-4)==".txt") base=base.substr(0,base.size()-4);
        auto us=base.find('_'); if(us!=std::string::npos) xqPool=base.substr(0,us); }
      if(XQPOOLO) xqPool=XQPOOLO;
      xqName=XQNAMEO?std::string(XQNAMEO):base; xqName+="@"+xqHost+":"+std::to_string((int)getpid())+":"+std::to_string((long long)time(nullptr)); }
    { unsigned long long hc=gOptFP; auto mx=[&](unsigned long long x){ hc^=x; hc*=1099511628211ULL; hc^=hc>>29; };   // compat (also for a spill file without --xq)
      mx(gTabHash); mx((unsigned long long)R); mx((unsigned long long)WL.size());
      if(XPS){ auto hb=[](const char* p,size_t n){ unsigned long long th=0x9E3779B97F4A7C15ULL^(unsigned long long)n; size_t i=0; for(;i+8<=n;i+=8){ unsigned long long x; memcpy(&x,p+i,8); th=(th^x)*0xBF58476D1CE4E5B9ULL; th^=th>>31; } for(;i<n;i++){ th=(th^(unsigned char)p[i])*0xBF58476D1CE4E5B9ULL; th^=th>>31; } return th; };   // prof7R3q
        mx(hb((const char*)XPLAB.data(),XPLAB.size())); for(int i=1;i+1<argc;i++) if(!strcmp(argv[i],"--pcxp") || !strcmp(argv[i],"--xpeel")){ FILE* cf=fopen(argv[i+1],"rb"); std::string cb; if(cf){ char tb[1<<16]; size_t k; while((k=fread(tb,1,sizeof tb,cf))>0) cb.append(tb,k); fclose(cf); } mx(hb(cb.data(),cb.size())); } } if(LPMIN>=0){ mx((unsigned long long)lpx::NR); mx((unsigned long long)lpx::RE.size()); }
      gCompat=hc; }
    if(XQADDR){
      if(XQOUTP) xqOutPath=XQOUTP; else { xqOutPath=outpath; if(xqOutPath.size()>5 && xqOutPath.substr(xqOutPath.size()-5)==".prof") xqOutPath=xqOutPath.substr(0,xqOutPath.size()-5); xqOutPath+="_xq.prof"; }
      XOUT=fopen(xqOutPath.c_str(),"a"); if(!XOUT){ fprintf(stderr,"cannot open --xqout %s\n",xqOutPath.c_str()); return 2; } gXOUTsync=XOUT;
      fprintf(stderr,"R3q: xq %s name %s pool %s compat %016llx (options %016llx, table %016llx) space %016llx slots %zu export %d import %d helper %d linger %.0f maxd %d keep %d xqout %s\n",
              XQADDR,xqName.c_str(),xqPool.c_str(),gCompat,gOptFP,gTabHash,gFP,MS,(int)XQEXPORT,(int)XQIMPORT,(int)XQHELPER,XQLINGER,XQMAXD,XQKEEP,xqOutPath.c_str()); }
    std::atomic<size_t> nextI{0}; std::mutex& rm=gRm; std::vector<double> sizes=prevSizes; double sumN=prevNodes; long long ndone=prevDone; double sumSec=0; std::atomic<bool> finF{false};
    auto t1=std::chrono::steady_clock::now();
    // prof7L29: per-unit bookkeeping for donated pieces (prof7L92: units, not only frontier jobs)
    std::unique_ptr<std::atomic<int>[]> outst(new std::atomic<int>[NU>0?NU:1]); for(size_t i=0;i<NU;i++) outst[i]=0; gOutst=outst.get();
    std::vector<char> rootDone(NU,0); std::vector<long long> jnodes(NU,0), jl0(NU,0), jp0(NU,0), jlv(NU,0), jpf(NU,0); std::atomic<long long> gReplayCut{0}; std::vector<std::chrono::steady_clock::time_point> jt0(NU);
    int activeR=0, activeP=0; bool fdone=false;
    // prof7L41: jobs finished elsewhere (--skipfile), re-read by whichever worker first sees the file is due
    std::unique_ptr<std::atomic<char>[]> skipIdx(new std::atomic<char>[NU>0?NU:1]); for(size_t i=0;i<NU;i++) skipIdx[i]=0;
    std::unique_ptr<std::atomic<char>[]> abortIdx(new std::atomic<char>[NU>0?NU:1]); for(size_t i=0;i<NU;i++) abortIdx[i]=0;   // prof7L92: units to abandon (prof7L48: the skip file with --abortdone)
    std::unique_ptr<std::atomic<char>[]> xother(new std::atomic<char>[NF>0?NF:1]); for(size_t i=0;i<NF;i++) xother[i]=0;   // prof7L92: jobs another run handed to the queue
    std::unique_ptr<std::atomic<char>[]> jab(new std::atomic<char>[NU>0?NU:1]); for(size_t i=0;i<NU;i++) jab[i]=0; gJab=jab.get(); std::atomic<long long> nAborted{0}; std::atomic<bool> drainNow{false};
    std::atomic<long long> skipLoad{0}, nSkipped{0}; std::mutex skipmu; auto tSkip=std::chrono::steady_clock::now()-std::chrono::hours(1);
    auto loadSkip=[&](){ if(!SKIPF) return; std::unique_lock<std::mutex> lk(skipmu,std::try_to_lock); if(!lk.owns_lock()) return;
      auto now=std::chrono::steady_clock::now(); if(std::chrono::duration<double>(now-tSkip).count()<SKIPEVERY) return; tSkip=now;
      if(DRAINF && !drainNow && access(DRAINF,F_OK)==0){ drainNow=true; fprintf(stderr,"drain file %s seen: no new list jobs\n",DRAINF); }
      FILE* f=fopen(SKIPF,"r"); if(!f) return; long long x, n=0; while(fscanf(f,"%lld",&x)==1){ if(x>=0 && (size_t)x<NF){ skipIdx[x]=1; if(ABORTDONE && !gU[x].exempt) abortIdx[x]=1; n++; } } fclose(f); skipLoad=n; };
    loadSkip(); if((ABORTDONE && SKIPF) || XQADDR) gSkipP=abortIdx.get();
    // prof7L92: queue client state.  Lines waiting for an answer are re-sent after a reconnect (the server dedups by run name + cseq).
    std::mutex xmu; std::map<long long,std::pair<int,Job>> xpend;   // export cseq -> (unit, piece)
    std::map<long long,std::string> xspl; std::map<long long,std::string> xsplRes;   // spill messages waiting for SPA/SPN; answers
    std::unordered_map<long long,int> itemSlot, jitem2ix; std::vector<int> freeSlots; for(size_t u=NU;u-->NF;) freeSlots.push_back((int)u);
    std::atomic<int> xfree{(int)MS}, xpendN{0}, xgive{0}; std::atomic<bool> xconn{false}, xrelease{false}, xstop{false}, xready{false};
    std::atomic<long long> xcseq{0}, xlastWork{0}; std::atomic<long long> nXrep{0}, nXrepAck{0};
    auto nowS=[](){ return (long long)std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now().time_since_epoch()).count(); };
    xlastWork=nowS();
    auto xsend=[&](const std::string& line){ std::lock_guard<std::mutex> lk(gXmu); gXout.push_back(line+"\n"); };
    auto vecs=[&](const std::vector<int>& seq){ std::string t=std::to_string(seq.size()); for(int l:seq){ t+=' '; t+=std::to_string(vecOf[l]); } return t; };
    auto parentRef=[&](int u){ if((size_t)u<NF) return std::string("j ")+std::to_string(u)+" "+vecs(frontier[u]); return std::string("i ")+std::to_string(gU[u].item); };
    auto dropOwn=[&](XUnit& U){ if(U.rootSeg) gOwn.drop(U.rootSeg); for(auto& kv:U.pcs) gOwn.drop(kv.second); U.rootSeg=0; U.pcs.clear(); };   // prof7R3q: segments no item assembly needs
    auto freeSlot=[&](int u){   // caller holds rm
      XUnit& U=gU[u]; if(U.item) itemSlot.erase(U.item); dropOwn(U); U.kind=0; U.item=0; U.ix=-1; U.seq.clear(); U.rs=-1; U.rp=-1; U.din={}; U.win.clear(); U.active=false; U.pexp=U.nexp=0; U.intr=0; U.skmask=0; U.sk.clear(); U.skHit=0; U.regen=false; U.rstop.clear(); U.rsmask=0; U.rsHit=0; U.rcut=false; U.rgive=false; U.live=0; U.bytes=0; U.split=false; U.srecs.clear(); U.spieces.clear();
      rootDone[u]=0; outst[u]=0; jnodes[u]=jlv[u]=jpf[u]=0; jab[u]=0; abortIdx[u]=0; freeSlots.push_back(u); xfree++; };
    // prof7R3q: a finished unit's canonical own-part segment is assembled off the results lock (finalizer thread), written to --xqseg with
    // its sha256, and only then reported; the committer syncs the profiles, the stream and the item segments before the report goes out.
    struct FinJob { int u; long long item; int jix, job, skh, rsh; int kind; std::vector<int> pre; int rs, rp; std::array<uint64_t,8> din; unsigned long long root; std::unordered_map<std::string,unsigned long long> pcs; long long n,l,p; int nexp; std::vector<int32_t> win; bool split=false; std::string spRef, spKids; };   // win: the root's witness rows (--pcwit); split: an --xqcap split (reported by one SP: parent ref, child items)
    std::mutex finmu; std::condition_variable fincv; std::deque<FinJob> finq; std::atomic<int> finBusy{0}; std::atomic<bool> finStop{false};
    std::mutex heldmu; std::unordered_set<long long> xheld;   // items reported or being reported here, until the queue answers (HOLD after a reconnect)
    auto segWriteFrom=[&](xqr3::OwnIndex& own,bool mine,const std::string& dkey,int kind,long long item,int jix,const std::vector<int>& pre,int rs,int rp,const std::array<uint64_t,8>& din,const std::vector<int32_t>& win,unsigned long long root,const std::unordered_map<std::string,unsigned long long>& pcs,std::string& err)->std::string{
      std::string recs;   // OWN: this run's pcert index (mine), or an earlier launch's pcert on this host (recovery of a fast spill)
      try{ xqr3::Assembler A; A.own=&own; A.pieces=&pcs; A.srcPaths=&gJpc; recs=A.unit(root,kind,pre,rp); }
      catch(const std::exception& e){ err=e.what(); return std::string(); }
      uint8_t raw[32]; const std::string hex=xqr3::sha256hex(recs,raw);
      std::string hdr; pcVar(hdr,(unsigned long long)std::max(0LL,item)); pcVar(hdr,(unsigned long long)std::max(0,jix)); pcU8(hdr,(unsigned)kind); pcU8(hdr,(unsigned)pre.size()); for(int l:pre) pcU16(hdr,(unsigned)l);
      uint64_t lm[8]={0}; for(int v=1;v<512;v++) if((din[v>>6]>>(v&63))&1){ int l=labOf[v]; if(l>=0) lm[l>>6]|=1ULL<<(l&63); } hdr.append((const char*)lm,64);
      if(PCWIT) winBytes(hdr,(kind==1 || kind==3)?win:std::vector<int32_t>());   // batch 12 (--pcwit): the witness rows of the mask, as in the pcert header
      pcU16(hdr,(unsigned)(kind==3?rs:0)); pcU16(hdr,(unsigned)(kind==3?rp:0));
      std::lock_guard<std::mutex> lk(gXqSegMu);
      if(!gXqSeg){ gXqSeg=fopen(gXqSegPath.c_str(),"a"); if(!gXqSeg){ err="cannot open "+gXqSegPath; return std::string(); }
        if(ftell(gXqSeg)==0){ fprintf(gXqSeg,"#R3XQ 1 fp=%016llx compat=%016llx run=%s pcert=%s\n#lab %d",gFP,gCompat,xqName.c_str(),PCPATH,N); for(int l=0;l<N;l++) fprintf(gXqSeg," %d",vecOf[l]);
          fprintf(gXqSeg,"\n#table %s\n#kept %s\n#typecut %d\n",tabpath,LPKEPT,TYPECUT); if(PCLEAFX) fprintf(gXqSeg,"#leafx 1\n"); if(XPS) fprintf(gXqSeg,"#cutx 1\n"); if(XPVAR) fprintf(gXqSeg,"#xpvar 1\n"); if(LEAFV7) fprintf(gXqSeg,"#leafv7 1\n"); if(PCWIT) fprintf(gXqSeg,"#pcwit 1\n"); fprintf(gXqSeg,"#end\n"); fflush(gXqSeg); }
        gXqSegOff=ftell(gXqSeg); }
      // run 1 (2026-10-07): on a full disk unchecked fwrites failed and the counted offset ran ahead of the file, so every later reference named
      // other bytes. Now the block goes in one checked write at the file's true end (O_APPEND: its size under gXqSegMu); a failed or short write
      // is cut off again, the pcert stays unpunched and the item goes without a segment (ERR / SGL: the queue re-runs it elsewhere). A full disk
      // (ENOSPC, EDQUOT) is waited out first, up to 15 min (the checks free space; checkd pauses the helper).
      const uint32_t h2[2]={0x49583352u,(uint32_t)hdr.size()}; const uint64_t n=recs.size();
      std::string blk; blk.reserve(8+hdr.size()+8+recs.size()+32); blk.append((const char*)h2,8); blk.append(hdr); blk.append((const char*)&n,8); blk.append(recs); blk.append((const char*)raw,32);
      const long long len=(long long)blk.size(); long long off=-1; const int sfd=fileno(gXqSeg);
      for(int tr=0;;tr++){
        if(fflush(gXqSeg)!=0) clearerr(gXqSeg);
        struct stat sst; if(fstat(sfd,&sst)!=0){ gXqSegWErr++; err=std::string("segment file fstat: ")+strerror(errno); return std::string(); }
        off=(long long)sst.st_size; size_t done=0; int we=0;
        while(done<blk.size()){ const ssize_t w=::write(sfd,blk.data()+done,blk.size()-done); if(w<0){ if(errno==EINTR) continue; we=errno; break; } if(w==0){ we=EIO; break; } done+=(size_t)w; }
        if(done==blk.size()) break;
        if(ftruncate(sfd,(off_t)off)!=0) fprintf(stderr,"R3q: segment of item %lld: the partial block at %lld could not be cut off: %s\n",item,off,strerror(errno));
        if((we==ENOSPC || we==EDQUOT) && tr<90){ if(tr==0) fprintf(stderr,"R3q: segment of item %lld: %s; waiting for space (up to 15 min)\n",item,strerror(we)); std::this_thread::sleep_for(std::chrono::seconds(10)); continue; }
        gXqSegWErr++; err=std::string("segment write failed: ")+strerror(we); return std::string(); }
      if(gXqSegOff>0 && off!=gXqSegOff) fprintf(stderr,"R3q: segment file end %lld, counted %lld: the end is used\n",off,gXqSegOff);
      gXqSegOff=off+len; gXqSegN++; gXqSegB+=len;
      const std::string ref=gXqSegPath+":"+std::to_string(off)+":"+std::to_string(len)+":"+hex;
      auto unwrite=[&](const char* what){ const int e=errno; gXqSegWErr++; err=std::string(what)+": "+strerror(e); if(ftruncate(sfd,(off_t)off)==0) gXqSegOff=off; return std::string(); };   // not durable: not reported
      if(mine && !dkey.empty()){ if(fdatasync(sfd)!=0) return unwrite("segment fdatasync"); FILE* pf=fopen((std::string(PCPATH)+".pend").c_str(),"a"); if(pf){ fprintf(pf,"D %s seg=%s\n",dkey.c_str(),ref.c_str()); fflush(pf); fsync(fileno(pf)); fclose(pf); } }   // a pending report's segment: <pcert>.pend names it (durably) before its raw blocks go
      if(mine){ if(own.fdw>=0){ if(fdatasync(sfd)!=0) return unwrite("segment fdatasync"); own.punch(root); for(auto& kv:pcs) own.punch(kv.second); }   // a helper's pcert is scratch: punched once the segment is on disk
        own.drop(root); for(auto& kv:pcs) own.drop(kv.second); }
      return ref; };
    auto segWrite=[&](int kind,long long item,int jix,const std::vector<int>& pre,int rs,int rp,const std::array<uint64_t,8>& din,const std::vector<int32_t>& win,unsigned long long root,const std::unordered_map<std::string,unsigned long long>& pcs,std::string& err)->std::string{
      return segWriteFrom(gOwn,true,std::string(),kind,item,jix,pre,rs,rp,din,win,root,pcs,err); };
    auto segWritePend=[&](const std::string& dkey,const FinJob& f,std::string& err)->std::string{ return segWriteFrom(gOwn,true,dkey,f.kind,f.item,f.job,f.pre,f.rs,f.rp,f.din,f.win,f.root,f.pcs,err); };   // the segment of a pending report (key dkey)
    // prof7R3q fast spill: a spill (SIGTERM: a preemption leaves ~30 s) reports the units finished but not yet assembled and the spilled units at once,
    // with seg=pending; their segments follow as "SG RUN:C seg=REF" (C = the report's number). <pcert>.pend lists them (assembly data), so that a
    // later launch on this host (--xqrecover DIR) assembles from this pcert whatever this one could not.
    FinJob finCur; bool finCurOn=false;   // the job the finalizer is assembling (under finmu)
    std::mutex pendmu; std::unordered_map<long long,std::string> pendRep;   // item -> key of its pending report: the finalizer sends SG instead of R
    std::map<std::string,std::string> sgPend;   // key -> SG line until the queue answers (resent after a reconnect)
    std::map<std::string,int> sgRetry;   // keys whose SG / SGL the queue refused with "noreport" (the report not there yet): sent again, up to 40 times
    auto sgSend=[&](const std::string& key,const std::string& line){ const auto c=key.rfind(':'); const std::string rp="R "+key.substr(c+1)+" ", sp="SP "+key.substr(c+1)+" "; bool later=false;
      { std::lock_guard<std::mutex> lk(gJmu); for(auto& x:gRpend) if(x.compare(0,rp.size(),rp)==0 || x.compare(0,sp.size(),sp)==0){ later=true; break; } if(later) gRpend.push_back(line); }   // after its report, in the same commit
      if(!later) xsend(line); };
    auto sgLost=[](const std::string& key,const std::string& why){ std::string w=why.substr(0,120); for(char& ch:w) if(ch==' '||ch=='\n'||ch=='\t') ch='_'; return "SGL "+key+" "+(w.empty()?std::string("-"):w); };   // SGL: this host cannot produce the segment of a pending report
    auto pendLine=[&](const std::string& key,int kind,long long item,int job,const std::vector<int>& pre,int rs,int rp,const std::array<uint64_t,8>& din,const std::vector<int32_t>& win,unsigned long long root,const std::unordered_map<std::string,unsigned long long>& pcs)->std::string{
      std::string t="P "+key+" "+std::to_string(kind)+" "+std::to_string(item)+" "+std::to_string(job)+" "+std::to_string(pre.size()); for(int l:pre) t+=" "+std::to_string(l);
      t+=" "+std::to_string(rs)+" "+std::to_string(rp)+" "+dhex(din)+" "+(PCWIT?whex(win):std::string("-"))+" "+std::to_string(root)+" "+std::to_string(pcs.size());   // pend 2: the witness after the mask
      static const char* HX="0123456789abcdef"; for(auto& kv:pcs){ t+=' '; for(unsigned char ch:kv.first){ t+=HX[ch>>4]; t+=HX[ch&15]; } t+=":"+std::to_string(kv.second); }
      return t+"\n"; };
    // --xqrecover DIR: the <pcert>.pend files of earlier launches on this host: segments not yet sent are assembled from that launch's pcert;
    // sent ones (D lines) are sent again; a file whose segments the queue has all answered becomes .pend.done and its pcert is deleted
    std::vector<std::pair<std::string,std::pair<std::string,std::vector<std::string>>>> recFiles;   // .pend path -> (old pcert, keys)
    if(XQRECOVER && PCF){ DIR* dd=opendir(XQRECOVER); struct dirent* de; std::vector<std::string> pf;
      while(dd && (de=readdir(dd))){ std::string nm=de->d_name; if(nm.size()>5 && nm.compare(nm.size()-5,5,".pend")==0) pf.push_back(std::string(XQRECOVER)+"/"+nm); } if(dd) closedir(dd);
      for(auto& path:pf){ if(path==std::string(PCPATH)+".pend") continue; std::ifstream in(path); std::string ln, opc; std::vector<std::string> keys, Ps; std::map<std::string,std::string> Ds;
        int pver=1;
        while(std::getline(in,ln)){ if(ln.rfind("# R3Q pend",0)==0){ auto q=ln.find("pcert="); if(q!=std::string::npos) opc=ln.substr(q+6,ln.find(' ',q)-q-6); pver=atoi(ln.c_str()+11); continue; }
          std::istringstream is(ln); std::string t,k; is>>t>>k; if(t=="P"){ Ps.push_back(ln); keys.push_back(k); } else if(t=="D"){ std::string r; is>>r; if(r.rfind("seg=",0)==0) Ds[k]=r.substr(4); } }
        int nre=0, nas=0, nbad=0; xqr3::PFileQ G; xqr3::OwnIndex V; bool gok=false; std::string gerr;
        for(auto& P:Ps){ std::istringstream is(P); std::string t,key; int kind,d; long long item; int job; is>>t>>key>>kind>>item>>job>>d; std::vector<int> pre(d); for(int i=0;i<d;i++) is>>pre[i];
          int rs, rp; std::string dh, wh; unsigned long long root; size_t np; is>>rs>>rp>>dh; if(pver>=2) is>>wh; is>>root>>np; std::array<uint64_t,8> din{}; undhex(dh,din); std::vector<int32_t> win; if(!wh.empty() && wh!="-") unwhex(wh,win); std::unordered_map<std::string,unsigned long long> pcs;
          for(size_t i=0;i<np;i++){ std::string e; is>>e; auto c2=e.find(':'); std::string hk=e.substr(0,c2), k2; for(size_t q=0;q+1<hk.size();q+=2) k2+=(char)std::stoi(hk.substr(q,2),nullptr,16); pcs[k2]=std::stoull(e.substr(c2+1)); }
          auto di=Ds.find(key); if(di!=Ds.end()){ std::lock_guard<std::mutex> lk(pendmu); sgPend[key]="SG "+key+" seg="+di->second; nre++; continue; }
          if(!gok){ try{ G.open_(opc); V.fromPFile(G); gok=true; } catch(const std::exception& e){ fprintf(stderr,"R3q: recover %s: cannot read %s: %s\n",path.c_str(),opc.c_str(),e.what()); gerr=e.what(); gok=true; } }
          if(!gerr.empty()){ nbad++; std::lock_guard<std::mutex> lk(pendmu); sgPend[key]=sgLost(key,"pcert_unreadable:"+gerr); continue; }   // every segment of an unreadable pcert is lost
          std::string err; const std::string ref=segWriteFrom(V,false,std::string(),kind,item,job,pre,rs,rp,din,win,root,pcs,err);
          if(ref.empty()){ nbad++; fprintf(stderr,"R3q: recover %s: segment %s not assembled: %s (declared lost: the queue re-runs the item)\n",path.c_str(),key.c_str(),err.c_str()); std::lock_guard<std::mutex> lk(pendmu); sgPend[key]=sgLost(key,err); continue; }
          xqSegSync(); { FILE* f=fopen(path.c_str(),"a"); if(f){ fprintf(f,"D %s seg=%s\n",key.c_str(),ref.c_str()); fclose(f); } }
          { std::lock_guard<std::mutex> lk(pendmu); sgPend[key]="SG "+key+" seg="+ref; } nas++; }
        fprintf(stderr,"R3q: recover %s (pcert %s, %lld punched or damaged blocks skipped): %d segments assembled, %d sent again, %d declared lost\n",path.c_str(),opc.c_str(),G.nskip,nas,nre,nbad);
        recFiles.push_back({path,{opc,keys}}); } }
    auto recCheck=[&](){ for(auto it=recFiles.begin();it!=recFiles.end();){ bool open_=false; { std::lock_guard<std::mutex> lk(pendmu); for(auto& k:it->second.second) if(sgPend.count(k)){ open_=true; break; } }
        if(open_){ ++it; continue; } rename(it->first.c_str(),(it->first+".done").c_str()); if(!it->second.first.empty()) unlink(it->second.first.c_str());
        fprintf(stderr,"R3q: recovered %s: every segment answered; its pcert deleted\n",it->first.c_str()); it=recFiles.erase(it); } };
    auto xqReport=[&](int u,long long item,int jix){   // caller holds rm: the unit's own part is done; the finalizer assembles its segment and reports it
      XUnit& U=gU[u]; FinJob f; f.u=u; f.item=item; f.jix=jix; f.job=(size_t)u<NF?u:U.ix; f.skh=U.skHit.load(); f.rsh=U.rsHit.load(); f.n=jnodes[u]; f.l=jlv[u]; f.p=jpf[u]; f.nexp=U.nexp; f.root=U.rootSeg; f.pcs.swap(U.pcs); U.rootSeg=0;
      if((size_t)u<NF){ f.kind=0; f.pre=frontier[u]; f.rs=-1; f.rp=-1; f.din={}; }
      else { f.kind=U.rcut?2:(U.kind=='P'?1:(U.kind=='J'?0:3)); f.pre=U.seq; f.rs=U.rs; f.rp=U.rp; f.din=U.din; f.win=U.win; }
      { std::lock_guard<std::mutex> lk(heldmu); if(item>0) xheld.insert(item); }
      { std::lock_guard<std::mutex> lk(finmu); finq.push_back(std::move(f)); } fincv.notify_one(); nXrep++; };
    // --xqcap: a split unit's own part is done (caller holds rm): the finalizer writes its segment, then one SP message reports the own
    // counts with the segment and the unit's range records (Q items) and queued pieces (P items), as a spill does for one unit
    std::atomic<long long> nXsplitDone{0}, nXsplitAck{0};
    auto splitDone=[&](int u){ XUnit& U=gU[u]; FinJob f; f.u=u; f.item=U.item; f.jix=-1; f.job=U.ix; f.skh=U.skHit.load(); f.rsh=0; f.n=jnodes[u]; f.l=jlv[u]; f.p=jpf[u]; f.nexp=U.nexp;
      f.root=U.rootSeg; f.pcs.swap(U.pcs); U.rootSeg=0; f.kind=U.kind=='P'?1:(U.kind=='J'?0:3); f.pre=U.seq; f.rs=U.rs; f.rp=U.rp; f.din=U.din; f.win=U.win; f.split=true; f.spRef=parentRef(u);
      for(auto& r:U.srecs){ f.spKids+=" | Q "+vecs(r.seq)+" "+std::to_string(vecOf[r.l]); if(PCF) f.spKids+=" p="+std::to_string(vecOf[r.p])+" dinh="+dhex(r.D); if(PCF && PCWIT) f.spKids+=" win="+whex(r.win); }
      for(auto& j:U.spieces){ f.spKids+=" | P "+vecs(j.seq); if(PCF) f.spKids+=" dinh="+dhex(j.dinh); if(PCF && PCWIT) f.spKids+=" win="+whex(j.win); }
      U.srecs.clear(); U.spieces.clear();
      { std::lock_guard<std::mutex> lk(heldmu); if(f.item>0) xheld.insert(f.item); }
      { std::lock_guard<std::mutex> lk(finmu); finq.push_back(std::move(f)); } fincv.notify_one(); nXrep++; nXsplitDone++; };
    const int finDelayMs=getenv("R3Q_TEST_FIN_DELAY_MS")?atoi(getenv("R3Q_TEST_FIN_DELAY_MS")):0;   // tests only: a slow finalizer (finished units wait in its queue, so a spill reports them pending)
    std::thread finth([&](){ while(true){ FinJob f; { std::unique_lock<std::mutex> lk(finmu); fincv.wait(lk,[&]{ return !finq.empty() || finStop.load(); }); if(finq.empty() && finStop.load()) break; f=std::move(finq.front()); finq.pop_front(); finBusy++; finCur=f; finCurOn=true; }
        if(finDelayMs>0) std::this_thread::sleep_for(std::chrono::milliseconds(finDelayMs));
        std::string pk0; { std::lock_guard<std::mutex> lk(pendmu); auto it=pendRep.find(f.item); if(it!=pendRep.end()) pk0=it->second; }   // reported pending by a spill already: <pcert>.pend gets the D line before the punch
        std::string err, ref; if(PCF){ ref=pk0.empty()?segWrite(f.kind,f.item,f.job,f.pre,f.rs,f.rp,f.din,f.win,f.root,f.pcs,err):segWritePend(pk0,f,err); if(ref.empty()){ gXqAsmErr++; fprintf(stderr,"R3q: segment of item %lld (unit %d) not assembled: %s\n",f.item,f.u,err.c_str()); ref="ERR"; } }
        std::string pk; { std::lock_guard<std::mutex> lk(pendmu); auto it=pendRep.find(f.item); if(it!=pendRep.end()){ pk=it->second; pendRep.erase(it); } }
        if(!pk.empty() && pk0.empty() && ref!="ERR"){ FILE* pf=fopen((std::string(PCPATH)+".pend").c_str(),"a"); if(pf){ fprintf(pf,"D %s seg=%s\n",pk.c_str(),ref.c_str()); fflush(pf); fsync(fileno(pf)); fclose(pf); } }   // registered during the assembly
        if(!pk.empty()){ std::string sl; if(ref!="ERR"){ xqSegSync(); sl="SG "+pk+" seg="+ref; } else sl=sgLost(pk,err); { std::lock_guard<std::mutex> lk(pendmu); sgPend[pk]=sl; } sgSend(pk,sl); }   // reported at a spill: its segment (or SGL: the queue re-runs the item)
        else if(f.split){ long long c=++xcseq; std::string line="SP "+std::to_string(c)+" "+f.spRef+" "+std::to_string(f.n)+" "+std::to_string(f.l)+" "+std::to_string(f.p)+" "+std::to_string(f.nexp);   // --xqcap
          if(PCF) line+=" seg="+ref; line+=" skh="+std::to_string(f.skh)+f.spKids; { std::lock_guard<std::mutex> lk(gJmu); gRpend.push_back(line); } }
        else { long long c=++xcseq; char b[256]; snprintf(b,sizeof b,"R %lld %lld %lld %lld %lld %d",c,f.item,f.n,f.l,f.p,f.nexp); std::string line=b; if(PCF) line+=" seg="+ref; line+=" skh="+std::to_string(f.skh)+" rsh="+std::to_string(f.rsh);
          { std::lock_guard<std::mutex> lk(gXmu); gXrepIx[c]=f.jix; } { std::lock_guard<std::mutex> lk(gJmu); gRpend.push_back(line); } }
        { std::lock_guard<std::mutex> lk(finmu); finCurOn=false; } finBusy--; } });
    auto finDrain=[&](){ for(int w=0;w<36000;w++){ bool idle; { std::lock_guard<std::mutex> lk(finmu); idle=finq.empty() && finBusy.load()==0; } if(idle) return; std::this_thread::sleep_for(std::chrono::milliseconds(10)); } };
    auto writeState=[&](int ix){   // caller holds rm
      if(jab[ix].load()){ nAborted++; if(VERB) fprintf(stderr,"abandoned %d (done elsewhere)\n",ix); return; }   // prof7L48: no state line
      long long nn=jnodes[ix]; double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-jt0[ix]).count();
      sizes.push_back(nn); sumN+=nn; ndone++; sumSec+=sec;
      if(SF){ char sb[160]; snprintf(sb,sizeof sb,"%d %lld %lld %lld %.2f\n",ix,nn,jlv[ix],jpf[ix],sec); if(gJSF){ std::lock_guard<std::mutex> lk(gJmu); gSpend.push_back(sb); } else { fputs(sb,SF); fflush(SF); } }   // prof7L84: committed after the profiles
      if(VERB) fprintf(stderr,"end %d nodes %lld sec %.1f\n",ix,nn,sec); };
    std::atomic<long long> nXtrackedDone{0}, nXimpDone{0};
    auto unitDone=[&](int u){   // prof7L92 (caller holds rm): the root and every local piece of unit u are done
      XUnit& U=gU[u];
      if(U.split.load()){ if(gSpill.load()) return; if(!jab[u].load()) splitDone(u); freeSlot(u); return; }   // prof7R3q --xqcap: one SP for the split unit (under a spill, the spill writes it out)
      if(U.intr.load()) return;   // interrupted by a spill: the spill writes it out
      if((size_t)u<NF){
        if(!U.tracked){ writeState(u); dropOwn(U); return; }   // prof7L87's state line (prof7R3q: its stream is R3's job stream, r3cat assembles it)
        if(jab[u].load()){ xsend("UL "+std::to_string(U.item)); nAborted++; dropOwn(U); return; }   // abandoned after an accepted export: the server re-queues the job root
        xqReport(u,U.item,u); nXtrackedDone++; ndone++; return; }
      if(!jab[u].load()){ xqReport(u,U.item,-1); nXimpDone++; }
      freeSlot(u); };
    auto checkFin=[&](){   // caller holds qmu
      if(nextI.load()>=order.size() && Q.empty() && activeR==0 && activeP==0 && !fdone && xpendN.load()==0 && (!XQADDR || xrelease.load() || (!XQHELPER && XQLINGER<=0))){ fdone=true; qcv.notify_all(); } };
    auto worker=[&](int tid){ Search s; s.tid=tid; s.doneP=&doneT[tid*8];
      auto runPiece=[&](Job& job){ int ix=job.ix; s.curJob=ix; const bool imp=(size_t)ix>=NF;
        tlXU=nullptr;
        if(imp && !job.root && (XQCAP>0 || XQCAPB>0) && gU[ix].split.load()){ { std::lock_guard<std::mutex> lk(rm); gU[ix].spieces.push_back(std::move(job)); --outst[ix]; if(outst[ix]==0 && rootDone[ix]) unitDone(ix); }   // prof7R3q --xqcap
          { std::lock_guard<std::mutex> lq(qmu); activeP--; checkFin(); } return; }
        if(imp) tlXU=&gU[ix];   // --xqcapb
        long long v0=s.visited, lv0=s.myLeaf, pf0=s.myProf; s.jstart=std::chrono::steady_clock::now();
        s.xu=imp?&gU[ix]:nullptr;   // prof7L92: an imported item skips the children exported from it before
        if(job.root){ std::lock_guard<std::mutex> lk(rm); jt0[ix]=s.jstart; }
        if(!s.replay(job.seq)){ if(!imp){ fprintf(stderr,"replay failed (piece)\n"); exit(5); }
          if(job.root && gU[ix].kind=='J' && s.replayWhy==2){   // prof7R3q: R3's replay-cut segment (CUT 11), reported with no nodes
            if(PCF){ pcOpen(gU[ix].ix,2,job.seq,nullptr); std::string& B=tlPc.buf; pcU8(B,0x03); pcU8(B,11); pcU8(B,(unsigned)(s.rp.size()-1)); pcU8(B,(unsigned)s.addWhy);
              if(s.addWhy==1 || s.addWhy==2){ pcU8(B,(unsigned)s.addDim); for(int j=0;j<s.addDim;j++) pcU16(B,s.addRows[j]); } else pcU8(B,(unsigned)s.addW);
              const unsigned long long sid=tlPc.id; pcChunk(true); std::lock_guard<std::mutex> lk(rm); gU[ix].rootSeg=sid; }
            { std::lock_guard<std::mutex> lk(rm); gU[ix].rcut=true; }
            s.unreplay(job.seq); s.xu=nullptr; gReplayCut++;
            { std::lock_guard<std::mutex> lk(rm); rootDone[ix]=1; if(outst[ix]==0) unitDone(ix); }
            { std::lock_guard<std::mutex> lq(qmu); activeP--; checkFin(); } return; }
          s.unreplay(job.seq); s.xu=nullptr; fprintf(stderr,"R3q: imported item %lld does not replay here (why %d): reported as an error\n",gU[ix].item,s.replayWhy);
          xsend("E "+std::to_string(gU[ix].item)+" replay"+std::to_string(s.replayWhy)); abortIdx[ix]=1; jab[ix]=1;
          { std::lock_guard<std::mutex> lk(rm); if(job.root) rootDone[ix]=1; else --outst[ix]; if(outst[ix]==0 && rootDone[ix]) unitDone(ix); }
          { std::lock_guard<std::mutex> lq(qmu); activeP--; checkFin(); } return; }
        const long long pv0=s.visited, pl0=s.myLeaf, pp0=s.myProf, pd0=s.donN, pi0=s.nIntr;   // prof7L84
        if(PCF){ const int jx=imp?gU[ix].ix:ix;   // prof7R3q: the segment of an imported root (kind 1 piece, 0 job root, 3 range) or of a local piece (kind 1, R3)
          if(job.root){ const int kd=gU[ix].kind=='P'?1:(gU[ix].kind=='J'?0:3); if(kd==3) s.pcBeginQ(jx,3,job.seq,job.dinh,gU[ix].rs,gU[ix].rp,&job.win); else s.pcBegin(jx,kd,job.seq,job.dinh,&job.win); }
          else s.pcBegin(jx,1,job.seq,job.dinh,&job.win);   // batch 12: the piece's witness rows
          { std::lock_guard<std::mutex> lk(rm); if(job.root) gU[ix].rootSeg=tlPc.id; else gU[ix].pcs[pkey(job.seq)]=tlPc.id; } }
        s.resetLists(); s.jobBase=*s.doneP;
        if(job.rs>=0){ const int d0=(int)job.seq.size(); s.rngD=d0; s.rngL=job.rs; s.rngP=gU[ix].rp; s.rngSeen=0; s.dfs2(job.seq.back(),R-d0,job.w,d0); s.rngD=-1; s.rngP=-1; }   // prof7L92: a range item (the node itself is not counted)
        else s.dfs(job.seq.back(),R-(int)job.seq.size(),job.w);
        s.unreplay(job.seq); certFlush(); if(PCF) pcChunk(true); s.xu=nullptr;
        if(!imp && gJF && s.donN==pd0 && s.nIntr==pi0 && !jab[ix].load() && nprof<MAXPROF && s.visited-pv0>=JMIN){   // prof7L84: a finished piece (prof7L92: not one a spill interrupted)
          char b[96]; std::string t; snprintf(b,sizeof b,"P %d %lld %lld %lld %zu",ix,s.visited-pv0,s.myLeaf-pl0,s.myProf-pp0,job.seq.size()); t+=b;
          for(int l2:job.seq){ snprintf(b,sizeof b," %d",vecOf[l2]); t+=b; } if(PCF){ snprintf(b,sizeof b," %llu",tlPc.id); t+=b; } t+='\n'; std::lock_guard<std::mutex> lk(gJmu); gJpend.push_back(std::move(t)); }   // prof7R3: segment of the piece
        { std::lock_guard<std::mutex> lk(rm); long long dn=s.visited-v0; if(job.root && gU[ix].kind=='J') dn-=1;   // a job root does not count its frontier node (as a list job)
          jnodes[ix]+=dn; jlv[ix]+=s.myLeaf-lv0; jpf[ix]+=s.myProf-pf0; if(job.root) rootDone[ix]=1; else --outst[ix];
          if(!s.sp.empty() && !gSpill.load()){ for(auto& r:s.sp) gU[r.u].srecs.push_back(std::move(r)); s.sp.clear(); }   // prof7R3q --xqcap: a split's range records (a spill collects them at the end instead)
          tlXU=nullptr;
          if(outst[ix]==0 && rootDone[ix]) unitDone(ix); }
        { std::lock_guard<std::mutex> lq(qmu); activeP--; checkFin(); } };
      while(true){
        if(gSpill.load(std::memory_order_relaxed)) break;   // prof7L92: spill (queued work is written out by the main thread)
        if(AGEDON>0 && qsizeA.load(std::memory_order_relaxed)>0){ Job pj; bool got=false;   // prof7L48: queued pieces before new list jobs
          { std::lock_guard<std::mutex> lq(qmu); if(!Q.empty()){ pj=std::move(Q.front()); Q.pop_front(); qsizeA--; activeP++; got=true; } }
          if(got){ runPiece(pj); continue; } }
        size_t k=drainNow.load(std::memory_order_relaxed)?order.size():nextI++;
        if(k>=order.size() && drainNow.load(std::memory_order_relaxed)){ size_t cur=nextI.load(); while(cur<order.size() && !nextI.compare_exchange_weak(cur,order.size())){} }
        if(k<order.size()){ int ix=order[k]; if(doneIdx[ix]) continue;
          if(SKIPF){ loadSkip(); if(skipIdx[ix]){ nSkipped++; continue; } }
          if(XQADDR && (xother[ix].load() || gHanded.count(ix))){ gXskipT++; continue; }   // prof7L92: handed to the queue (by another run, or by an earlier copy here)
          { std::lock_guard<std::mutex> lq(qmu); activeR++; }
          long long v0=s.visited; s.jstart=std::chrono::steady_clock::now(); { std::lock_guard<std::mutex> lk(rm); jt0[ix]=std::chrono::steady_clock::now(); jl0[ix]=nleaf; jp0[ix]=nprof; }
          const auto& job=frontier[ix]; s.curJob=ix; s.xu=nullptr; tlXU=nullptr;   // prof7R3q --xqcapb: list jobs are not capped
          if(VERB){ std::lock_guard<std::mutex> lk(rm); fprintf(stderr,"start %d:",ix); for(int l:job) fprintf(stderr," %d(r%d)",vecOf[l],rk[l]); fprintf(stderr,"\n"); } if(!s.replay(job)){ if(s.replayWhy!=2){ fprintf(stderr,"replay failed (canonicity)\n"); exit(5); }
            if(PCF){ pcOpen(ix,2,job,nullptr); std::string& B=tlPc.buf; pcU8(B,0x03); pcU8(B,11); pcU8(B,(unsigned)(s.rp.size()-1)); pcU8(B,(unsigned)s.addWhy);   // prof7R3: replay cut segment
              if(s.addWhy==1 || s.addWhy==2){ pcU8(B,(unsigned)s.addDim); for(int j=0;j<s.addDim;j++) pcU16(B,s.addRows[j]); } else pcU8(B,(unsigned)s.addW); pcChunk(true); }
            s.unreplay(job); gReplayCut++;   // prof7L39: the prefix breaks a capacity of this table: no profiles below it
            { std::lock_guard<std::mutex> lk(rm); rootDone[ix]=1; if(outst[ix].load()==0) unitDone(ix); }
            { std::lock_guard<std::mutex> lq(qmu); activeR--; checkFin(); } continue; }
          long long lv0=s.myLeaf, pf0=s.myProf;
          if(KEST>0){ std::mt19937_64 krng(SAMPLE_SEED*1000003ULL+ix); double sm=0,s2=0,mx=0; auto tk=std::chrono::steady_clock::now();
            for(long long kk=0;kk<KEST;kk++){ s.resetLists(); double e=s.kdive(job.back(),R-(int)job.size(),krng); sm+=e; s2+=e*e; mx=std::max(mx,e); }
            s.unreplay(job); double K=KEST, mean=sm/K, se=sqrt(std::max(0.0,s2/K-mean*mean)/K);
            double ks=std::chrono::duration<double>(std::chrono::steady_clock::now()-tk).count();
            { std::lock_guard<std::mutex> lk(rm); fprintf(stderr,"kest %d:",ix); for(int l:job) fprintf(stderr," %d",vecOf[l]);
              fprintf(stderr," | dives %lld mean %.4g se %.3g max %.4g | %.1fs\n",KEST,mean,se,mx,ks); }
            { std::lock_guard<std::mutex> lq(qmu); activeR--; checkFin(); } continue; }
          s.pcBegin(ix,0,job,std::array<uint64_t,8>{});   // prof7R3: the job's root segment
          if(PCF){ std::lock_guard<std::mutex> lk(rm); gU[ix].rootSeg=tlPc.id; }   // prof7R3q
          s.resetLists(); s.jobBase=*s.doneP; s.dfs(job.back(),R-(int)job.size(),1.0); s.unreplay(job); certFlush(); if(PCF) pcChunk(true);
          { std::lock_guard<std::mutex> lk(rm); jnodes[ix]+=s.visited-v0-1; jlv[ix]+=s.myLeaf-lv0; jpf[ix]+=s.myProf-pf0; rootDone[ix]=1; if(outst[ix].load()==0) unitDone(ix); }
          { std::lock_guard<std::mutex> lq(qmu); activeR--; checkFin(); }
          continue; }
        // job list exhausted: run donated pieces (prof7L92: and imported items) until every job is finished
        Job job;
        { std::unique_lock<std::mutex> lq(qmu); checkFin(); idleN++; qcv.wait(lq,[&]{ return !Q.empty() || fdone || gSpill.load(); }); idleN--;
          if(gSpill.load()) break; if(Q.empty() && fdone) break; job=std::move(Q.front()); Q.pop_front(); qsizeA--; activeP++; }
        runPiece(job); }
      totv+=s.visited&1023; s.flush(); certFlush();
      { std::lock_guard<std::mutex> lk(fkmu); const fkx::Stats& a=s.fk.st; gFkSt.calls+=a.calls; gFkSt.cert+=a.cert; gFkSt.feas+=a.feas; gFkSt.err+=a.err; gFkSt.rounds+=a.rounds; gFkSt.lps+=a.lps; gFkSt.cliques+=a.cliques; gFkSt.lazyAdded+=a.lazyAdded; gFkSt.mwcCalls+=a.mwcCalls; gFkSt.mwcCut+=a.mwcCut; gFkSt.over+=a.over; gFkSt.units+=a.units; gFkSt.sing+=a.sing; for(int k=0;k<6;k++) gFkSt.cyc[k]+=a.cyc[k]; }
      if(!s.sp.empty()){ std::lock_guard<std::mutex> lk(gSpmu); for(auto& r:s.sp) gSpillRecs.push_back(std::move(r)); } };
    auto report=[&](bool fin){ std::lock_guard<std::mutex> lk(rm); double el=std::chrono::duration<double>(std::chrono::steady_clock::now()-t1).count();
      if(XQADDR) fprintf(stderr,"R3q: t=%.0fs xq %s exported %lld imported %lld (done %lld) tracked jobs reported %lld, reports acked %lld/%lld, skipped (handed elsewhere) %lld, free slots %d, queue %d\n",
                         el,xconn.load()?"up":"DOWN",(long long)gXexp,(long long)gXimp,(long long)nXimpDone,(long long)nXtrackedDone,(long long)nXrepAck,(long long)nXrep,(long long)gXskipT,xfree.load(),qsizeA.load());
      double S=ndone; if(S<1){ fprintf(stderr,"t=%.0fs none done yet nodes~%lld",el,(long long)totv); lpStats(stderr); stStats(stderr); double pg=0; for(int i=0;i<THREADS;i++) pg+=doneT[i*8]; fprintf(stderr," | prog %.9f\n",pg); return; } double mean=sumN/S; double s2=0; for(double x:sizes) s2+=(x-mean)*(x-mean); double sd=sqrt(s2/std::max(1.0,S-1));
      double F=frontier.size(); double est=above+F+F*mean; double se=F*sd/sqrt(S); double mx=0; for(double x:sizes) mx=std::max(mx,x);
      double rate=(sumN-prevNodes)/std::max(1.0,el); double remain=(F-S)*mean/std::max(1.0,rate);
      fprintf(stderr,"%st=%.0fs done %lld/%zu (%.3f%%) mean %.4g sd %.3g max %.4g | EST total %.4g +- %.2g nodes | rate %.3g n/s | ETA %.3g h | leaves %lld profiles %lld | wl nodes %lld",fin?"FINAL ":"",el,ndone,frontier.size(),100.0*S/std::max(1.0,F),mean,sd,mx,est,se,rate,remain/3600,(long long)nleaf,(long long)nprof,(long long)wNodes);
      for(int k=DMAX+1;k<=8;k++) fprintf(stderr," d%d %lld/%lld",k,(long long)wKill[k],(long long)wScan[k]);
      lpStats(stderr); stStats(stderr);
      { double pg=0; for(int i=0;i<THREADS;i++) pg+=doneT[i*8]; fprintf(stderr," | prog %.9f",pg); }
      fprintf(stderr,"\n"); };
    // prof7L92: the queue client.  One TCP connection to --xq; lines in both directions (protocol in r22/xq/DESIGN.md).
    std::thread xth;
    if(XQADDR){
      xth=std::thread([&](){
        std::string host=XQADDR, port="7919"; { auto c=host.rfind(':'); if(c!=std::string::npos){ port=host.substr(c+1); host=host.substr(0,c); } }
        int fd=-1; std::string inb; long long tTry=0, tHB=0, tWant=0, tDown=nowS(), tLog=0; int lastWant=-1, lastBq=0; bool helloSent=false; auto tBms=std::chrono::steady_clock::now();
        std::string xqMid; bool needResync=false, foreignNow=false, downActed=false; long long tGood=nowS();   // manifest id of our queue; last time we were welcomed
        auto closeFd=[&](){ if(fd>=0){ close(fd); fd=-1; } if(xconn.load()) tDown=nowS(); xconn=false; xready=false; helloSent=false; needResync=false; lastWant=-1; };
        auto rawSend=[&](const std::string& t)->bool{ size_t o=0; while(o<t.size()){ ssize_t w=send(fd,t.data()+o,t.size()-o,MSG_NOSIGNAL); if(w<=0){ if(w<0 && errno==EINTR) continue; return false; } o+=(size_t)w; } return true; };
        auto connectNow=[&]()->bool{
          struct addrinfo hints{}, *res=nullptr; hints.ai_family=AF_INET; hints.ai_socktype=SOCK_STREAM;
          if(getaddrinfo(host.c_str(),port.c_str(),&hints,&res)!=0 || !res) return false;
          int s0=socket(res->ai_family,res->ai_socktype,res->ai_protocol); if(s0<0){ freeaddrinfo(res); return false; }
          int fl=fcntl(s0,F_GETFL,0); fcntl(s0,F_SETFL,fl|O_NONBLOCK); int rc=connect(s0,res->ai_addr,res->ai_addrlen); freeaddrinfo(res);
          if(rc<0 && errno!=EINPROGRESS){ close(s0); return false; }
          if(rc<0){ struct pollfd p{s0,POLLOUT,0}; if(poll(&p,1,5000)<=0){ close(s0); return false; } int er=0; socklen_t el=sizeof er; getsockopt(s0,SOL_SOCKET,SO_ERROR,&er,&el); if(er){ close(s0); return false; } }
          fcntl(s0,F_SETFL,fl&~O_NONBLOCK); int one=1; setsockopt(s0,IPPROTO_TCP,TCP_NODELAY,&one,sizeof one); setsockopt(s0,SOL_SOCKET,SO_KEEPALIVE,&one,sizeof one);
          struct timeval tv{10,0}; setsockopt(s0,SOL_SOCKET,SO_SNDTIMEO,&tv,sizeof tv); fd=s0; return true; };
        auto onLine=[&](const std::string& line){
          std::stringstream ss(line); std::string tag; ss>>tag;
          if(tag=="I"){   // I id kind ix rsvec d v1..vd [dinh=HEX] [win=HEX] [p=VEC] [| d v1..vd]... : an item leased to this run
            long long id; std::string kind; int jx, rsv, d; ss>>id>>kind>>jx>>rsv>>d; std::vector<int> seq; bool ok=(bool)ss && d>=1 && d<=R;
            for(int i=0;i<d && ok;i++){ int v; if(!(ss>>v) || v<1 || v>511 || labOf[v]<0) ok=false; else seq.push_back(labOf[v]); }
            std::vector<std::string> sks; unsigned long long skm=0; std::string bar; std::array<uint64_t,8> din{}; int rpl=-1; bool rg=false; std::vector<std::pair<std::string,int>> rst; unsigned long long rsm=0; std::vector<int32_t> win; bool hw=false;
            while(ok && (ss>>bar)){ if(bar.compare(0,5,"dinh=")==0){ if(!undhex(bar.substr(5),din)) ok=false; continue; }   // prof7R3q
              if(bar.compare(0,4,"win=")==0){ if(!unwhex(bar.substr(4),win)) ok=false; hw=true; continue; }   // batch 12: the witness rows of dinh
              if(bar.compare(0,2,"p=")==0){ int pv=std::stoi(bar.substr(2)); if(pv<1 || pv>511 || labOf[pv]<0) ok=false; else rpl=labOf[pv]; continue; }
              if(bar=="rg=1"){ rg=true; continue; }   // prof7R3q: regeneration of a reported item (its children: pieces "| d v..", ranges "| R d v.. l")
              if(bar!="|"){ ok=false; break; }
              { const std::streampos sp0=ss.tellg(); std::string t3; ss>>t3;
                if(t3=="R"){ int dd; if(!(ss>>dd) || dd<1 || dd>63){ ok=false; break; } std::vector<int> p; for(int i=0;i<dd;i++){ int v; if(!(ss>>v) || v<1 || v>511 || labOf[v]<0){ ok=false; break; } p.push_back(labOf[v]); }
                  int lv=0; if(!ok || !(ss>>lv) || lv<1 || lv>511 || labOf[lv]<0){ ok=false; break; } rst.push_back({pkey(p),labOf[lv]}); rsm|=1ULL<<dd; continue; }
                ss.clear(); ss.seekg(sp0); } int dd; if(!(ss>>dd) || dd<1 || dd>63){ ok=false; break; } std::vector<int> p; for(int i=0;i<dd;i++){ int v; if(!(ss>>v) || v<1 || v>511 || labOf[v]<0){ ok=false; break; } p.push_back(labOf[v]); } if(!ok) break; sks.push_back(pkey(p)); skm|=1ULL<<dd; }
            if(ok && kind.size()==1 && kind[0]=='Q' && PCF && rpl<0) ok=false;   // prof7R3q: a range needs its delta base
            if(ok && kind.size()==1 && (kind[0]=='P' || kind[0]=='Q') && PCF && PCWIT && !hw) ok=false;   // batch 12: and a piece or range its witness
            if(!ok || kind.size()!=1 || (kind[0]!='P' && kind[0]!='Q' && kind[0]!='J') || (kind[0]=='Q' && (rsv<1 || rsv>511 || labOf[rsv]<0))){ fprintf(stderr,"R3q: bad item line '%s'\n",line.c_str()); xsend("E "+std::to_string(id)+" badline"); return; }
            if(gSpill.load() || !XQIMPORT){ xsend("UL "+std::to_string(id)); return; }
            int u=-1; { std::lock_guard<std::mutex> lk(rm); if(!freeSlots.empty()){ u=freeSlots.back(); freeSlots.pop_back(); xfree--; }
              if(u>=0){ XUnit& U=gU[u]; U.kind=kind[0]; U.item=id; U.ix=jx; U.seq=seq; U.rs=(kind[0]=='Q')?labOf[rsv]:-1; U.rp=rpl; U.din=din; U.win=win; U.rootSeg=0; U.pcs.clear(); U.active=true; U.tracked=false; U.noexp=false; U.pexp=U.nexp=0; U.intr=0;
                U.sk.clear(); for(auto& k2:sks) U.sk.insert(k2); U.skmask=skm; U.skHit=0; U.regen=rg; U.rstop.clear(); for(auto& e:rst) U.rstop[e.first]=e.second; U.rsmask=rsm; U.rsHit=0; U.rcut=false; U.rgive=false; rootDone[u]=0; outst[u]=0; jnodes[u]=jlv[u]=jpf[u]=0; jab[u]=0; abortIdx[u]=0; itemSlot[id]=u; } }
            if(u<0){ xsend("UL "+std::to_string(id)); return; }
            gXimp++; xlastWork=nowS();
            { std::lock_guard<std::mutex> lq(qmu); Job j; j.seq=seq; j.w=0.0; j.ix=u; j.rs=gU[u].rs; j.root=true; j.dinh=din; j.win=win; Q.push_back(std::move(j)); qsizeA++; } qcv.notify_one(); return; }
          if(tag=="XA"||tag=="XN"){ long long c; ss>>c; std::pair<int,Job> pe; bool have=false;
            { std::lock_guard<std::mutex> lk(xmu); auto it=xpend.find(c); if(it!=xpend.end()){ pe=std::move(it->second); xpend.erase(it); have=true; } }
            if(!have) return; xpendN--; int u=pe.first;
            if(tag=="XA"){ long long child=0, par=0; ss>>child>>par; gXexp++;
              std::lock_guard<std::mutex> lk(rm); XUnit& U=gU[u]; U.pexp--; U.nexp++;
              if((size_t)u<NF && !U.tracked){ U.tracked=true; U.item=par; U.exempt=true; jitem2ix[par]=u; }
              if(--outst[u]==0 && rootDone[u]) unitDone(u); }
            else { std::string why; ss>>why; { std::lock_guard<std::mutex> lk(rm); XUnit& U=gU[u]; U.pexp--; U.noexp=true; }
              if(!gSpill.load()){ { std::lock_guard<std::mutex> lq(qmu); Q.push_front(std::move(pe.second)); qsizeA++; } qcv.notify_one(); } }   // a spill of that unit is refused for the same reason
            { std::lock_guard<std::mutex> lq(qmu); checkFin(); } return; }
          if(tag=="SGA"||tag=="SGN"){ std::string k, why; ss>>k>>why;   // prof7R3q (also the answers to SGL)
            { std::lock_guard<std::mutex> lk(pendmu); if(tag=="SGN" && why=="noreport" && sgPend.count(k) && ++sgRetry[k]<=40){ fprintf(stderr,"R3q: segment for %s: the queue has no report yet; sent again later\n",k.c_str()); return; } sgPend.erase(k); sgRetry.erase(k); }
            if(tag=="SGN") fprintf(stderr,"R3q: segment for %s refused: %s\n",k.c_str(),line.c_str()); return; }
          if(tag=="RA"||tag=="RN"){ long long c; ss>>c; int jix=-2; long long rid=0; { std::lock_guard<std::mutex> lk(gXmu); auto it=gXrep.find(c); if(it!=gXrep.end()){ long long c2=0; sscanf(it->second.c_str(),"R %lld %lld",&c2,&rid); gXrep.erase(it); } auto i2=gXrepIx.find(c); if(i2!=gXrepIx.end()){ jix=i2->second; gXrepIx.erase(i2); } }
            if(rid>0){ std::lock_guard<std::mutex> lk(heldmu); xheld.erase(rid); }
            if(tag=="RA"){ nXrepAck++; if(jix>=0 && gJF){ std::lock_guard<std::mutex> lk(gJmu); gJpend.push_back("H "+std::to_string(jix)+"\n"); } }
            else { std::string why; std::getline(ss,why); fprintf(stderr,"R3q: report %lld rejected:%s\n",c,why.c_str()); }
            return; }
          if(tag=="SPA"||tag=="SPN"){ long long c; ss>>c; std::string rest; std::getline(ss,rest);
            { std::string sl; { std::lock_guard<std::mutex> lk(gXmu); auto it=gXrep.find(c); if(it!=gXrep.end()){ sl=it->second; gXrep.erase(it); } }   // prof7R3q --xqcap: the answer to a split's SP
              if(!sl.empty()){ long long iid=0; char rt[8]={0}; sscanf(sl.c_str(),"SP %*s %7s %lld",rt,&iid); if(iid>0){ std::lock_guard<std::mutex> lk(heldmu); xheld.erase(iid); }
                if(tag=="SPN"){ fprintf(stderr,"R3q: split report of item %lld refused (%s): item returned to the queue\n",iid,rest.c_str()); if(iid>0) xsend("UL "+std::to_string(iid)); } else nXsplitAck++; return; } }
            std::lock_guard<std::mutex> lk(xmu); xspl.erase(c); xsplRes[c]=tag+rest; return; }
          if(tag=="GIVE"){ int k=0; ss>>k; xgive=std::max(0,k); return; }
          if(tag=="T"){ long long jx; while(ss>>jx){ if(jx<0 || (size_t)jx>=NF) continue; xother[jx]=1; bool own; { std::lock_guard<std::mutex> lk(rm); own=gU[jx].tracked; } if(!own) abortIdx[jx]=1; } return; }
          if(tag=="REVOKE"){ long long id; while(ss>>id){ std::lock_guard<std::mutex> lk(rm); auto it=itemSlot.find(id); if(it==itemSlot.end()){ it=jitem2ix.find(id); if(it==jitem2ix.end()) continue; }
              abortIdx[it->second]=1; fprintf(stderr,"R3q: item %lld revoked by the server: unit %d abandoned\n",id,it->second); } return; }
          if(tag=="SPILL"){ if(!gSpill.load()){ fprintf(stderr,"R3q: SPILL from the server\n"); gSpill=1; qcv.notify_all(); } return; }
          if(tag=="EXIT"){ fprintf(stderr,"R3q: EXIT from the server\n"); xrelease=true; { std::lock_guard<std::mutex> lq(qmu); checkFin(); } qcv.notify_all(); return; }
          if(tag=="WELCOME"){ std::string mid; { auto q=line.find("mid="); if(q!=std::string::npos) mid=line.substr(q+4,line.find(' ',q)==std::string::npos?std::string::npos:line.find(' ',q)-q-4); }
            if(xqMid.empty()) xqMid=mid;
            if(mid!=xqMid){ fprintf(stderr,"R3q: %s is another queue (manifest %s, ours %s): not used\n",XQADDR,mid.c_str(),xqMid.c_str()); foreignNow=true; return; }
            needResync=true; fprintf(stderr,"R3q: connected to %s (%s)\n",XQADDR,line.c_str()); return; }
          if(tag=="PING"){ xsend("PONG"); return; }
          if(tag=="ERR"){ fprintf(stderr,"R3q: server error: %s\n",line.c_str()); return; } };
        long long tRec=0, tSgr=0;
        while(!xstop.load()){
          long long now=nowS();
          if(xready.load()) tGood=now;
          if(!recFiles.empty() && now-tRec>=10){ tRec=now; recCheck(); }   // prof7R3q: recovered .pend files whose segments the queue answered
          if(now-tSgr>=15){ tSgr=now; std::vector<std::string> rs; { std::lock_guard<std::mutex> lk(pendmu); for(auto& kv:sgRetry){ auto it=sgPend.find(kv.first); if(it!=sgPend.end()) rs.push_back(it->second); } } for(auto& l:rs) xsend(l); }   // SG / SGL refused with "noreport"
          if(!downActed && XQDOWN>0 && now-tGood>=XQDOWN){ bool work; { std::lock_guard<std::mutex> lq(qmu); work=!Q.empty() || activeR>0 || activeP>0 || nextI.load()<order.size(); }
            if(!work && xpendN.load()>0){ downActed=true; fprintf(stderr,"R3q: queue unusable for %llds with %d hand-offs unanswered: spill to file\n",now-tGood,xpendN.load()); gSpill=1; qcv.notify_all(); }
            else if(!work && (XQHELPER || XQLINGER>0) && !xrelease.load()){ downActed=true; fprintf(stderr,"R3q: queue unusable for %llds: releasing\n",now-tGood); xrelease=true; { std::lock_guard<std::mutex> lq(qmu); checkFin(); } qcv.notify_all(); } }
          if(fd<0){ xlastWork=now;   // linger counts connected time only
            if(now-tTry>=5){ tTry=now; if(connectNow()){ xconn=true; inb.clear(); }
              else if(now-tLog>=60){ tLog=now; fprintf(stderr,"R3q: queue %s unreachable for %llds\n",XQADDR,now-tDown); } }
            if(fd<0){ std::this_thread::sleep_for(std::chrono::milliseconds(200)); continue; } }
          if(!helloSent){   // HELLO alone; after WELCOME (our manifest) everything still waiting for an answer, then the items held here
            char b[4096]; snprintf(b,sizeof b,"HELLO 1 name=%s host=%s pid=%d compat=%016llx space=%016llx pool=%s statedir=%s frontier=%s out=%s xqout=%s threads=%d mode=%s rord=%d\n",
                                   xqName.c_str(),xqHost.c_str(),(int)getpid(),gCompat,gFP,xqPool.c_str(),xqStateDir.c_str(),FRONTF?FRONTF:"-",outpath,xqOutPath.c_str(),THREADS,XQHELPER?"H":"L",RORD);
            if(!rawSend(std::string(b))){ closeFd(); continue; } helloSent=true; tHB=0; }
          if(needResync){ needResync=false;
            std::string t;
            { std::lock_guard<std::mutex> lk(xmu); for(auto& kv:xpend){ int u=kv.second.first; t+="X "+std::to_string(kv.first)+" "+parentRef(u)+" P "+vecs(kv.second.second.seq)+" dinh="+dhex(kv.second.second.dinh)+(PCWIT?" win="+whex(kv.second.second.win):std::string())+"\n"; } for(auto& kv:xspl) t+=kv.second+"\n"; }
            { std::lock_guard<std::mutex> lk(gXmu); for(auto& kv:gXrep) t+=kv.second+"\n"; }
            { std::string h="HOLD"; { std::lock_guard<std::mutex> lk(rm); for(auto& kv:itemSlot) h+=" "+std::to_string(kv.first); for(size_t u=0;u<NF;u++) if(gU[u].tracked && gU[u].item) h+=" "+std::to_string(gU[u].item); }
              { std::lock_guard<std::mutex> lk(heldmu); for(long long id:xheld) h+=" "+std::to_string(id); } t+=h+"\n"; }   // prof7R3q: and the items whose report is under way
            { std::lock_guard<std::mutex> lk(pendmu); for(auto& kv:sgPend) t+=kv.second+"\n"; }   // prof7R3q: segments of pending reports
            t+="READY\n";
            if(!rawSend(t)){ closeFd(); continue; } xready=true; }
          if(xready.load()){ std::deque<std::string> o; { std::lock_guard<std::mutex> lk(gXmu); o.swap(gXout); }   // nothing goes out before our queue is confirmed
            std::string t; for(auto& x:o) t+=x; if(!t.empty() && !rawSend(t)){ closeFd(); continue; } }
          if(xready.load()){
            { int q; { std::lock_guard<std::mutex> lq(qmu); q=(int)Q.size(); }   // heartbeat: every 10 s, at once after connecting, and when the local queue fills from empty (at most 1/s)
              const auto tms=std::chrono::steady_clock::now(); const double sinceB=std::chrono::duration<double>(tms-tBms).count();
              if(tHB==0 || now-tHB>=10 || (q>0 && lastBq==0 && sinceB>=1.0)){ tHB=now; tBms=tms; lastBq=q; char b[160]; snprintf(b,sizeof b,"B %d %d %d %d",q,idleN.load(),activeR+activeP,xfree.load()); if(!rawSend(std::string(b)+"\n")){ closeFd(); continue; } }
              else if(q==0) lastBq=0; }
            int want=0;   // idle threads with nothing local to do ask for items
            if(XQIMPORT && !gSpill.load() && !xrelease.load()){ bool listDone=nextI.load()>=order.size() || drainNow.load();
              if(listDone){ int q; { std::lock_guard<std::mutex> lq(qmu); q=(int)Q.size(); } want=std::max(0,std::min(idleN.load()-q,xfree.load())); } }
            if(XQPAUSE && access(XQPAUSE,F_OK)==0) want=0;   // prof7R3q: checkd's backpressure (too many unchecked segments here)
            if(want!=lastWant || now-tWant>=10){ tWant=now; lastWant=want; if(!rawSend("W "+std::to_string(want)+"\n")){ closeFd(); continue; } }
            int g=xgive.exchange(0);   // GIVE k: hand up to k queued pieces to the server (shallowest first)
            if(g>0 && XQEXPORT && !gSpill.load()){ std::vector<std::pair<int,Job>> outp;
              { std::lock_guard<std::mutex> lq(qmu); std::lock_guard<std::mutex> lk(rm); int avail=(int)Q.size()-idleN.load()-XQKEEP; int n=std::min(g,avail);
                if(n>0){ std::vector<size_t> cand; for(size_t i=0;i<Q.size();i++){ const Job& j=Q[i]; int u=j.ix; if(j.root || u<0 || (int)j.seq.size()>XQMAXD || jab[u].load() || abortIdx[u].load()) continue;
                    if((size_t)u<NF){ if(gU[u].noexp || xother[u].load()) continue; } else if(!gU[u].active || gU[u].intr.load() || gU[u].regen || gU[u].split.load()) continue; cand.push_back(i); }
                  std::stable_sort(cand.begin(),cand.end(),[&](size_t a,size_t b){ return Q[a].seq.size()<Q[b].seq.size(); }); if((int)cand.size()>n) cand.resize(n);
                  std::sort(cand.begin(),cand.end()); for(size_t k2=cand.size();k2-->0;){ size_t i=cand[k2]; gU[Q[i].ix].pexp++; outp.push_back({Q[i].ix,std::move(Q[i])}); Q.erase(Q.begin()+i); qsizeA--; } } }
              std::string t;
              for(auto& pj:outp){ long long c=++xcseq; std::string line; { std::lock_guard<std::mutex> lk(rm); line="X "+std::to_string(c)+" "+parentRef(pj.first)+" P "+vecs(pj.second.seq)+" dinh="+dhex(pj.second.dinh)+(PCWIT?" win="+whex(pj.second.win):std::string()); }
                { std::lock_guard<std::mutex> lk(xmu); xpend[c]=std::move(pj); } xpendN++; t+=line+"\n"; }
              t+="GD "+std::to_string(outp.size())+"\n"; if(!rawSend(t)){ closeFd(); continue; } } }
          // linger / helper end: nothing local and nothing arriving for --xqlinger seconds
          { bool busy; { std::lock_guard<std::mutex> lq(qmu); busy=!Q.empty() || activeR>0 || activeP>0 || nextI.load()<order.size(); } if(!busy && finBusy.load()>0) busy=true; if(!busy){ std::lock_guard<std::mutex> lk(finmu); busy=!finq.empty(); } if(busy) xlastWork=now;   // prof7R3q: segments still being written count as work (a split's new items may follow)
            if(!xrelease.load() && ((XQLINGER>0 && now-xlastWork.load()>=XQLINGER) || (XQSTOPF && access(XQSTOPF,F_OK)==0))){ xrelease=true; fprintf(stderr,"R3q: %s: releasing\n",(XQSTOPF && access(XQSTOPF,F_OK)==0)?"stop file":"linger time over"); { std::lock_guard<std::mutex> lq(qmu); checkFin(); } qcv.notify_all(); } }
          struct pollfd p{fd,POLLIN,0}; int pr=poll(&p,1,100);
          if(pr>0){ char buf[65536]; ssize_t r=recv(fd,buf,sizeof buf,0); if(r<=0){ fprintf(stderr,"R3q: connection to the queue lost\n"); closeFd(); continue; }
            inb.append(buf,(size_t)r); size_t pos;
            while((pos=inb.find('\n'))!=std::string::npos){ std::string line=inb.substr(0,pos); inb.erase(0,pos+1); if(!line.empty()) onLine(line); }
            if(foreignNow){ foreignNow=false; closeFd(); tTry=now+25; continue; } } }
        if(fd>=0){ rawSend("BYE\n"); close(fd); } });
    }
    std::thread mon([&](){ int nr=0; while(!finF){ for(int i=0;i<60&&!finF;i++) std::this_thread::sleep_for(std::chrono::seconds(1)); if(!finF){ report(false); loadSkip(); if(drainNow){ std::lock_guard<std::mutex> lq(qmu); checkFin(); } if(lpx::PROF && ++nr%10==0) lpx::prof_print(stderr); } } });
    std::atomic<long long> termDeadline{0};
    std::thread jth([&](){ auto last=std::chrono::steady_clock::now(); auto lastSpf=last;   // prof7L84: committer and SIGTERM watcher (prof7L92: spill triggers)
      const double jsync=XQADDR?std::min(JSYNC,2.0):JSYNC;
      while(!finF){ std::this_thread::sleep_for(std::chrono::milliseconds(100));
        if(gUsr1){ gUsr1=0; if(!gSpill.load()){ fprintf(stderr,"R3q: SIGUSR1: spill\n"); gSpill=1; qcv.notify_all(); } }
        if(SPILLF && std::chrono::duration<double>(std::chrono::steady_clock::now()-lastSpf).count()>=1.0){ lastSpf=std::chrono::steady_clock::now();
          if(!gSpill.load() && access(SPILLF,F_OK)==0){ fprintf(stderr,"R3q: spill file %s seen: spill\n",SPILLF); gSpill=1; qcv.notify_all(); } }
        if(gTermSig && XQADDR && XQSPILLTERM && xconn.load() && termDeadline.load()==0){   // prof7L92: SIGTERM while connected: spill to the queue, within --xqtermwait
          termDeadline=nowS()+(long long)XQTERMWAIT; gTermSig=0; fprintf(stderr,"R3q: SIGTERM: spill (deadline %.0fs)\n",XQTERMWAIT); if(!gSpill.load()){ gSpill=1; qcv.notify_all(); } }
        if(gTermSig || (termDeadline.load()>0 && nowS()>=termDeadline.load())){ std::lock_guard<std::mutex> lr(rm); std::lock_guard<std::mutex> lo(outmu);   // no state or profile line is half written now, and none starts
          std::vector<std::string> J,S; { std::lock_guard<std::mutex> lk(gJmu); J.swap(gJpend); S.swap(gSpend); }
          if(OUT){ fflush(OUT); fdatasync(fileno(OUT)); } if(XOUT){ fflush(XOUT); fdatasync(fileno(XOUT)); } { std::lock_guard<std::mutex> lc(certmu); if(CERTF){ fflush(CERTF); fdatasync(fileno(CERTF)); } } { std::lock_guard<std::mutex> lp2(pcmu); if(PCF){ fflush(PCF); fdatasync(fileno(PCF)); } } jwrite(J,S,SF);   // prof7R2: certificate first (prof7R3: and the pcert stream)
          fprintf(stderr,"SIGTERM: profiles synced, %zu journal records and %zu state lines committed; exit 143\n",J.size(),S.size()); fflush(stderr); _exit(143); }
        if((gJF || XQADDR) && std::chrono::duration<double>(std::chrono::steady_clock::now()-last).count()>=jsync){ jcommit(); last=std::chrono::steady_clock::now(); } } });
    std::vector<std::thread> th; for(int i=0;i<THREADS;i++) th.emplace_back(worker,i); for(auto& t:th) t.join();
    int exitRc=0;
    if(gSpill.load()){   // prof7L92: write out every unfinished unit: explored counts + open items; send them to the queue as one message per unit
      auto ts0=std::chrono::steady_clock::now();
      if(XQADDR){ for(int w=0;w<100 && xpendN.load()>0 && xconn.load();w++) std::this_thread::sleep_for(std::chrono::milliseconds(50)); }   // let pending exports resolve (5 s)
      // prof7R3q fast spill: the units the finalizer has not assembled yet (and the one it is assembling) are reported now with seg=pending
      std::vector<std::pair<std::string,FinJob>> pendJobs; std::string pendText; const std::string pendPath=PCF?std::string(PCPATH)+".pend":std::string();
      if(PCF){ std::vector<FinJob> q; FinJob cur; bool curOn=false;
        { std::lock_guard<std::mutex> lk(finmu); while(!finq.empty()){ q.push_back(std::move(finq.front())); finq.pop_front(); } if(finCurOn){ cur=finCur; curOn=true; } }
        auto pendReport=[&](const FinJob& f){ long long c=++xcseq; const std::string key=xqName+":"+std::to_string(c); char b[256]; snprintf(b,sizeof b,"R %lld %lld %lld %lld %lld %d",c,f.item,f.n,f.l,f.p,f.nexp);
          std::string line=std::string(b)+" seg=pending skh="+std::to_string(f.skh)+" rsh="+std::to_string(f.rsh);
          if(f.split) line="SP "+std::to_string(c)+" "+f.spRef+" "+std::to_string(f.n)+" "+std::to_string(f.l)+" "+std::to_string(f.p)+" "+std::to_string(f.nexp)+" seg=pending skh="+std::to_string(f.skh)+f.spKids;   // --xqcap: a split's SP
          { std::lock_guard<std::mutex> lk(gXmu); gXrepIx[c]=f.jix; } { std::lock_guard<std::mutex> lk(gJmu); gRpend.push_back(line); }
          pendText+=pendLine(key,f.kind,f.item,f.job,f.pre,f.rs,f.rp,f.din,f.win,f.root,f.pcs); return key; };
        for(auto& f:q){ const std::string k=pendReport(f); pendJobs.push_back({k,std::move(f)}); }
        if(curOn){ const std::string k=pendReport(cur); std::lock_guard<std::mutex> lk(pendmu); pendRep[cur.item]=k; } }   // the finalizer sends its SG
      std::vector<SpillRec> recs; { std::lock_guard<std::mutex> lk(gSpmu); recs.swap(gSpillRecs); }
      std::deque<Job> rest; { std::lock_guard<std::mutex> lq(qmu); rest.swap(Q); qsizeA=0; }
      std::vector<int> splitU; { std::lock_guard<std::mutex> lk(rm); for(size_t u=NF;u<gNU;u++) if(gU[u].active && gU[u].split.load()){ for(auto& r:gU[u].srecs) recs.push_back(std::move(r)); gU[u].srecs.clear();   // prof7R3q --xqcap: split units not yet reported
        for(auto& j:gU[u].spieces) rest.push_back(std::move(j)); gU[u].spieces.clear(); splitU.push_back((int)u); } }
      std::map<int,std::vector<std::string>> kids; std::vector<long long> giveBack; long long nR=0, nP=0, nK=0;
      std::set<int> rgBack;   // prof7R3q: a regeneration in progress is returned (the queue re-leases it), never spilled
      for(auto& r:recs){ if(gU[r.u].regen){ rgBack.insert(r.u); continue; } std::vector<int> ss2=r.seq; std::string q="Q "+vecs(ss2)+" "+std::to_string(vecOf[r.l]); if(PCF) q+=" p="+std::to_string(vecOf[r.p])+" dinh="+dhex(r.D); if(PCF && PCWIT) q+=" win="+whex(r.win); kids[r.u].push_back(q); nR++; }
      for(auto& j:rest){ if(j.root){ giveBack.push_back(gU[j.ix].item); continue; } if(gU[j.ix].regen){ rgBack.insert(j.ix); continue; } std::string q="P "+vecs(j.seq); if(PCF) q+=" dinh="+dhex(j.dinh); if(PCF && PCWIT) q+=" win="+whex(j.win); kids[j.ix].push_back(q); nP++; }
      for(int u:rgBack){ giveBack.push_back(gU[u].item); kids.erase(u); }
      for(int u:splitU) if(!kids.count(u) && !jab[u].load()) kids[u];   // --xqcap: a split unit with nothing left reports its own part
      for(size_t u=NF;u<gNU;u++) if(gU[u].rgive && gU[u].item && !rgBack.count((int)u)){ giveBack.push_back(gU[u].item); kids.erase((int)u); }   // ranges stopped before their first child
      { std::lock_guard<std::mutex> lk(xmu); for(auto& kv:xpend){ std::string q="K "+xqName+":"+std::to_string(kv.first)+" P "+vecs(kv.second.second.seq); if(PCF) q+=" dinh="+dhex(kv.second.second.dinh); if(PCF && PCWIT) q+=" win="+whex(kv.second.second.win); kids[kv.second.first].push_back(q); nK++; } }   // unresolved exports: the server keeps the copy it already has
      std::vector<std::pair<long long,std::string>> msgs; std::string unst;
      { std::lock_guard<std::mutex> lk(rm);
        for(auto& kv:kids){ int u=kv.first; if(jab[u].load()) continue; gU[u].intr=1; }
        for(auto& kv:kids){ int u=kv.first; if(jab[u].load()) continue; long long c=++xcseq;
          std::string m="SP "+std::to_string(c)+" "+parentRef(u)+" "+std::to_string(jnodes[u])+" "+std::to_string(jlv[u])+" "+std::to_string(jpf[u])+" "+std::to_string(gU[u].nexp);
          if(PCF){ XUnit& U=gU[u]; std::string err, ref;   // prof7R3q: the unit's canonical own part (with its RNG references) as an item segment
            FinJob f; f.u=u; f.item=U.item; f.jix=-1; f.skh=0; f.rsh=0; f.root=U.rootSeg; f.pcs.swap(U.pcs); U.rootSeg=0; f.n=f.l=f.p=0; f.nexp=0;   // fast spill: assembled after the reports
            if((size_t)u<NF){ f.kind=0; f.job=u; f.pre=frontier[u]; f.rs=-1; f.rp=-1; f.din={}; } else { f.kind=U.kind=='P'?1:(U.kind=='J'?0:3); f.job=U.ix; f.pre=U.seq; f.rs=U.rs; f.rp=U.rp; f.din=U.din; f.win=U.win; }
            const std::string key=xqName+":"+std::to_string(c); pendText+=pendLine(key,f.kind,f.item,f.job,f.pre,f.rs,f.rp,f.din,f.win,f.root,f.pcs); pendJobs.push_back({key,std::move(f)}); m+=" seg=pending"; }
          m+=" skh="+std::to_string(gU[u].skHit.load());
          for(auto& k2:kv.second) m+=" | "+k2; msgs.push_back({c,m}); }
        for(size_t k2=nextI.load();k2<order.size();k2++){ int ix=order[k2]; if(!doneIdx[ix]) unst+="U "+std::to_string(ix)+"\n"; } }
      if(!pendText.empty()){ FILE* pf=fopen(pendPath.c_str(),"a"); if(pf){ fprintf(pf,"# R3Q pend 2 run=%s pcert=%s host=%s t=%lld\n%s",xqName.c_str(),PCPATH,xqHost.c_str(),(long long)time(nullptr),pendText.c_str()); fflush(pf); fsync(fileno(pf)); fclose(pf); }
        else fprintf(stderr,"R3q: cannot write %s\n",pendPath.c_str()); pcSync(); }   // prof7R3q: the pcert holds their raw records; the .pend file their assembly data
      jcommit();   // the profiles the spilled counts refer to are on disk before the spill file or any message
      std::string sp=SPILLOUT?std::string(SPILLOUT):(STATEPATH?std::string(STATEPATH)+".spill":std::string(outpath)+".spill");
      { FILE* f=fopen(sp.c_str(),"a"); if(f){ fprintf(f,"# prof7L92 spill fp=%016llx compat=%016llx rord=%d run=%s pool=%s statedir=%s frontier=%s out=%s xqout=%s t=%lld units %zu ranges %lld pieces %lld unresolved %lld\n",
            gFP,gCompat,RORD,xqName.c_str(),xqPool.c_str(),xqStateDir.c_str(),FRONTF?FRONTF:"-",outpath,xqOutPath.c_str(),(long long)time(nullptr),msgs.size(),nR,nP,nK);
          for(auto& m:msgs) fprintf(f,"%s\n",m.second.c_str()); fputs(unst.c_str(),f); { std::lock_guard<std::mutex> lk(gXmu); for(auto& kv:gXrep) fprintf(f,"%s\n",kv.second.c_str()); }
          fflush(f); fsync(fileno(f)); fclose(f); } else fprintf(stderr,"R3q: cannot write the spill file %s\n",sp.c_str()); }
      fprintf(stderr,"R3q: spill: %zu units, %lld range items, %lld queued pieces, %lld unresolved exports, %zu imported items returned; file %s\n",msgs.size(),nR,nP,nK,giveBack.size(),sp.c_str());
      exitRc=75;
      if(XQADDR){
        for(long long id:giveBack) xsend("UL "+std::to_string(id));
        { std::lock_guard<std::mutex> lk(xmu); for(auto& m:msgs) xspl[m.first]=m.second; } for(auto& m:msgs) xsend(m.second);
        double wmax=termDeadline.load()>0?std::max(1.0,(double)(termDeadline.load()-nowS())-2.0):std::max(XQTERMWAIT,30.0);
        auto tw=std::chrono::steady_clock::now(); size_t left=msgs.size(), lrep=1;
        while(std::chrono::duration<double>(std::chrono::steady_clock::now()-tw).count()<wmax){ { std::lock_guard<std::mutex> lk(xmu); left=xspl.size(); } { std::lock_guard<std::mutex> lk(gXmu); lrep=gXrep.size()+gRpend.size(); } if(left==0 && lrep==0) break; std::this_thread::sleep_for(std::chrono::milliseconds(100)); }
        long long nacc=0, nrej=0; std::string res;
        { std::lock_guard<std::mutex> lk(xmu); for(auto& kv:xsplRes){ res+=(kv.second.compare(0,3,"SPA")==0?"ACK ":"NAK ")+std::to_string(kv.first)+kv.second.substr(3)+"\n"; if(kv.second.compare(0,3,"SPA")==0) nacc++; else nrej++; } }
        { std::lock_guard<std::mutex> lk(rm); std::lock_guard<std::mutex> lk2(gJmu); for(auto& m:msgs){ std::stringstream ss3(m.second); std::string a,b,c3; long long cs; ss3>>a>>cs>>b; if(b=="j"){ int jx; ss3>>jx; bool acked; { std::lock_guard<std::mutex> lk3(xmu); acked=xsplRes.count(cs) && xsplRes[cs].compare(0,3,"SPA")==0; } if(acked && gJF) gJpend.push_back("H "+std::to_string(jx)+"\n"); } } }
        { FILE* f=fopen(sp.c_str(),"a"); if(f){ fputs(res.c_str(),f); fprintf(f,"# acked %lld rejected %lld unanswered %zu\n",nacc,nrej,left); fflush(f); fsync(fileno(f)); fclose(f); } }
        fprintf(stderr,"R3q: spill sent: %lld accepted, %lld rejected, %zu unanswered (resubmit with ops/xqctl.py submit %s) in %.1fs\n",nacc,nrej,left,sp.c_str(),std::chrono::duration<double>(std::chrono::steady_clock::now()-ts0).count()); }
      if(PCF && !pendJobs.empty() && getenv("R3Q_TEST_EXIT_AFTER_REPORTS")){ fprintf(stderr,"R3q: test hook R3Q_TEST_EXIT_AFTER_REPORTS: exit before the %zu pending segments are written\n",pendJobs.size()); fflush(stderr); _exit(9); }   // tests of --xqrecover only
      if(PCF && !pendJobs.empty()){   // prof7R3q fast spill: the segments of the pending reports, each sent as soon as it is on disk (until the SIGTERM deadline)
        size_t nd=0; for(auto& pj:pendJobs){ FinJob& f=pj.second; std::string err; const std::string ref=segWritePend(pj.first,f,err);
          if(ref.empty()){ gXqAsmErr++; fprintf(stderr,"R3q: pending segment %s not assembled: %s (declared lost: the queue re-runs the item)\n",pj.first.c_str(),err.c_str()); const std::string sl=sgLost(pj.first,err); { std::lock_guard<std::mutex> lk(pendmu); sgPend[pj.first]=sl; } if(XQADDR) xsend(sl); continue; }
          if(getenv("R3Q_TEST_EXIT_AFTER_SEGS") && (long long)nd+1>=atoll(getenv("R3Q_TEST_EXIT_AFTER_SEGS"))){ fprintf(stderr,"R3q: test hook R3Q_TEST_EXIT_AFTER_SEGS: exit after %zu pending segments written, before their SG\n",nd+1); fflush(stderr); _exit(9); }   // tests of --xqrecover only
          xqSegSync(); const std::string sl="SG "+pj.first+" seg="+ref; { std::lock_guard<std::mutex> lk(pendmu); sgPend[pj.first]=sl; } if(XQADDR) sgSend(pj.first,sl); nd++; }
        fprintf(stderr,"R3q: fast spill: %zu of %zu pending segments written after the reports\n",nd,pendJobs.size()); }
      if(PCF){ auto tw2=std::chrono::steady_clock::now(); const double wm=termDeadline.load()>0?std::max(1.0,(double)(termDeadline.load()-nowS())-1.0):30.0;   // the finalizer's last job and the answers
        while(std::chrono::duration<double>(std::chrono::steady_clock::now()-tw2).count()<wm){ bool busy; { std::lock_guard<std::mutex> lk(finmu); busy=finCurOn; } size_t np; { std::lock_guard<std::mutex> lk(pendmu); np=sgPend.size()+pendRep.size(); } if(!busy && np==0) break; std::this_thread::sleep_for(std::chrono::milliseconds(50)); }
        size_t np; { std::lock_guard<std::mutex> lk(pendmu); np=sgPend.size()+pendRep.size(); } if(np==0 && !pendText.empty()) rename(pendPath.c_str(),(pendPath+".done").c_str());
        if(!pendText.empty()) fprintf(stderr,"R3q: fast spill: %zu segments still unanswered%s\n",np,np?" (the next launch on this host sends them: --xqrecover)":""); } }
    finDrain();   // prof7R3q: every finished unit's segment written and its report queued
    finF=true; mon.join(); jth.join(); jcommit(); report(true);
    if(XQADDR){   // prof7L92: wait for the queue to take the last reports; keep the unanswered ones for a resubmit
      auto tw=std::chrono::steady_clock::now(); size_t left=0;
      while(std::chrono::duration<double>(std::chrono::steady_clock::now()-tw).count()<std::max(XQTERMWAIT,30.0)){ { std::lock_guard<std::mutex> lk(gXmu); left=gXrep.size(); } if(left==0) break; std::this_thread::sleep_for(std::chrono::milliseconds(100)); }
      if(left>0){ std::string pf=(STATEPATH?std::string(STATEPATH):std::string(outpath))+".xqpend"; FILE* f=fopen(pf.c_str(),"a");
        if(f){ fprintf(f,"# prof7L92 unanswered reports run=%s t=%lld\n",xqName.c_str(),(long long)time(nullptr)); std::lock_guard<std::mutex> lk(gXmu); for(auto& kv:gXrep) fprintf(f,"%s\n",kv.second.c_str()); fflush(f); fsync(fileno(f)); fclose(f); }
        fprintf(stderr,"R3q: %zu reports unanswered by the queue: kept in %s (resubmit with ops/xqctl.py submit)\n",left,pf.c_str()); }
      if(gJF){ jcommit(); }   // H lines of the last acks
      xstop=true; xth.join(); if(XOUT){ fflush(XOUT); fclose(XOUT); XOUT=nullptr; gXOUTsync=nullptr; } }
    { std::lock_guard<std::mutex> lk(finmu); finStop=true; } fincv.notify_all(); finth.join();
    if(gXqSeg){ std::lock_guard<std::mutex> lk(gXqSegMu); fflush(gXqSeg); fdatasync(fileno(gXqSeg)); fclose(gXqSeg); gXqSeg=nullptr; }
    if(PCF || gXqSegN.load()) fprintf(stderr,"R3q: item segments %lld (%lld bytes) in %s, assembly failures %lld, write failures %lld, pcert bytes freed %lld\n",(long long)gXqSegN,(long long)gXqSegB,gXqSegPath.c_str(),(long long)gXqAsmErr,(long long)gXqSegWErr,gOwn.punched);
    if(XQCAP>0 || XQCAPB>0) fprintf(stderr,"R3q: item-size cap %lld nodes / %.0f MB (split depth <= %d): %lld units reached it, %lld split reports, %lld accepted\n",XQCAP,XQCAPB/1e6,XQCAPD,(long long)gXsplit,(long long)nXsplitDone,(long long)nXsplitAck);
    if(PCF){ fflush(PCF); fdatasync(fileno(PCF)); fclose(PCF); PCF=nullptr;   // prof7R3
      fprintf(stderr,"R3 pcert: %lld bytes in %lld blocks; records NODE %lld LEAF %lld CUT %lld OPEN %lld VROWS %lld XROWS %lld WB %lld BLK %lld (labels %lld) | T %lld C %lld X %lld (kill types T %lld C %lld X %lld) CANON %lld PREFF %lld TYPE %lld DOOM %lld ADDF %lld DON %lld SKR %lld SKP %lld ABORT %lld | internal check failures %lld\n",
        (long long)gPcBytes,(long long)gPcBlocks,(long long)gPcN[1],(long long)gPcN[2],(long long)gPcN[3],(long long)gPcN[4],(long long)gPcN[0x10],(long long)gPcN[0x11],(long long)gPcN[0x12],(long long)gPcN[0x13],(long long)gPcBlk,
        (long long)gPcN[0x20],(long long)gPcN[0x21],(long long)gPcN[0x22],(long long)gPcTC[0],(long long)gPcTC[1],(long long)gPcTC[2],(long long)gPcN[0x23],(long long)gPcN[0x24],(long long)gPcN[0x25],(long long)gPcN[0x26],(long long)gPcN[0x27],(long long)gPcN[0x28],(long long)gPcN[0x29],(long long)gPcN[0x2A],(long long)gPcN[6],(long long)gPcErr);
      if(PCFK>0){ static const char* BK[7]={"0-1","2-8","9-15","16-63","64-255","256-1000","1001+"}; fprintf(stderr,"R3 Farkas%s (kind bb: attempts certificates ms/attempt B/cert constraints/cert units/cert):",PCFK6?" check6":"");
        for(int k=1;k<6;k++) for(int b=0;b<7;b++) if(gFkA[k][b]) fprintf(stderr," | %d %s: %lld %lld %.2f %.0f %.1f %.1f",k,BK[b],(long long)gFkA[k][b],(long long)gFkS[k][b],gFkC[k][b]/2.6e6/gFkA[k][b],gFkS[k][b]?(double)gFkB[k][b]/gFkS[k][b]:0.0,gFkS[k][b]?(double)gFkN[k][b]/gFkS[k][b]:0.0,gFkS[k][b]?(double)gFkU[k][b]/gFkS[k][b]:0.0);
        fprintf(stderr,"\n"); }
      if(XPS){ static const char* BK[7]={"0-1","2-8","9-15","16-63","64-255","256-1000","1001+"}; fprintf(stderr,"R3 bulk peel (kind bb: attempts certificates ms/attempt B/cert):");
        for(int k=2;k<6;k++) for(int b=0;b<7;b++) if(gXpA[k][b]) fprintf(stderr," | %d %s: %lld %lld %.2f %.0f",k,BK[b],(long long)gXpA[k][b],(long long)gXpS[k][b],gXpC[k][b]/2.6e6/gXpA[k][b],gXpS[k][b]?(double)gXpB[k][b]/gXpS[k][b]:0.0);
        if(XP2){ static const char* PH[7]={"gen","setup","tree","cover","excl","prune","emit"}; static const char* BQ[7]={"0-1","2-8","9-15","16-63","64-255","256-1000","1001+"};
          fprintf(stderr,"\nR3 xp2 context row gathering %.3f ms each; contexts with a crow kill %lld, with kind-4 kills only %lld",gX2CtxN?gX2Gath/1e4/gX2CtxN:0.0,(long long)gX2CtxK5,(long long)gX2CtxK4);
          for(int c=0;c<3;c++) if(gX2GN[c]) fprintf(stderr,"\nR3 xp2 contexts %s: %lld, gathering %.3f ms each, residual-2 rows %.0f each",c==2?"with a crow kill":c==1?"with kind-4 kills only":"with kinds 2/3 only",(long long)gX2GN[c],gX2GC[c]/1e4/gX2GN[c],(double)gX2GR[c]/gX2GN[c]);
          fprintf(stderr,"\nR3 xp2 node contexts %lld: %.3f ms each (rows %.0f residual-1, %.0f residual-2), dictionary %.1f, extras outside L1 %.1f, node rows %.1f per context; X records %lld bytes\n",(long long)gX2CtxN,gX2CtxN?gX2Ctx/1e4/gX2CtxN:0.0,gX2CtxN?(double)gX2Rows1/gX2CtxN:0.0,gX2CtxN?(double)gX2Rows2/gX2CtxN:0.0,gX2CtxN?(double)gX2Dict/gX2CtxN:0.0,gX2CtxN?(double)gX2Ext/gX2CtxN:0.0,gX2CtxN?(double)gX2NodeR/gX2CtxN:0.0,(long long)gX2B);
          double tot[7]={0}; for(int k=2;k<=5;k++) for(int b=0;b<7;b++){ if(!gX2A[k][b]) continue; fprintf(stderr,"R3 xp2 kind %d bb %-8s: %8lld kills, %8lld certificates | us/kill",k,BQ[b],(long long)gX2A[k][b],(long long)gX2S[k][b]);
              for(int q=0;q<7;q++){ fprintf(stderr," %s %.0f",PH[q],gX2P[k][b][q]/10.0/gX2A[k][b]); tot[q]+=gX2P[k][b][q]/10.0; } fprintf(stderr," | total %.1f s\n",gX2P[k][b][0]/1e7); }
          fprintf(stderr,"R3 xp2 total s:"); for(int q=0;q<7;q++) fprintf(stderr," %s %.1f",PH[q],tot[q]/1e6); fprintf(stderr," contexts %.1f\n",gX2Ctx/1e7); }
        fprintf(stderr,"\nR3 bulk peel nodes: %lld node contexts, %.1f rows each, setup %.2f ms each, node records %lld bytes | node cuts 5/6: %lld certified, %lld not, %.2f ms each\n",(long long)gXpNodes,gXpNodes?(double)gXpRows/gXpNodes:0.0,gXpNodes?gXpNodeC/2.6e6/gXpNodes:0.0,(long long)gXpNodeB,(long long)gXpCut[0],(long long)gXpCut[1],(gXpCut[0]+gXpCut[1])?gXpCutC/2.6e6/(gXpCut[0]+gXpCut[1]):0.0); }
      if(PCFK>0) fprintf(stderr,"R3 Farkas generator: check6 units %lld (singletons %lld), integer candidates rejected for supply per point > %lld: %lld | scale D of certificates 1: %lld 2: %lld 3-4: %lld 5-8: %lld 9-16: %lld 17-64: %lld 65+: %lld\n",gFkSt.units,gFkSt.sing,PCFK6SUP,gFkSt.over,(long long)gFkDh[0],(long long)gFkDh[1],(long long)gFkDh[2],(long long)gFkDh[3],(long long)gFkDh[4],(long long)gFkDh[5],(long long)gFkDh[6]);
      if(PCFK>0) fprintf(stderr,"R3 Farkas generator: calls %lld certificates %lld LP-feasible %lld errors %lld | rounds %lld LPs %lld cliques %lld lazy rows %lld | exact separations %lld (node limit %lld) | Gcycles first LP %.1f later LPs %.1f Farkas LP %.1f integer %.1f lazy sep %.1f clique sep %.1f build %.1f | residual-2 rows per node %.0f\n",gFkSt.calls,gFkSt.cert,gFkSt.feas,gFkSt.err,gFkSt.rounds,gFkSt.lps,gFkSt.cliques,gFkSt.lazyAdded,gFkSt.mwcCalls,gFkSt.mwcCut,gFkSt.cyc[0]/1e9,gFkSt.cyc[1]/1e9,gFkSt.cyc[2]/1e9,gFkSt.cyc[3]/1e9,gFkSt.cyc[4]/1e9,gFkSt.cyc[5]/1e9,gFkBuild/1e9,gFkR2n?(double)gFkR2/gFkR2n:0.0);
      { static const char* BK[7]={"0-1","2-8","9-15","16-63","64-255","256-1000","1001+"}; long long tn=0, tb=0; fprintf(stderr,"R3 X kills (kind bb: kills search-nodes):");
        for(int k=1;k<7;k++) for(int b=0;b<7;b++) if(gXn[k][b]){ fprintf(stderr," | %d %s: %lld %lld",k,BK[b],(long long)gXn[k][b],(long long)gXb[k][b]); tn+=gXn[k][b]; tb+=gXb[k][b]; }
        fprintf(stderr," | total %lld %lld\n",tn,tb); }
      if(PCEXP>0 || PCEXP5>0 || PCNOREP) fprintf(stderr,"R3 expansion: %lld kills expanded, %lld nodes inside them, %lld accepted leaves inside them (must be 0)\n",(long long)gExpK,(long long)gExpN,(long long)gExpBad);
      if(LEAFV7) fprintf(stderr,"R3 leafv7: %lld leaf certificate records (%lld need none: rank sum < 27), %lld via the fit fallback, %lld / %lld retried at 2e6 / 2e7 calls, %lld without a certificate (must be 0); %.1f bits each, %.2f ms each, max %.1f ms\n",(long long)gLv7N,(long long)gLv7None,(long long)gLv7Fit,(long long)gLv7Big1,(long long)gLv7Big2,(long long)gLv7Fail,gLv7N?(double)gLv7Bits/gLv7N:0.0,gLv7N?gLv7Us/1e3/gLv7N:0.0,gLv7MaxUs/1e3);   // batch 13
      if(PCNOREP) fprintf(stderr,"R3 no replay: X kills expanded for lack of a certificate by kind 1-5: %lld %lld %lld %lld %lld; node cuts 5 / 6 not taken: %lld / %lld (%lld nodes searched instead)\n",(long long)gNrX[1],(long long)gNrX[2],(long long)gNrX[3],(long long)gNrX[4],(long long)gNrX[5],(long long)gNrCut[0],(long long)gNrCut[1],(long long)gNrCutN);
      if(TLMAX>=0){ long long t=0,k=0,n=0; for(int d=0;d<24;d++){ t+=gTLt[d]; k+=gTLk[d]; n+=gTLn[d]; } fprintf(stderr,"R3 tl2: tests %lld cuts %lld search nodes %lld\n",t,k,n); }
      fprintf(stderr,"R3 cover attempts/successes by node count:"); for(int b=0;b<17;b++) if(gPcAtt[b]) fprintf(stderr," %d:%lld/%lld",b,(long long)gPcAtt[b],(long long)gPcSuc[b]); fprintf(stderr,"\n");
      fprintf(stderr,"R3 pcert cycles (G): enter %.1f classify rows %.1f classify kills %.1f open %.1f | classify calls %llu, residual-1 rows per call %.0f\n",gPcCyc[0]/1e9,gPcCyc[1]/1e9,gPcCyc[2]/1e9,gPcCyc[3]/1e9,(unsigned long long)gPcCyc[6],gPcCyc[6]?(double)gPcCyc[5]/gPcCyc[6]:0.0); }
    if(gJF || gJdmask || gJrmask) fprintf(stderr,"L84: journal records %lld (%lld commits), subtrees skipped %lld (%lld nodes)\n",(long long)gJrec,(long long)gJsyncs,(long long)gJskip,(long long)gJskipN);
    if(gJF){ fclose(gJF); gJF=nullptr; }
    if(lpx::PROF){ lpx::prof_print(stderr); fprintf(stderr,"LPPROF first builds %.0f ms, pool rebuilds %lld (%.0f ms)\n",gBLDns/1e6,(long long)gRBn,gRBns/1e6); }
    if(SF) fclose(SF); if(OUT) fclose(OUT);
    { double est=0; fprintf(stderr,"job-tree depth counts (scaled by 1/p below the sample depth):");
      for(int d=0;d<=R;d++){ if(!gDepth[d]) continue; double sc=(SAMPLE_D>=0&&d>SAMPLE_D)?1.0/SAMPLE_P:1.0; est+=gDepth[d]*sc; fprintf(stderr," d%d %lld(%.4g)",d,gDepth[d],gDepth[d]*sc); }
      fprintf(stderr,"\nEST job-tree nodes %.4g\n",est);
      if(!gSub.empty()){ std::sort(gSub.begin(),gSub.end()); double sm=0,s2=0; for(auto x:gSub){ sm+=x; s2+=(double)x*x; } double S=gSub.size(); double mean=sm/S; double sd=sqrt(std::max(0.0,s2/S-mean*mean));
        fprintf(stderr,"SAMPLE depth %d p %g: N_D %lld sampled %zu mean %.1f sd %.1f median %lld p90 %lld max %lld\n",SAMPLE_D,SAMPLE_P,gDepth[SAMPLE_D],gSub.size(),mean,sd,gSub[gSub.size()/2],gSub[(size_t)(0.9*S)],gSub.back()); } }
    fprintf(stderr,"DONE frontier run: profiles %lld (minr1 cuts %lld, jobs cut at replay %lld, skipped as done elsewhere %lld, abandoned as done elsewhere %lld)\n",(long long)nprof,(long long)gR1cut,(long long)gReplayCut,(long long)nSkipped,(long long)nAborted);
    if(XQADDR || exitRc) fprintf(stderr,"R3q DONE: exported %lld imported %lld (reported %lld) tracked jobs reported %lld, skipped as handed elsewhere %lld, exit %d\n",(long long)gXexp,(long long)gXimp,(long long)nXimpDone,(long long)nXtrackedDone,(long long)gXskipT,exitRc);
    if(wcut::ON){ fprintf(stderr,"WCUT"); wcut::stats(stderr); fprintf(stderr,"\n"); }
    if(WBLOCK) fprintf(stderr,"WBLOCK nodes %lld labels %lld W-checks %lld\n",(long long)gWbN,(long long)gWbL,(long long)gWbC);
    if(FLOOK<24){ fprintf(stderr,"FLOOK (tests/cuts by depth):"); for(int d=FLOOK;d<24;d++) if(gFlN[d]) fprintf(stderr," d%d %lld/%lld x%lld",d,(long long)gFlN[d],(long long)gFlC[d],(long long)gRlX[d]); fprintf(stderr,"\n"); }
    if(rootcut::ON) fprintf(stderr,"ROOTCUT leaf tests %lld, leaves cut %lld\n",(long long)rootcut::gCalls,(long long)rootcut::gCut);
    { fprintf(stderr,"DEPTHTIME (CPU s incl/excl):"); for(int d=10;d<23;d++){ unsigned long long a=gIncl[d], b=gIncl[d+1]; fprintf(stderr," d%d %.1f/%.1f",d,a/1e9,(a>b?a-b:0)/1e9); } fprintf(stderr,"\n"); }
    return exitRc; }
