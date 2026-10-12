#!/usr/bin/env python3
"""r3q_block.py L92_BLOCK.txt R3_BASE.cc OUT_BLOCK.cc: prof7R3q's frontier driver block = prof7L92's (the queue client) + prof7R3's stream
lines (segments of jobs and pieces, replay-cut segment, piece journal records with their segment, syncs, statistics) + the item segments."""
import sys
l92,r3,outf=sys.argv[1:4]
s=open(l92).read(); R=open(r3).read()
def rep(old,new,cnt=1):
    global s
    n=s.count(old)
    if n!=cnt: sys.exit('block anchor %r found %d times (want %d)'%(old[:90],n,cnt))
    s=s.replace(old,new)

# journal header: prof7R3's fields
rep('''      char hb[2048]; snprintf(hb,sizeof hb,"# prof7L92 journal fp=%016llx out=%s state=%s jdepth=%d jmin=%lld pid=%d\\n",gFP,outpath,STATEPATH?STATEPATH:"-",JDEPTH,JMIN,(int)getpid()); fputs(hb,gJF); fflush(gJF);''',
    '''      char hb[2048]; snprintf(hb,sizeof hb,"# prof7R3q journal fp=%016llx out=%s state=%s cert=%s pcert=%s jdepth=%d jmin=%lld pid=%d\\n",gFP,outpath,STATEPATH?STATEPATH:"-",CERTPATH?CERTPATH:"-",PCPATH?PCPATH:"-",JDEPTH,JMIN,(int)getpid()); fputs(hb,gJF); fflush(gJF);''')
rep('''U.sk.clear(); for(auto& k2:sks) U.sk.insert(k2); U.skmask=skm;''','''U.sk.clear(); for(auto& k2:sks) U.sk.insert(k2); U.skmask=skm; U.skHit=0; U.regen=rg; U.rstop.clear(); for(auto& e:rst) U.rstop[e.first]=e.second; U.rsmask=rsm; U.rsHit=0; U.rcut=false; U.rgive=false;''')
rep('''} else if(!gU[u].active || gU[u].intr.load()) continue; cand.push_back(i); }''','''} else if(!gU[u].active || gU[u].intr.load() || gU[u].regen || gU[u].split.load()) continue; cand.push_back(i); }''')   # a regeneration hands nothing off; a split unit's pieces go with its SP
rep('''      jcommit();   // the profiles the spilled counts refer to are on disk before the spill file or any message''',
    '''      if(!pendText.empty()){ FILE* pf=fopen(pendPath.c_str(),"a"); if(pf){ fprintf(pf,"# R3Q pend 2 run=%s pcert=%s host=%s t=%lld\\n%s",xqName.c_str(),PCPATH,xqHost.c_str(),(long long)time(nullptr),pendText.c_str()); fflush(pf); fsync(fileno(pf)); fclose(pf); }
        else fprintf(stderr,"R3q: cannot write %s\\n",pendPath.c_str()); pcSync(); }   // prof7R3q: the pcert holds their raw records; the .pend file their assembly data
      jcommit();   // the profiles the spilled counts refer to are on disk before the spill file or any message''')
rep('''        while(!xstop.load()){
          long long now=nowS();
          if(xready.load()) tGood=now;''','''        long long tRec=0;
        while(!xstop.load()){
          long long now=nowS();
          if(xready.load()) tGood=now;
          if(!recFiles.empty() && now-tRec>=10){ tRec=now; recCheck(); }   // prof7R3q: recovered .pend files whose segments the queue answered''')
rep('''in %.1fs\\n",nacc,nrej,left,sp.c_str(),std::chrono::duration<double>(std::chrono::steady_clock::now()-ts0).count()); } }''',
    '''in %.1fs\\n",nacc,nrej,left,sp.c_str(),std::chrono::duration<double>(std::chrono::steady_clock::now()-ts0).count()); }
      if(PCF && !pendJobs.empty() && getenv("R3Q_TEST_EXIT_AFTER_REPORTS")){ fprintf(stderr,"R3q: test hook R3Q_TEST_EXIT_AFTER_REPORTS: exit before the %zu pending segments are written\\n",pendJobs.size()); fflush(stderr); _exit(9); }   // tests of --xqrecover only
      if(PCF && !pendJobs.empty()){   // prof7R3q fast spill: the segments of the pending reports, each sent as soon as it is on disk (until the SIGTERM deadline)
        size_t nd=0; for(auto& pj:pendJobs){ FinJob& f=pj.second; std::string err; const std::string ref=segWrite(f.kind,f.item,f.job,f.pre,f.rs,f.rp,f.din,f.win,f.root,f.pcs,err);
          if(ref.empty()){ gXqAsmErr++; fprintf(stderr,"R3q: pending segment %s not assembled: %s (declared lost: the queue re-runs the item)\\n",pj.first.c_str(),err.c_str()); const std::string sl=sgLost(pj.first,err); { std::lock_guard<std::mutex> lk(pendmu); sgPend[pj.first]=sl; } if(XQADDR) xsend(sl); continue; }
          xqSegSync(); const std::string sl="SG "+pj.first+" seg="+ref; { std::lock_guard<std::mutex> lk(pendmu); sgPend[pj.first]=sl; } if(XQADDR) xsend(sl);
          { FILE* pf=fopen(pendPath.c_str(),"a"); if(pf){ fprintf(pf,"D %s seg=%s\\n",pj.first.c_str(),ref.c_str()); fclose(pf); } } nd++; }
        fprintf(stderr,"R3q: fast spill: %zu of %zu pending segments written after the reports\\n",nd,pendJobs.size()); }
      if(PCF){ auto tw2=std::chrono::steady_clock::now(); const double wm=termDeadline.load()>0?std::max(1.0,(double)(termDeadline.load()-nowS())-1.0):30.0;   // the finalizer's last job and the answers
        while(std::chrono::duration<double>(std::chrono::steady_clock::now()-tw2).count()<wm){ bool busy; { std::lock_guard<std::mutex> lk(finmu); busy=finCurOn; } size_t np; { std::lock_guard<std::mutex> lk(pendmu); np=sgPend.size()+pendRep.size(); } if(!busy && np==0) break; std::this_thread::sleep_for(std::chrono::milliseconds(50)); }
        size_t np; { std::lock_guard<std::mutex> lk(pendmu); np=sgPend.size()+pendRep.size(); } if(np==0 && !pendText.empty()) rename(pendPath.c_str(),(pendPath+".done").c_str());
        if(!pendText.empty()) fprintf(stderr,"R3q: fast spill: %zu segments still unanswered%s\\n",np,np?" (the next launch on this host sends them: --xqrecover)":""); } }''')
# an imported job root cut at replay (its prefix breaks a capacity of this table): R3's kind-2 segment, as for a list job; done with no nodes
rep('''          s.unreplay(job.seq); s.xu=nullptr; fprintf(stderr,"L92: imported item %lld does not replay here (why %d): reported as an error\\n",gU[ix].item,s.replayWhy);''',
    '''          if(job.root && gU[ix].kind=='J' && s.replayWhy==2){   // prof7R3q: R3's replay-cut segment (CUT 11), reported with no nodes
            if(PCF){ pcOpen(gU[ix].ix,2,job.seq,nullptr); std::string& B=tlPc.buf; pcU8(B,0x03); pcU8(B,11); pcU8(B,(unsigned)(s.rp.size()-1)); pcU8(B,(unsigned)s.addWhy);
              if(s.addWhy==1 || s.addWhy==2){ pcU8(B,(unsigned)s.addDim); for(int j=0;j<s.addDim;j++) pcU16(B,s.addRows[j]); } else pcU8(B,(unsigned)s.addW);
              const unsigned long long sid=tlPc.id; pcChunk(true); std::lock_guard<std::mutex> lk(rm); gU[ix].rootSeg=sid; }
            { std::lock_guard<std::mutex> lk(rm); gU[ix].rcut=true; }
            s.unreplay(job.seq); s.xu=nullptr; gReplayCut++;
            { std::lock_guard<std::mutex> lk(rm); rootDone[ix]=1; if(outst[ix]==0) unitDone(ix); }
            { std::lock_guard<std::mutex> lq(qmu); activeP--; checkFin(); } return; }
          s.unreplay(job.seq); s.xu=nullptr; fprintf(stderr,"L92: imported item %lld does not replay here (why %d): reported as an error\\n",gU[ix].item,s.replayWhy);''')
rep('''            if(want!=lastWant || now-tWant>=10){''','''            if(XQPAUSE && access(XQPAUSE,F_OK)==0) want=0;   // prof7R3q: checkd's backpressure (too many unchecked segments here)
            if(want!=lastWant || now-tWant>=10){''')
# compat: the content of the bulk-peel inputs (--pcxp C2T LAB) too, not only their paths
rep('''      mx(gTabHash); mx((unsigned long long)R); mx((unsigned long long)WL.size());''',
    '''      mx(gTabHash); mx((unsigned long long)R); mx((unsigned long long)WL.size());
      if(XPS){ auto hb=[](const char* p,size_t n){ unsigned long long th=0x9E3779B97F4A7C15ULL^(unsigned long long)n; size_t i=0; for(;i+8<=n;i+=8){ unsigned long long x; memcpy(&x,p+i,8); th=(th^x)*0xBF58476D1CE4E5B9ULL; th^=th>>31; } for(;i<n;i++){ th=(th^(unsigned char)p[i])*0xBF58476D1CE4E5B9ULL; th^=th>>31; } return th; };   // prof7R3q
        mx(hb((const char*)XPLAB.data(),XPLAB.size())); for(int i=1;i+1<argc;i++) if(!strcmp(argv[i],"--pcxp") || !strcmp(argv[i],"--xpeel")){ FILE* cf=fopen(argv[i+1],"rb"); std::string cb; if(cf){ char tb[1<<16]; size_t k; while((k=fread(tb,1,sizeof tb,cf))>0) cb.append(tb,k); fclose(cf); } mx(hb(cb.data(),cb.size())); } }''')
# own-stream index and the item segment file
rep('''    { struct sigaction sa{}; sa.sa_handler=onUsr1; sigemptyset(&sa.sa_mask); sigaction(SIGUSR1,&sa,nullptr); }   // prof7L92: SIGUSR1 = spill''',
    '''    { struct sigaction sa{}; sa.sa_handler=onUsr1; sigemptyset(&sa.sa_mask); sigaction(SIGUSR1,&sa,nullptr); }   // prof7L92: SIGUSR1 = spill
    xqr3::gLeafx=PCLEAFX; xqr3::gCutx=(XPS!=nullptr);   // prof7R3q: the record flags of this run's stream (header #leafx / #cutx)
    if(XQCAPD<0) XQCAPD=SPILLD; if(XQCAP>0 || XQCAPB>0) fprintf(stderr,"R3q: item-size cap: an imported unit is split when its own part reaches %lld nodes or %.0f MB of records (0 = no bound; at open nodes of depth <= %d)\\n",XQCAP,XQCAPB/1e6,XQCAPD);
    if(XQRECIPE) fprintf(stderr,"R3q: recipe %s sha256 %s (part of the compat fingerprint)\\n",XQRECIPE,gRecipeSha.c_str());
    if(PCF){ fflush(PCF); gPcFileOff=ftell(PCF); gOwn.fd=open(PCPATH,O_RDONLY); if(XQPUNCH<0) XQPUNCH=XQHELPER?1:0; if(XQPUNCH>0 && XQHELPER) gOwn.fdw=open(PCPATH,O_RDWR);   // a helper has no list job: its pcert is scratch if(gOwn.fd<0){ fprintf(stderr,"R3q: cannot reread %s\\n",PCPATH); return 2; }   // prof7R3q: item assembly reads this run's stream back
      if(XQSEGP) gXqSegPath=XQSEGP; else gXqSegPath=std::string(PCPATH)+".xq";
      if(gXqSegPath[0]!='/'){ char cwd[4096]; if(getcwd(cwd,sizeof cwd)) gXqSegPath=std::string(cwd)+"/"+gXqSegPath; } }''')
# unit bookkeeping: own segments, finalizer
rep('''    auto freeSlot=[&](int u){   // caller holds rm
      XUnit& U=gU[u]; if(U.item) itemSlot.erase(U.item); U.kind=0; U.item=0; U.ix=-1; U.seq.clear(); U.rs=-1; U.active=false; U.pexp=U.nexp=0; U.intr=0; U.skmask=0; U.sk.clear();''',
    '''    auto dropOwn=[&](XUnit& U){ if(U.rootSeg) gOwn.drop(U.rootSeg); for(auto& kv:U.pcs) gOwn.drop(kv.second); U.rootSeg=0; U.pcs.clear(); };   // prof7R3q: segments no item assembly needs
    auto freeSlot=[&](int u){   // caller holds rm
      XUnit& U=gU[u]; if(U.item) itemSlot.erase(U.item); dropOwn(U); U.kind=0; U.item=0; U.ix=-1; U.seq.clear(); U.rs=-1; U.rp=-1; U.din={}; U.win.clear(); U.active=false; U.pexp=U.nexp=0; U.intr=0; U.skmask=0; U.sk.clear(); U.skHit=0; U.regen=false; U.rstop.clear(); U.rsmask=0; U.rsHit=0; U.rcut=false; U.rgive=false; U.live=0; U.bytes=0; U.split=false; U.srecs.clear(); U.spieces.clear();''')
rep('''    auto xqReport=[&](int u,long long item,int jix){   // caller holds rm: the unit's own part is done; sent after the next profile fdatasync
      long long c=++xcseq; char b[256]; snprintf(b,sizeof b,"R %lld %lld %lld %lld %lld %d",c,item,jnodes[u],jlv[u],jpf[u],gU[u].nexp);
      { std::lock_guard<std::mutex> lk(gXmu); gXrepIx[c]=jix; } { std::lock_guard<std::mutex> lk(gJmu); gRpend.push_back(b); } nXrep++; };''',
    '''    // prof7R3q: a finished unit's canonical own-part segment is assembled off the results lock (finalizer thread), written to --xqseg with
    // its sha256, and only then reported; the committer syncs the profiles, the stream and the item segments before the report goes out.
    struct FinJob { int u; long long item; int jix, job, skh, rsh; int kind; std::vector<int> pre; int rs, rp; std::array<uint64_t,8> din; unsigned long long root; std::unordered_map<std::string,unsigned long long> pcs; long long n,l,p; int nexp; std::vector<int32_t> win; bool split=false; std::string spRef, spKids; };   // win: the root's witness rows (--pcwit); split: an --xqcap split (reported by one SP: parent ref, child items)
    std::mutex finmu; std::condition_variable fincv; std::deque<FinJob> finq; std::atomic<int> finBusy{0}; std::atomic<bool> finStop{false};
    std::mutex heldmu; std::unordered_set<long long> xheld;   // items reported or being reported here, until the queue answers (HOLD after a reconnect)
    auto segWriteFrom=[&](xqr3::OwnIndex& own,bool mine,int kind,long long item,int jix,const std::vector<int>& pre,int rs,int rp,const std::array<uint64_t,8>& din,const std::vector<int32_t>& win,unsigned long long root,const std::unordered_map<std::string,unsigned long long>& pcs,std::string& err)->std::string{
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
        if(ftell(gXqSeg)==0){ fprintf(gXqSeg,"#R3XQ 1 fp=%016llx compat=%016llx run=%s pcert=%s\\n#lab %d",gFP,gCompat,xqName.c_str(),PCPATH,N); for(int l=0;l<N;l++) fprintf(gXqSeg," %d",vecOf[l]);
          fprintf(gXqSeg,"\\n#table %s\\n#kept %s\\n#typecut %d\\n",tabpath,LPKEPT,TYPECUT); if(PCLEAFX) fprintf(gXqSeg,"#leafx 1\\n"); if(XPS) fprintf(gXqSeg,"#cutx 1\\n");XPVARLINE if(PCWIT) fprintf(gXqSeg,"#pcwit 1\\n"); fprintf(gXqSeg,"#end\\n"); fflush(gXqSeg); }
        gXqSegOff=ftell(gXqSeg); }
      const long long off=gXqSegOff; const uint32_t h2[2]={0x49583352u,(uint32_t)hdr.size()}; const uint64_t n=recs.size();
      fwrite(h2,4,2,gXqSeg); fwrite(hdr.data(),1,hdr.size(),gXqSeg); fwrite(&n,8,1,gXqSeg); fwrite(recs.data(),1,recs.size(),gXqSeg); fwrite(raw,1,32,gXqSeg); fflush(gXqSeg);
      const long long len=8+(long long)hdr.size()+8+(long long)recs.size()+32; gXqSegOff+=len; gXqSegN++; gXqSegB+=len;
      if(mine){ if(own.fdw>=0){ fdatasync(fileno(gXqSeg)); own.punch(root); for(auto& kv:pcs) own.punch(kv.second); }   // a helper's pcert is scratch: punched once the segment is on disk
        own.drop(root); for(auto& kv:pcs) own.drop(kv.second); }
      return gXqSegPath+":"+std::to_string(off)+":"+std::to_string(len)+":"+hex; };
    auto segWrite=[&](int kind,long long item,int jix,const std::vector<int>& pre,int rs,int rp,const std::array<uint64_t,8>& din,const std::vector<int32_t>& win,unsigned long long root,const std::unordered_map<std::string,unsigned long long>& pcs,std::string& err)->std::string{
      return segWriteFrom(gOwn,true,kind,item,jix,pre,rs,rp,din,win,root,pcs,err); };
    // prof7R3q fast spill: a spill (SIGTERM: a preemption leaves ~30 s) reports the units finished but not yet assembled and the spilled units at once,
    // with seg=pending; their segments follow as "SG RUN:C seg=REF" (C = the report's number). <pcert>.pend lists them (assembly data), so that a
    // later launch on this host (--xqrecover DIR) assembles from this pcert whatever this one could not.
    FinJob finCur; bool finCurOn=false;   // the job the finalizer is assembling (under finmu)
    std::mutex pendmu; std::unordered_map<long long,std::string> pendRep;   // item -> key of its pending report: the finalizer sends SG instead of R
    std::map<std::string,std::string> sgPend;   // key -> SG line until the queue answers (resent after a reconnect)
    auto sgLost=[](const std::string& key,const std::string& why){ std::string w=why.substr(0,120); for(char& ch:w) if(ch==' '||ch=='\\n'||ch=='\\t') ch='_'; return "SGL "+key+" "+(w.empty()?std::string("-"):w); };   // SGL: this host cannot produce the segment of a pending report
    auto pendLine=[&](const std::string& key,int kind,long long item,int job,const std::vector<int>& pre,int rs,int rp,const std::array<uint64_t,8>& din,const std::vector<int32_t>& win,unsigned long long root,const std::unordered_map<std::string,unsigned long long>& pcs)->std::string{
      std::string t="P "+key+" "+std::to_string(kind)+" "+std::to_string(item)+" "+std::to_string(job)+" "+std::to_string(pre.size()); for(int l:pre) t+=" "+std::to_string(l);
      t+=" "+std::to_string(rs)+" "+std::to_string(rp)+" "+dhex(din)+" "+(PCWIT?whex(win):std::string("-"))+" "+std::to_string(root)+" "+std::to_string(pcs.size());   // pend 2: the witness after the mask
      static const char* HX="0123456789abcdef"; for(auto& kv:pcs){ t+=' '; for(unsigned char ch:kv.first){ t+=HX[ch>>4]; t+=HX[ch&15]; } t+=":"+std::to_string(kv.second); }
      return t+"\\n"; };
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
          if(!gok){ try{ G.open_(opc); V.fromPFile(G); gok=true; } catch(const std::exception& e){ fprintf(stderr,"R3q: recover %s: cannot read %s: %s\\n",path.c_str(),opc.c_str(),e.what()); gerr=e.what(); gok=true; } }
          if(!gerr.empty()){ nbad++; std::lock_guard<std::mutex> lk(pendmu); sgPend[key]=sgLost(key,"pcert_unreadable:"+gerr); continue; }   // every segment of an unreadable pcert is lost
          std::string err; const std::string ref=segWriteFrom(V,false,kind,item,job,pre,rs,rp,din,win,root,pcs,err);
          if(ref.empty()){ nbad++; fprintf(stderr,"R3q: recover %s: segment %s not assembled: %s (declared lost: the queue re-runs the item)\\n",path.c_str(),key.c_str(),err.c_str()); std::lock_guard<std::mutex> lk(pendmu); sgPend[key]=sgLost(key,err); continue; }
          xqSegSync(); { FILE* f=fopen(path.c_str(),"a"); if(f){ fprintf(f,"D %s seg=%s\\n",key.c_str(),ref.c_str()); fclose(f); } }
          { std::lock_guard<std::mutex> lk(pendmu); sgPend[key]="SG "+key+" seg="+ref; } nas++; }
        fprintf(stderr,"R3q: recover %s (pcert %s, %lld punched or damaged blocks skipped): %d segments assembled, %d sent again, %d declared lost\\n",path.c_str(),opc.c_str(),G.nskip,nas,nre,nbad);
        recFiles.push_back({path,{opc,keys}}); } }
    auto recCheck=[&](){ for(auto it=recFiles.begin();it!=recFiles.end();){ bool open_=false; { std::lock_guard<std::mutex> lk(pendmu); for(auto& k:it->second.second) if(sgPend.count(k)){ open_=true; break; } }
        if(open_){ ++it; continue; } rename(it->first.c_str(),(it->first+".done").c_str()); if(!it->second.first.empty()) unlink(it->second.first.c_str());
        fprintf(stderr,"R3q: recovered %s: every segment answered; its pcert deleted\\n",it->first.c_str()); it=recFiles.erase(it); } };
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
        std::string err, ref; if(PCF){ ref=segWrite(f.kind,f.item,f.job,f.pre,f.rs,f.rp,f.din,f.win,f.root,f.pcs,err); if(ref.empty()){ gXqAsmErr++; fprintf(stderr,"R3q: segment of item %lld (unit %d) not assembled: %s\\n",f.item,f.u,err.c_str()); ref="ERR"; } }
        std::string pk; { std::lock_guard<std::mutex> lk(pendmu); auto it=pendRep.find(f.item); if(it!=pendRep.end()){ pk=it->second; pendRep.erase(it); } }
        if(!pk.empty()){ std::string sl; if(ref!="ERR"){ xqSegSync(); sl="SG "+pk+" seg="+ref; } else sl=sgLost(pk,err); { std::lock_guard<std::mutex> lk(pendmu); sgPend[pk]=sl; } xsend(sl); }   // reported at a spill: its segment (or SGL: the queue re-runs the item)
        else if(f.split){ long long c=++xcseq; std::string line="SP "+std::to_string(c)+" "+f.spRef+" "+std::to_string(f.n)+" "+std::to_string(f.l)+" "+std::to_string(f.p)+" "+std::to_string(f.nexp);   // --xqcap
          if(PCF) line+=" seg="+ref; line+=" skh="+std::to_string(f.skh)+f.spKids; { std::lock_guard<std::mutex> lk(gJmu); gRpend.push_back(line); } }
        else { long long c=++xcseq; char b[256]; snprintf(b,sizeof b,"R %lld %lld %lld %lld %lld %d",c,f.item,f.n,f.l,f.p,f.nexp); std::string line=b; if(PCF) line+=" seg="+ref; line+=" skh="+std::to_string(f.skh)+" rsh="+std::to_string(f.rsh);
          { std::lock_guard<std::mutex> lk(gXmu); gXrepIx[c]=f.jix; } { std::lock_guard<std::mutex> lk(gJmu); gRpend.push_back(line); } }
        { std::lock_guard<std::mutex> lk(finmu); finCurOn=false; } finBusy--; } });
    auto finDrain=[&](){ for(int w=0;w<36000;w++){ bool idle; { std::lock_guard<std::mutex> lk(finmu); idle=finq.empty() && finBusy.load()==0; } if(idle) return; std::this_thread::sleep_for(std::chrono::milliseconds(10)); } };''')
rep('''        if(!U.tracked){ writeState(u); return; }   // prof7L87's state line
        if(jab[u].load()){ xsend("UL "+std::to_string(U.item)); nAborted++; return; }   // abandoned after an accepted export: the server re-queues the job root''',
    '''        if(!U.tracked){ writeState(u); dropOwn(U); return; }   // prof7L87's state line (prof7R3q: its stream is R3's job stream, r3cat assembles it)
        if(jab[u].load()){ xsend("UL "+std::to_string(U.item)); nAborted++; dropOwn(U); return; }   // abandoned after an accepted export: the server re-queues the job root''')
rep('''      if(!jab[u].load()){ xqReport(u,U.item,-1); nXimpDone++; }
      freeSlot(u); };''','''      if(!jab[u].load()){ xqReport(u,U.item,-1); nXimpDone++; }
      freeSlot(u); };''')
# runPiece: segments (R3) and imported roots (kind 0 / 1 / 3)
rep('''        const long long pv0=s.visited, pl0=s.myLeaf, pp0=s.myProf, pd0=s.donN, pi0=s.nIntr;   // prof7L84
        s.resetLists(); s.jobBase=*s.doneP;
        if(job.rs>=0){ const int d0=(int)job.seq.size(); s.rngD=d0; s.rngL=job.rs; s.dfs2(job.seq.back(),R-d0,job.w,d0); s.rngD=-1; }   // prof7L92: a range item (the node itself is not counted)
        else s.dfs(job.seq.back(),R-(int)job.seq.size(),job.w);
        s.unreplay(job.seq); certFlush(); s.xu=nullptr;''',
    '''        const long long pv0=s.visited, pl0=s.myLeaf, pp0=s.myProf, pd0=s.donN, pi0=s.nIntr;   // prof7L84
        if(PCF){ const int jx=imp?gU[ix].ix:ix;   // prof7R3q: the segment of an imported root (kind 1 piece, 0 job root, 3 range) or of a local piece (kind 1, R3)
          if(job.root){ const int kd=gU[ix].kind=='P'?1:(gU[ix].kind=='J'?0:3); if(kd==3) s.pcBeginQ(jx,3,job.seq,job.dinh,gU[ix].rs,gU[ix].rp,&job.win); else s.pcBegin(jx,kd,job.seq,job.dinh,&job.win); }
          else s.pcBegin(jx,1,job.seq,job.dinh,&job.win);   // batch 12: the piece's witness rows
          { std::lock_guard<std::mutex> lk(rm); if(job.root) gU[ix].rootSeg=tlPc.id; else gU[ix].pcs[pkey(job.seq)]=tlPc.id; } }
        s.resetLists(); s.jobBase=*s.doneP;
        if(job.rs>=0){ const int d0=(int)job.seq.size(); s.rngD=d0; s.rngL=job.rs; s.rngP=gU[ix].rp; s.rngSeen=0; s.dfs2(job.seq.back(),R-d0,job.w,d0); s.rngD=-1; s.rngP=-1; }   // prof7L92: a range item (the node itself is not counted)
        else s.dfs(job.seq.back(),R-(int)job.seq.size(),job.w);
        s.unreplay(job.seq); certFlush(); if(PCF) pcChunk(true); s.xu=nullptr;''')
rep('''          for(int l2:job.seq){ snprintf(b,sizeof b," %d",vecOf[l2]); t+=b; } t+='\\n'; std::lock_guard<std::mutex> lk(gJmu); gJpend.push_back(std::move(t)); }''',
    '''          for(int l2:job.seq){ snprintf(b,sizeof b," %d",vecOf[l2]); t+=b; } if(PCF){ snprintf(b,sizeof b," %llu",tlPc.id); t+=b; } t+='\\n'; std::lock_guard<std::mutex> lk(gJmu); gJpend.push_back(std::move(t)); }   // prof7R3: segment of the piece''')
# list jobs: replay-cut segment, the job's root segment
rep('''            s.unreplay(job); gReplayCut++;   // prof7L39: the prefix breaks a capacity of this table: no profiles below it''',
    '''            if(PCF){ pcOpen(ix,2,job,nullptr); std::string& B=tlPc.buf; pcU8(B,0x03); pcU8(B,11); pcU8(B,(unsigned)(s.rp.size()-1)); pcU8(B,(unsigned)s.addWhy);   // prof7R3: replay cut segment
              if(s.addWhy==1 || s.addWhy==2){ pcU8(B,(unsigned)s.addDim); for(int j=0;j<s.addDim;j++) pcU16(B,s.addRows[j]); } else pcU8(B,(unsigned)s.addW); pcChunk(true); }
            s.unreplay(job); gReplayCut++;   // prof7L39: the prefix breaks a capacity of this table: no profiles below it''')
rep('''          s.resetLists(); s.jobBase=*s.doneP; s.dfs(job.back(),R-(int)job.size(),1.0); s.unreplay(job); certFlush();''',
    '''          s.pcBegin(ix,0,job,std::array<uint64_t,8>{});   // prof7R3: the job's root segment
          if(PCF){ std::lock_guard<std::mutex> lk(rm); gU[ix].rootSeg=tlPc.id; }   // prof7R3q
          s.resetLists(); s.jobBase=*s.doneP; s.dfs(job.back(),R-(int)job.size(),1.0); s.unreplay(job); certFlush(); if(PCF) pcChunk(true);''')
# worker end: prof7R3's Farkas statistics
i=R.index('      { std::lock_guard<std::mutex> lk(fkmu); const fkx::Stats& a=s.fk.st;'); j=R.index('\n',i); FKLINE=R[i:j]
if FKLINE.rstrip().endswith('} };'): FKLINE=FKLINE.rstrip()[:-3]   # R3's line also closes its worker lambda
rep('''      totv+=s.visited&1023; s.flush(); certFlush();
''','''      totv+=s.visited&1023; s.flush(); certFlush();
'''+FKLINE+'\n')
# import: the dead mask and the delta base travel with the item
rep('''          if(tag=="I"){   // I id kind ix rsvec d v1..vd [| d v1..vd]... : an item leased to this run
            long long id; std::string kind; int jx, rsv, d; ss>>id>>kind>>jx>>rsv>>d; std::vector<int> seq; bool ok=(bool)ss && d>=1 && d<=R;
            for(int i=0;i<d && ok;i++){ int v; if(!(ss>>v) || v<1 || v>511 || labOf[v]<0) ok=false; else seq.push_back(labOf[v]); }
            std::vector<std::string> sks; unsigned long long skm=0; std::string bar;
            while(ok && (ss>>bar)){ if(bar!="|"){ ok=false; break; }''',
    '''          if(tag=="I"){   // I id kind ix rsvec d v1..vd [dinh=HEX] [win=HEX] [p=VEC] [| d v1..vd]... : an item leased to this run
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
                ss.clear(); ss.seekg(sp0); }''')
rep('''            if(!ok || kind.size()!=1 || (kind[0]!='P' && kind[0]!='Q' && kind[0]!='J') || (kind[0]=='Q' && (rsv<1 || rsv>511 || labOf[rsv]<0))){''',
    '''            if(ok && kind.size()==1 && kind[0]=='Q' && PCF && rpl<0) ok=false;   // prof7R3q: a range needs its delta base
            if(ok && kind.size()==1 && (kind[0]=='P' || kind[0]=='Q') && PCF && PCWIT && !hw) ok=false;   // batch 12: and a piece or range its witness
            if(!ok || kind.size()!=1 || (kind[0]!='P' && kind[0]!='Q' && kind[0]!='J') || (kind[0]=='Q' && (rsv<1 || rsv>511 || labOf[rsv]<0))){''')
rep('''              if(u>=0){ XUnit& U=gU[u]; U.kind=kind[0]; U.item=id; U.ix=jx; U.seq=seq; U.rs=(kind[0]=='Q')?labOf[rsv]:-1; U.active=true;''',
    '''              if(u>=0){ XUnit& U=gU[u]; U.kind=kind[0]; U.item=id; U.ix=jx; U.seq=seq; U.rs=(kind[0]=='Q')?labOf[rsv]:-1; U.rp=rpl; U.din=din; U.win=win; U.rootSeg=0; U.pcs.clear(); U.active=true;''')
rep('''            { std::lock_guard<std::mutex> lq(qmu); Job j; j.seq=seq; j.w=0.0; j.ix=u; j.rs=gU[u].rs; j.root=true; Q.push_back(std::move(j)); qsizeA++; } qcv.notify_one(); return; }''',
    '''            { std::lock_guard<std::mutex> lq(qmu); Job j; j.seq=seq; j.w=0.0; j.ix=u; j.rs=gU[u].rs; j.root=true; j.dinh=din; j.win=win; Q.push_back(std::move(j)); qsizeA++; } qcv.notify_one(); return; }''')
# RA / RN: no longer held
rep('''          if(tag=="RA"||tag=="RN"){ long long c; ss>>c; int jix=-2; { std::lock_guard<std::mutex> lk(gXmu); auto it=gXrep.find(c); if(it!=gXrep.end()) gXrep.erase(it); auto i2=gXrepIx.find(c); if(i2!=gXrepIx.end()){ jix=i2->second; gXrepIx.erase(i2); } }''',
    '''          if(tag=="SGA"||tag=="SGN"){ std::string k; ss>>k; { std::lock_guard<std::mutex> lk(pendmu); sgPend.erase(k); } if(tag=="SGN") fprintf(stderr,"R3q: segment for %s refused: %s\\n",k.c_str(),line.c_str()); return; }   // prof7R3q (also the answers to SGL)
          if(tag=="RA"||tag=="RN"){ long long c; ss>>c; int jix=-2; long long rid=0; { std::lock_guard<std::mutex> lk(gXmu); auto it=gXrep.find(c); if(it!=gXrep.end()){ long long c2=0; sscanf(it->second.c_str(),"R %lld %lld",&c2,&rid); gXrep.erase(it); } auto i2=gXrepIx.find(c); if(i2!=gXrepIx.end()){ jix=i2->second; gXrepIx.erase(i2); } }
            if(rid>0){ std::lock_guard<std::mutex> lk(heldmu); xheld.erase(rid); }''')
# exports carry the dead mask (both the live hand-off and the resend after a reconnect)
rep('''              for(auto& pj:outp){ long long c=++xcseq; std::string line; { std::lock_guard<std::mutex> lk(rm); line="X "+std::to_string(c)+" "+parentRef(pj.first)+" P "+vecs(pj.second.seq); }''',
    '''              for(auto& pj:outp){ long long c=++xcseq; std::string line; { std::lock_guard<std::mutex> lk(rm); line="X "+std::to_string(c)+" "+parentRef(pj.first)+" P "+vecs(pj.second.seq)+" dinh="+dhex(pj.second.dinh)+(PCWIT?" win="+whex(pj.second.win):std::string()); }''')
rep('''            { std::lock_guard<std::mutex> lk(xmu); for(auto& kv:xpend){ int u=kv.second.first; t+="X "+std::to_string(kv.first)+" "+parentRef(u)+" P "+vecs(kv.second.second.seq)+"\\n"; } for(auto& kv:xspl) t+=kv.second+"\\n"; }''',
    '''            { std::lock_guard<std::mutex> lk(xmu); for(auto& kv:xpend){ int u=kv.second.first; t+="X "+std::to_string(kv.first)+" "+parentRef(u)+" P "+vecs(kv.second.second.seq)+" dinh="+dhex(kv.second.second.dinh)+(PCWIT?" win="+whex(kv.second.second.win):std::string())+"\\n"; } for(auto& kv:xspl) t+=kv.second+"\\n"; }''')
rep('''            { std::string h="HOLD"; std::lock_guard<std::mutex> lk(rm); for(auto& kv:itemSlot) h+=" "+std::to_string(kv.first); for(size_t u=0;u<NF;u++) if(gU[u].tracked && gU[u].item) h+=" "+std::to_string(gU[u].item); t+=h+"\\n"; }''',
    '''            { std::string h="HOLD"; { std::lock_guard<std::mutex> lk(rm); for(auto& kv:itemSlot) h+=" "+std::to_string(kv.first); for(size_t u=0;u<NF;u++) if(gU[u].tracked && gU[u].item) h+=" "+std::to_string(gU[u].item); }
              { std::lock_guard<std::mutex> lk(heldmu); for(long long id:xheld) h+=" "+std::to_string(id); } t+=h+"\\n"; }   // prof7R3q: and the items whose report is under way
            { std::lock_guard<std::mutex> lk(pendmu); for(auto& kv:sgPend) t+=kv.second+"\\n"; }   // prof7R3q: segments of pending reports''')
# SIGTERM: certificate and stream first (prof7R2 / prof7R3), item segments too
rep('''          if(OUT){ fflush(OUT); fdatasync(fileno(OUT)); } if(XOUT){ fflush(XOUT); fdatasync(fileno(XOUT)); } jwrite(J,S,SF);''',
    '''          if(OUT){ fflush(OUT); fdatasync(fileno(OUT)); } if(XOUT){ fflush(XOUT); fdatasync(fileno(XOUT)); } { std::lock_guard<std::mutex> lc(certmu); if(CERTF){ fflush(CERTF); fdatasync(fileno(CERTF)); } } { std::lock_guard<std::mutex> lp2(pcmu); if(PCF){ fflush(PCF); fdatasync(fileno(PCF)); } } jwrite(J,S,SF);   // prof7R2: certificate first (prof7R3: and the pcert stream)''')
# spill: kids carry their dead masks / delta bases; each spilled unit's own part becomes an item segment
rep('''      if(XQADDR){ for(int w=0;w<100 && xpendN.load()>0 && xconn.load();w++) std::this_thread::sleep_for(std::chrono::milliseconds(50)); }   // let pending exports resolve (5 s)''',
    '''      if(XQADDR){ for(int w=0;w<100 && xpendN.load()>0 && xconn.load();w++) std::this_thread::sleep_for(std::chrono::milliseconds(50)); }   // let pending exports resolve (5 s)
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
        if(curOn){ const std::string k=pendReport(cur); std::lock_guard<std::mutex> lk(pendmu); pendRep[cur.item]=k; } }   // the finalizer sends its SG''')
rep('''      for(auto& r:recs){ std::vector<int> ss2=r.seq; kids[r.u].push_back("Q "+vecs(ss2)+" "+std::to_string(vecOf[r.l])); nR++; }
      for(auto& j:rest){ if(j.root){ giveBack.push_back(gU[j.ix].item); continue; } kids[j.ix].push_back("P "+vecs(j.seq)); nP++; }
      { std::lock_guard<std::mutex> lk(xmu); for(auto& kv:xpend){ kids[kv.second.first].push_back("K "+xqName+":"+std::to_string(kv.first)+" P "+vecs(kv.second.second.seq)); nK++; } }   // unresolved exports: the server keeps the copy it already has''',
    '''      std::set<int> rgBack;   // prof7R3q: a regeneration in progress is returned (the queue re-leases it), never spilled
      for(auto& r:recs){ if(gU[r.u].regen){ rgBack.insert(r.u); continue; } std::vector<int> ss2=r.seq; std::string q="Q "+vecs(ss2)+" "+std::to_string(vecOf[r.l]); if(PCF) q+=" p="+std::to_string(vecOf[r.p])+" dinh="+dhex(r.D); if(PCF && PCWIT) q+=" win="+whex(r.win); kids[r.u].push_back(q); nR++; }
      for(auto& j:rest){ if(j.root){ giveBack.push_back(gU[j.ix].item); continue; } if(gU[j.ix].regen){ rgBack.insert(j.ix); continue; } std::string q="P "+vecs(j.seq); if(PCF) q+=" dinh="+dhex(j.dinh); if(PCF && PCWIT) q+=" win="+whex(j.win); kids[j.ix].push_back(q); nP++; }
      for(int u:rgBack){ giveBack.push_back(gU[u].item); kids.erase(u); }
      for(int u:splitU) if(!kids.count(u) && !jab[u].load()) kids[u];   // --xqcap: a split unit with nothing left reports its own part
      for(size_t u=NF;u<gNU;u++) if(gU[u].rgive && gU[u].item && !rgBack.count((int)u)){ giveBack.push_back(gU[u].item); kids.erase((int)u); }   // ranges stopped before their first child
      { std::lock_guard<std::mutex> lk(xmu); for(auto& kv:xpend){ std::string q="K "+xqName+":"+std::to_string(kv.first)+" P "+vecs(kv.second.second.seq); if(PCF) q+=" dinh="+dhex(kv.second.second.dinh); if(PCF && PCWIT) q+=" win="+whex(kv.second.second.win); kids[kv.second.first].push_back(q); nK++; } }   // unresolved exports: the server keeps the copy it already has''')
rep('''        for(auto& kv:kids){ int u=kv.first; if(jab[u].load()) continue; long long c=++xcseq;
          std::string m="SP "+std::to_string(c)+" "+parentRef(u)+" "+std::to_string(jnodes[u])+" "+std::to_string(jlv[u])+" "+std::to_string(jpf[u])+" "+std::to_string(gU[u].nexp);
          for(auto& k2:kv.second) m+=" | "+k2; msgs.push_back({c,m}); }''',
    '''        for(auto& kv:kids){ int u=kv.first; if(jab[u].load()) continue; long long c=++xcseq;
          std::string m="SP "+std::to_string(c)+" "+parentRef(u)+" "+std::to_string(jnodes[u])+" "+std::to_string(jlv[u])+" "+std::to_string(jpf[u])+" "+std::to_string(gU[u].nexp);
          if(PCF){ XUnit& U=gU[u]; std::string err, ref;   // prof7R3q: the unit's canonical own part (with its RNG references) as an item segment
            FinJob f; f.u=u; f.item=U.item; f.jix=-1; f.skh=0; f.rsh=0; f.root=U.rootSeg; f.pcs.swap(U.pcs); U.rootSeg=0; f.n=f.l=f.p=0; f.nexp=0;   // fast spill: assembled after the reports
            if((size_t)u<NF){ f.kind=0; f.job=u; f.pre=frontier[u]; f.rs=-1; f.rp=-1; f.din={}; } else { f.kind=U.kind=='P'?1:(U.kind=='J'?0:3); f.job=U.ix; f.pre=U.seq; f.rs=U.rs; f.rp=U.rp; f.din=U.din; f.win=U.win; }
            const std::string key=xqName+":"+std::to_string(c); pendText+=pendLine(key,f.kind,f.item,f.job,f.pre,f.rs,f.rp,f.din,f.win,f.root,f.pcs); pendJobs.push_back({key,std::move(f)}); m+=" seg=pending"; }
          m+=" skh="+std::to_string(gU[u].skHit.load());
          for(auto& k2:kv.second) m+=" | "+k2; msgs.push_back({c,m}); }''')
# normal exit: the finalizer drains before the last commit; stop it at the end; then prof7R3's stream close and statistics
rep('''    finF=true; mon.join(); jth.join(); jcommit(); report(true);''','''    finDrain();   // prof7R3q: every finished unit's segment written and its report queued
    finF=true; mon.join(); jth.join(); jcommit(); report(true);''')
rep('''      if(gJF){ jcommit(); }   // H lines of the last acks
      xstop=true; xth.join(); if(XOUT){ fflush(XOUT); fclose(XOUT); XOUT=nullptr; gXOUTsync=nullptr; } }''',
    '''      if(gJF){ jcommit(); }   // H lines of the last acks
      xstop=true; xth.join(); if(XOUT){ fflush(XOUT); fclose(XOUT); XOUT=nullptr; gXOUTsync=nullptr; } }
    { std::lock_guard<std::mutex> lk(finmu); finStop=true; } fincv.notify_all(); finth.join();
    if(gXqSeg){ std::lock_guard<std::mutex> lk(gXqSegMu); fflush(gXqSeg); fdatasync(fileno(gXqSeg)); fclose(gXqSeg); gXqSeg=nullptr; }
    if(PCF || gXqSegN.load()) fprintf(stderr,"R3q: item segments %lld (%lld bytes) in %s, assembly failures %lld, pcert bytes freed %lld\\n",(long long)gXqSegN,(long long)gXqSegB,gXqSegPath.c_str(),(long long)gXqAsmErr,gOwn.punched);
    if(XQCAP>0 || XQCAPB>0) fprintf(stderr,"R3q: item-size cap %lld nodes / %.0f MB (split depth <= %d): %lld units reached it, %lld split reports, %lld accepted\\n",XQCAP,XQCAPB/1e6,XQCAPD,(long long)gXsplit,(long long)nXsplitDone,(long long)nXsplitAck);''')
i=R.index('    if(PCF){ fflush(PCF); fdatasync(fileno(PCF)); fclose(PCF); PCF=nullptr;   // prof7R3'); j=R.index('    if(gJF || gJdmask || gJrmask)',i); R3STATS=R[i:j]
rep('''    if(gJF || gJdmask || gJrmask) fprintf(stderr,"L84: journal records''',R3STATS+'''    if(gJF || gJdmask || gJrmask) fprintf(stderr,"L84: journal records''')
# --xqcap: a split unit's queued pieces become P items (never run here); its range records are collected when each piece ends
rep('''      auto runPiece=[&](Job& job){ int ix=job.ix; s.curJob=ix; const bool imp=(size_t)ix>=NF;''','''      auto runPiece=[&](Job& job){ int ix=job.ix; s.curJob=ix; const bool imp=(size_t)ix>=NF;
        tlXU=nullptr;
        if(imp && !job.root && (XQCAP>0 || XQCAPB>0) && gU[ix].split.load()){ { std::lock_guard<std::mutex> lk(rm); gU[ix].spieces.push_back(std::move(job)); --outst[ix]; if(outst[ix]==0 && rootDone[ix]) unitDone(ix); }   // prof7R3q --xqcap
          { std::lock_guard<std::mutex> lq(qmu); activeP--; checkFin(); } return; }
        if(imp) tlXU=&gU[ix];   // --xqcapb
       ''')
rep('''          jnodes[ix]+=dn; jlv[ix]+=s.myLeaf-lv0; jpf[ix]+=s.myProf-pf0; if(job.root) rootDone[ix]=1; else --outst[ix];''','''          jnodes[ix]+=dn; jlv[ix]+=s.myLeaf-lv0; jpf[ix]+=s.myProf-pf0; if(job.root) rootDone[ix]=1; else --outst[ix];
          if(!s.sp.empty() && !gSpill.load()){ for(auto& r:s.sp) gU[r.u].srecs.push_back(std::move(r)); s.sp.clear(); }   // prof7R3q --xqcap: a split's range records (a spill collects them at the end instead)
          tlXU=nullptr;''')
rep('''      XUnit& U=gU[u];
      if(U.intr.load()) return;   // interrupted by a spill: the spill writes it out''','''      XUnit& U=gU[u];
      if(U.split.load()){ if(gSpill.load()) return; if(!jab[u].load()) splitDone(u); freeSlot(u); return; }   // prof7R3q --xqcap: one SP for the split unit (under a spill, the spill writes it out)
      if(U.intr.load()) return;   // interrupted by a spill: the spill writes it out''')
rep('''          if(tag=="SPA"||tag=="SPN"){ long long c; ss>>c; std::string rest; std::getline(ss,rest); std::lock_guard<std::mutex> lk(xmu); xspl.erase(c); xsplRes[c]=tag+rest; return; }''',
    '''          if(tag=="SPA"||tag=="SPN"){ long long c; ss>>c; std::string rest; std::getline(ss,rest);
            { std::string sl; { std::lock_guard<std::mutex> lk(gXmu); auto it=gXrep.find(c); if(it!=gXrep.end()){ sl=it->second; gXrep.erase(it); } }   // prof7R3q --xqcap: the answer to a split's SP
              if(!sl.empty()){ long long iid=0; char rt[8]={0}; sscanf(sl.c_str(),"SP %*s %7s %lld",rt,&iid); if(iid>0){ std::lock_guard<std::mutex> lk(heldmu); xheld.erase(iid); }
                if(tag=="SPN"){ fprintf(stderr,"R3q: split report of item %lld refused (%s): item returned to the queue\\n",iid,rest.c_str()); if(iid>0) xsend("UL "+std::to_string(iid)); } else nXsplitAck++; return; } }
            std::lock_guard<std::mutex> lk(xmu); xspl.erase(c); xsplRes[c]=tag+rest; return; }''')
rep('''      std::deque<Job> rest; { std::lock_guard<std::mutex> lq(qmu); rest.swap(Q); qsizeA=0; }''','''      std::deque<Job> rest; { std::lock_guard<std::mutex> lq(qmu); rest.swap(Q); qsizeA=0; }
      std::vector<int> splitU; { std::lock_guard<std::mutex> lk(rm); for(size_t u=NF;u<gNU;u++) if(gU[u].active && gU[u].split.load()){ for(auto& r:gU[u].srecs) recs.push_back(std::move(r)); gU[u].srecs.clear();   // prof7R3q --xqcap: split units not yet reported
        for(auto& j:gU[u].spieces) rest.push_back(std::move(j)); gU[u].spieces.clear(); splitU.push_back((int)u); } }''')
rep('''          const auto& job=frontier[ix]; s.curJob=ix; s.xu=nullptr;''','''          const auto& job=frontier[ix]; s.curJob=ix; s.xu=nullptr; tlXU=nullptr;   // prof7R3q --xqcapb: list jobs are not capped''')
s=s.replace('"L92 DONE: exported','"R3q DONE: exported').replace('"L92: ','"R3q: ')
s=s.replace('XPVARLINE',' if(XPVAR) fprintf(gXqSeg,"#xpvar 1\\n");' if 'static bool XPVAR' in R else '')   # batch 11: varint bulk-peel blobs (header flag, as in the pcert)
open(outf,'w').write(s); print('wrote',outf)
