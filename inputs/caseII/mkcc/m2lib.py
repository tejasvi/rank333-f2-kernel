# m2lib.py: helpers for the math2 stream (subspaces of A = F2^{3x3}, bit 3i+j = a[i][j]; table lookups; the group G).
import numpy as np, itertools, os
W=os.environ.get('M2_WORK', '.')
BASE=lambda f: os.path.join(os.environ.get('MKCC_BASE', '.'), f)   # MKCC_BASE: the base tables' directory
def vec2mat(v): return np.array([(v>>k)&1 for k in range(9)],dtype=np.uint8).reshape(3,3)
def mat2vec(M): return int(sum(int(M.flat[k]&1)<<k for k in range(9)))
def rank_bits(rows):
    bas={}; r=0
    for v in rows:
        while v:
            h=v.bit_length()-1
            if h not in bas: bas[h]=v; r+=1; break
            v^=bas[h]
    return r
def rk3(a): return rank_bits([(a>>(3*i))&7 for i in range(3)])
RK=[rk3(a) for a in range(512)]
def span(basis):
    s={0}
    for b in basis: s|={x^b for x in s}
    return s
def reduce_basis(vs):
    # returns an echelon basis (list) of span(vs)
    bas={}
    for v in vs:
        while v:
            h=v.bit_length()-1
            if h not in bas: bas[h]=v; break
            v^=bas[h]
    return list(bas.values())
def rref_key(vs):
    rows=reduce_basis(vs); k=len(rows)
    rows=list(rows)
    # full RREF with pivots descending, as table.py: process bits 8..0
    r=0
    for bit in range(8,-1,-1):
        piv=-1
        for i in range(r,k):
            if (rows[i]>>bit)&1: piv=i; break
        if piv<0: continue
        rows[r],rows[piv]=rows[piv],rows[r]
        for i in range(k):
            if i!=r and (rows[i]>>bit)&1: rows[i]^=rows[r]
        r+=1
    key=0
    for i in range(k): key|=rows[i]<<(9*i)
    return key,k
class Table:
    def __init__(self,tab=None):
        tab=tab or BASE('tab_C3eD.bin')
        t=np.fromfile(tab,dtype=np.uint8).reshape(-1,24)
        hi=t[:,0:8].copy().view(np.uint64).ravel(); lo=t[:,8:16].copy().view(np.uint64).ravel()
        self.lb=t[:,16].astype(np.int8); self.k=t[:,17].astype(np.int8)
        d=np.load(os.environ.get('M2_ORB_NPZ', BASE('mm3_table.npz'))); self.orb=d['orb']
        keys=hi.astype(object)*0  # placeholder
        # combined 128-bit key as python ints would be slow; sort by (hi,lo) with lexsort
        self.order=np.lexsort((lo,hi)); self.hi=hi[self.order]; self.lo=lo[self.order]
    def find(self,vs):
        key,k=rref_key(vs)
        h=np.uint64(key>>64); l=np.uint64(key&((1<<64)-1))
        i=np.searchsorted(self.hi,h,side='left'); j=np.searchsorted(self.hi,h,side='right')
        if i==j: return None
        p=i+np.searchsorted(self.lo[i:j],l)
        if p<j and self.lo[p]==l: return int(self.order[p])
        return None
    def info(self,vs):
        p=self.find(vs)
        if p is None: return None
        return int(self.orb[p]),int(self.lb[p]),int(self.k[p])
def gl3():
    out=[]
    for bits in range(512):
        M=vec2mat(bits).astype(np.int64)
        d=int(round(np.linalg.det(M)))%2
        if d: out.append(M)
    return out
_G=None
def group():
    # 56448 x 512 uint16: g = (t*168+p)*168+q : a -> P a Q (t=0) or P a^T Q (t=1)
    global _G
    if _G is not None: return _G
    fn=os.environ.get('M2_IMG_NPY', 'm2_img.npy')   # a cache
    if os.path.exists(fn): _G=np.load(fn); return _G
    G=gl3(); Ms=np.array([vec2mat(v) for v in range(512)],dtype=np.int64); Gs=np.array(G,dtype=np.int64)
    img=np.zeros((2*168*168,512),dtype=np.uint16); idx=0; pw=(1<<np.arange(9))
    for t in range(2):
        base=Ms if t==0 else Ms.transpose(0,2,1)
        for p in range(168):
            PB=np.einsum('ab,vbc->vac',Gs[p],base)
            R=np.einsum('vac,qcd->qvad',PB,Gs)%2
            img[idx:idx+168]=(R.reshape(168,512,9)*pw).sum(2)
            idx+=168
    np.save(fn,img); _G=img; return img
def T333():
    T=np.zeros((9,9,9),dtype=np.uint8)
    for i in range(3):
        for j in range(3):
            for k in range(3): T[3*i+j,3*j+k,3*k+i]=1
    return T
def class_subspaces(T,c):
    # list of (index, basis list, point set as python int bitmask over 512) for all table subspaces of class c
    idx=np.nonzero(T.orb==c)[0]
    t=np.fromfile(BASE('tab_C3eD.bin'),dtype=np.uint8).reshape(-1,24)
    out=[]
    for i in idx:
        hi=int(t[i,0:8].copy().view(np.uint64)[0]); lo=int(t[i,8:16].copy().view(np.uint64)[0])
        key=(hi<<64)|lo; k=int(t[i,17])
        basis=[(key>>(9*j))&511 for j in range(k)]
        pts=span(basis); m=0
        for x in pts:
            if x: m|=1<<x
        out.append((int(i),basis,m))
    return out
def load_nodes(fn):
    out=[]
    for line in open(fn):
        t=line.split()
        if not t: continue
        out.append((float(t[0]),[int(x) for x in t[1:]]))
    return out
