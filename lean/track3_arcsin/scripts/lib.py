"""Exact finite-domain synthesis tools for the frozen stage-three slice tables."""
import contextlib
import io
import json
import re
import sys
from functools import reduce
from itertools import combinations
from operator import xor
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE.parents[1]))
with contextlib.redirect_stdout(io.StringIO()):
    import op102_sim as S

def xsum(items):
    return reduce(xor, items, 0)

def bits(n):
    while n:
        bit = n & -n
        yield bit.bit_length()-1
        n ^= bit

class Basis:
    def __init__(self, columns=()):
        self.piv = {}
        for i,v in enumerate(columns):
            self.add(v, 1<<i)

    def add(self, v, m):
        while v:
            k = v.bit_length()
            if k not in self.piv:
                self.piv[k]=(v,m)
                return True
            vv, mm=self.piv[k]
            v ^= vv
            m ^= mm
        return False

    def solve(self, v):
        m=0
        while v:
            t=self.piv.get(v.bit_length())
            if t is None: return None
            v ^= t[0]
            m ^= t[1]
        return m

def get_tree(name):
    out = [0]*100
    shift = 0
    for s in range(8):
        v=list(map(int,re.findall(r'\.leaf (\d+)',S.def_blocks[f'{name}_{s}'][1])))
        assert len(v)==128
        for w in range(25,100):
            out[w] |= v[w-25]<<shift
        shift += int(S.def_blocks[f'allM_{s}'][1]).bit_length()
    assert shift == 440
    return out

ALL=(1<<440)-1
ST2, ST3A, ST3B = [get_tree(n) for n in ('trS2c','trS3a','trS3b')]
ADDRESS = [41,42,43,44,45,46,47,48,58]
ALLOWED = [*range(41,49),*range(50,100)]

def simulate(w, ops, phase=0, allbits=ALL):
    for op in ops:
        k=op[0]
        if k=='cx':
            c,t=op[1:]; assert c!=t; w[t]^=w[c]
        elif k=='x': w[op[1]]^=allbits
        elif k=='z': phase ^=w[op[1]]
        elif k=='cz': phase ^=w[op[1]] & w[op[2]]
        elif k in ('and4t','unand'):
            a,b,t=op[1:]; assert len({a,b,t})==3
            if k=='and4t': assert w[t]==0; w[t]=w[a]&w[b]
            else: assert w[t]==(w[a]&w[b]); w[t]=0
        elif k=='unquad':
            qs,ls,t=op[1:]; assert t not in ls and all(t not in q for q in qs)
            assert w[t]==xsum([*(w[a]&w[b] for a,b in qs),*(w[a] for a in ls)])
            w[t]=0
        elif k=='hGadget':
            t,ps,ns,uc,uls=op[1:]
            assert not w[t] and len(ps)==len(ns)
            acc=par=0
            prev=b0=b1=b2=0
            for i,(const,ls) in enumerate([*ps,*ns]):
                assert all(0<=w1<100 and w1!=t for w1 in ls)
                acc^=(int(const)<<100)^xsum(1<<w1 for w1 in ls); par^=acc
                prev ^= (allbits if const else 0) ^ xsum(w[j] for j in ls)
                b0,b1,b2=(S.add1_par if i<len(ps) else S.add7_par)(b0,b1,b2,prev)
            assert all(0<=j<100 and j!=t for j in uls)
            assert not par and acc==((int(uc)<<100)^xsum(1<<j for j in uls)) and b0==0
            w[t]=b1; phase^=b2
        else: raise ValueError(op)
    return phase

def affine(w,t,mask):
    return [('x',t)]*int(bool(mask>>100))+[('cx',i,t) for i in bits(mask&((1<<100)-1))]

def quad_terms(w,allowed):
    ws=[i for i in allowed if w[i]]
    terms=[(),*((i,) for i in ws),*combinations(ws,2)]
    vals=[ALL,*(w[i] for i in ws),*(w[a]&w[b] for a,b in combinations(ws,2))]
    return terms,Basis(vals)

def correct(w,phase,allowed=ALLOWED):
    if not phase: return []
    terms,b=quad_terms(w,allowed)
    sol=b.solve(phase)
    assert sol is not None
    ops=[]
    for i in bits(sol):
        t=terms[i]
        if len(t)==0:
            z=allowed[0]
            ops += [('x',z),('z',z),('x',z),('z',z)]
        else: ops.append(('z' if len(t)==1 else 'cz',*t))
    return ops

def emit_gadget(target,pairs):
    if not pairs: return []
    pos=[0]; neg=[]; suffix=xsum(p[0] for p in pairs); total=suffix
    for u,v in pairs:
        pos.append(v^suffix); suffix^=u; neg.append(v^suffix)
    neg.append(total)
    masks=[*pos,*neg]; steps=[]; prev=0
    for m in masks:
        d=m^prev
        steps.append((bool(d>>100),list(bits(d&((1<<100)-1)))))
        prev=m
    return [('hGadget',target,steps[:len(pos)],steps[len(pos):],bool(prev>>100),list(bits(prev&((1<<100)-1))))]

if __name__=='__main__':
    for nm,src,dst in [('s3aOps',ST2,ST3A),('s3bPostOps',ST3A,ST3B)]:
        w=src.copy()
        ph=simulate(w,S.eval_op_list(nm))
        assert w==dst and not ph
        print(nm,[i for i in ALLOWED if src[i]],[i for i in ALLOWED if dst[i]])
