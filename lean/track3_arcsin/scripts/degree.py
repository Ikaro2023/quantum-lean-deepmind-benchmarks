"""Exact algebraic degree of the two normalized 23-input prefix circuits."""
from rotation import CUBES
from slice_ops import HOME, tree, Basis
import json
import numpy as np

def audit(stage):
    tr=tree(stage)
    ws=[w for w in range(50,100) if tr[w]]
    assert len(ws)<=16
    n=1<<23
    assert CUBES[0][0]==0 and CUBES[-1][1]==n
    assert all(ue-us==1<<width and us%(1<<width)==0 for us,ue,width,s in CUBES)
    assert all(l[1]==r[0] for l,r in zip(CUBES,CUBES[1:]))
    f=np.zeros(n,dtype=np.uint16)
    for i,(us,ue,_,_) in enumerate(CUBES):
        f[us:ue]=sum(((tr[w]>>i)&1)<<j for j,w in enumerate(ws))
    # GF(2) subset Möbius transform. Entry S is the coefficient of the monomial on bits S.
    for k in range(23):
        blocks=f.reshape(-1,1<<(k+1))
        blocks[:,1<<k:]^=blocks[:,:1<<k]
    pop=np.zeros(n,dtype=np.uint8)
    for k in range(23):pop[1<<k:1<<(k+1)]=pop[:1<<k]+1
    degrees={}
    for j,w in enumerate(ws):
        hits=(f&(1<<j))!=0
        degree=int(max(pop[hits]))
        monomial=int(np.flatnonzero(hits&(pop==degree))[0])
        degrees[w]=dict(degree=degree,first_highest_degree_monomial_hex=hex(monomial))
    return dict(domain=n,nonzero_ancillas=len(ws),wire_degrees=degrees)

if __name__=='__main__':
    stats={name:audit(name) for name in ('trS2a','trS6cIn')}
    (HOME/'degree_receipt.json').write_text(json.dumps(stats,indent=2))
    print(json.dumps(stats,indent=2))
