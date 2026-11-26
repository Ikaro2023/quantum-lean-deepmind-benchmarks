"""Try rank-two downdates modulo the actual affine functions at each gadget."""
import argparse
import json
from pathlib import Path
import random
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/"m1"))
from lib import ALL, ALLOWED, ST2, ST3A, ST3B, S, Basis, affine, bits, correct, emit_gadget, simulate, xsum

USABLE=[w for w in ALLOWED if w != 99]


def outer(rows,u,v):
    for i in bits(u):
        rows[i]^=v
    for i in bits(v):
        rows[i]^=u


def polar(op):
    rows=[0]*100
    dt=0
    for _,ls in op[2]+op[3]:
        dt ^= xsum(1<<i for i in ls)
        for i in bits(dt):
            rows[i]^=dt
    assert all(not (row >> i & 1) for i,row in enumerate(rows))
    return rows


def factor(rows):
    tmp=rows.copy()
    pairs=[]
    for i,r in enumerate(tmp):
        if r:
            j=(r & -r).bit_length()-1
            u,v=r,tmp[j]
            pairs.append((u,v))
            outer(tmp,u,v)
    assert not any(tmp)
    return pairs


def residual(base,x):
    for k in sorted(base.piv,reverse=True):
        if x>>(k-1)&1:
            x ^= base.piv[k][0]
    return x


def update(rows,w,base,limit,rng):
    fs=[z for pair in factor(rows) for z in pair]
    vals=[xsum(w[i] for i in bits(m)) for m in fs]
    C=[[residual(base,x&y) for y in vals] for x in vals]
    n=len(fs)
    tries=list(range(1,1<<n))
    rng.shuffle(tries)
    for u in tries[:limit]:
        idx=list(bits(u))
        bs=Basis()
        for j in range(n):
            val=xsum(C[i][j] for i in idx)
            bs.add((val<<1) | (u>>(j^1)&1),1<<j)
        v=bs.solve(1)
        if v is not None:
            rr=rows.copy()
            outer(rr,xsum(fs[i] for i in idx),xsum(fs[j] for j in bits(v)))
            assert 2*len(factor(rr))==n-2
            return rr


def improve(w,op,limit,rng):
    t=op[1]
    ws=[i for i in USABLE if w[i]]
    base=Basis([ALL]+[w[i] for i in ws])
    original=w.copy()
    ph=simulate(original,[op])
    rows=polar(op)
    while True:
        rr=update(rows,w,base,limit,rng) if any(rows) else None
        if rr is None: break
        rows=rr
    pairs=factor(rows)
    if pairs and 2*len(pairs)+2>=S.t_cost([op]):
        return [op]
    ops=emit_gadget(t,pairs)
    test=w.copy()
    ph2=simulate(test,ops)
    c=base.solve(test[t]^original[t])
    assert c is not None
    mask=xsum((1<<100 if j==0 else 1<<ws[j-1]) for j in bits(c))
    adjust=affine(test,t,mask)
    simulate(test,adjust)
    try:
        fix=correct(test,ph^ph2,USABLE)
    except AssertionError:
        return [op]
    assert test==original and simulate(test,fix,ph2)==ph
    return ops+adjust+fix


def main(limit):
    rng=random.Random(971)
    for stage,vin,vout in (("s3aOps",ST2,ST3A),("s3bPostOps",ST3A,ST3B)):
        ops=S.eval_op_list(stage)
        w=vin.copy()
        result=[]
        for j,op in enumerate(ops):
            chosen=improve(w,op,limit,rng) if op[0]=="hGadget" else [op]
            if len(chosen)!=1 or chosen[0]!=op:
                print(stage,j,op[1],S.t_cost([op]),S.t_cost(chosen),flush=True)
                partial=result+chosen+ops[j+1:]
                test=vin.copy()
                assert simulate(test,partial)==0 and test==vout
                dest=HERE/(stage+"_rank.json")
                if not dest.exists() or S.t_cost(json.loads(dest.read_text())[stage])>S.t_cost(partial):
                    dest.write_text(json.dumps({stage:partial},separators=(",",":")),encoding="utf8")
            result+=chosen
            simulate(w,[op])
        print("final",stage,S.t_cost(result),flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--limit",type=int,default=16384)
    main(p.parse_args().limit)
