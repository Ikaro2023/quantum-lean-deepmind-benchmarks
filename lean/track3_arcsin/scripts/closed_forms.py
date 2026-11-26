"""Vary the whole alternating form as well as its B-dependent linear cross terms."""
import itertools
from rank_updates import *
from partitions import group_stats


def synth(w,op,groups,r,trials,rng):
    t=op[1]
    ws=[i for i in USABLE if w[i]]
    lin=Basis([ALL]+[w[i] for i in ws])
    def lift(m):
        return xsum(1<<ws[j-1] if j else 1<<100 for j in bits(m))
    # The surviving B-linear subspace may contain sums of indicators even
    # after some individual indicators cease to be representable.
    # Track the kernel of reduction modulo the affine live-wire span.
    quotient=Basis()
    B=[]
    for j,x in enumerate(groups):
        v=residual(lin,x)
        m=quotient.solve(v)
        if m is None:
            quotient.add(v,1<<j)
        else:
            B.append(x^xsum(groups[i] for i in bits(m)))
    if len(B)<20: return
    labels=[lift(lin.solve(x)) for x in B]
    old=w.copy(); orig_phase=simulate(old,[op])
    target=old[t]
    pairs=list(itertools.combinations(range(2*r),2))
    for _ in range(trials):
        zs=[rng.getrandbits(len(ws)) for _ in range(2*r)]
        zs=[xsum(1<<ws[j] for j in bits(z)) for z in zs]
        vals=[xsum(w[j] for j in bits(z)) for z in zs]
        cols=[a&b for a in vals for b in B] + [vals[i]&vals[j] for i,j in pairs] + groups
        basis=Basis([ALL]+[w[i] for i in ws]+cols)
        s=basis.solve(target)
        if s is None: continue
        s >>= 1+len(ws)
        betas=[]
        for _ in vals:
            betas.append(xsum(labels[i] for i in bits(s & ((1<<len(B))-1))))
            s >>= len(B)
        A=[0]*len(vals)
        s &= (1<<len(pairs))-1
        for k in bits(s):
            i,j=pairs[k]; A[i]^=1<<j; A[j]^=1<<i
        inv=Basis(A)
        if len(inv.piv)!=len(vals):continue
        adjusted=[]
        for i,z in enumerate(zs):
            adjusted.append(z^xsum(betas[j] for j in bits(inv.solve(1<<i))))
        rows=[0]*101
        for k in bits(s):
            i,j=pairs[k];outer(rows,adjusted[i],adjusted[j])
        # Constants can be treated as another affine input; the final linear
        # residual accounts for any diagonal terms in the decomposition.
        rr=factor(rows)
        if len(rr)>r:continue
        alt=emit_gadget(t,rr)
        test=w.copy()
        phase=simulate(test,alt)
        delta=lin.solve(test[t]^target)
        if delta is None:continue
        adjust=affine(test,t,lift(delta))
        simulate(test,adjust)
        try: fix=correct(test,phase^orig_phase,USABLE)
        except AssertionError:continue
        assert test==old and simulate(test,fix,phase)==orig_phase
        return alt+adjust+fix


def run(trials, targets=None):
    rng=random.Random(5129)
    from lib import ADDRESS
    g=group_stats(ST2,ADDRESS[4:])
    for stage,vin,vout in (("s3aOps",ST2,ST3A),("s3bPostOps",ST3A,ST3B)):
        ops=S.eval_op_list(stage)
        w=vin.copy(); result=[]
        for j,op in enumerate(ops):
            chosen=None
            if op[0]=="hGadget" and S.t_cost([op])>=14 and (targets is None or j in targets):
                chosen=synth(w,op,g,(S.t_cost([op])-4)//2,trials,rng)
            if chosen:
                print(stage,j,op[1],S.t_cost([op]),S.t_cost(chosen),flush=True)
                table=result+chosen+ops[j+1:]
                test=vin.copy()
                assert simulate(test,table)==0 and test==vout
                suffix="_closed.json" if targets is None else "_closed_"+"_".join(map(str,sorted(targets)))+".json"
                dest=HERE/(stage+suffix)
                if not dest.exists() or S.t_cost(json.loads(dest.read_text())[stage])>S.t_cost(table):
                    dest.write_text(json.dumps({stage:table},separators=(",",":")),encoding="utf8")
            result+=chosen or [op]
            simulate(w,[op])
        print("end",stage,S.t_cost(result),flush=True)

if __name__=="__main__":
    run(int(sys.argv[1]) if len(sys.argv)>1 else 64, set(map(int,sys.argv[2:])) or None)
