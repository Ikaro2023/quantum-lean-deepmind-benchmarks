"""Recompute GR0 and the limiting independent-restart reference without any V table."""
from decimal import Decimal, localcontext
from fractions import Fraction as F
from math import ceil, factorial, isqrt
from pathlib import Path
import json
import runpy
from flint import arb
from lean_tools import PROJECT, ROOT, digest

REF=PROJECT/"inputs"

def decimal(q):
    with localcontext() as ctx:
        ctx.prec=46
        return str(Decimal(q.numerator)/Decimal(q.denominator))

def gr0():
    evaluator=REF/"baseline.py"
    score=runpy.run_path(str(evaluator))["score"]
    cap=4
    lo,hi=score(1024,512,cap,32)
    others={}
    for t in (1,2,3):
        a,b=score(1024,512,t,6)
        assert a>hi
        others[t]=[a.str(35),b.str(35)]
    h=[arb(0)]
    for j in range(1,513):h.append(h[-1]+1/arb(j).sqrt())
    assert h[5]/h[512]>hi
    rational=F(6957627832198676185,10**20)
    assert lo>arb(rational.numerator)/arb(rational.denominator)
    return rational, dict(source_sha256=digest(evaluator),winning_cap=cap,range=[lo.str(38),hi.str(38)],
                         other_caps=others,all_caps_ge_5_lower=(h[5]/h[512]).str(35))

def restart():
    source=REF/"refine_placement0.json"
    q=json.loads(source.read_bytes());m,r=1024,512;B=10**26;D=10**9
    assert q["widths"]==[1]*24 and q["denom"]==D
    v=[B]+[0]*r
    edges=[isqrt(4*(j+1)*(m-j)*(r-j)*B**2) for j in range(r)]
    left=[0]+edges;right=edges+[0]
    norm=max(a+b for a,b in zip(left,right))+2
    err=time_err=F(0);work=F(0);steps=0
    for t,mask,a in zip(q["times"],q["masks_le_hex"],q["no_click_amplitude_numerator"],strict=True):
        assert 0<=a<=D
        work+=F(t*sum(x*x for x in v),D*B**2)
        time_err+=F(t,D)*(2+err)*err
        h=ceil(F(t*norm,D*B))
        err+=F(2*t,D*B)
        for i in range(h):
            z=v[:];out=v[:]
            for j in range(1,25):
                z=[t*(b*y-a*x)//(j*h*D*B) for a,b,x,y in zip(left,right,[0]+z[:-1],z[1:]+[0])]
                out=[u+w for u,w in zip(out,z)]
            v=out
        steps+=h
        err+=h*(F(24*3*23,B)+F(6,factorial(25)))
        signs=int.from_bytes(bytes.fromhex(mask),"little")
        assert signs.bit_length()<=r+1
        v=[-x if signs>>j&1 else x for j,x in enumerate(v)]
        if a!=D:
            v[-1]=v[-1]*a//D
            err+=F(1,B)
    failure=F(sum(x*x for x in v[:-1]),B*B);ep=(2+err)*err
    assert failure+ep<1
    interval=[(work-time_err)/(1-failure+ep),(work+time_err)/(1-failure-ep)]
    p=10**15
    harm=sum(p**2//(isqrt(j*p*p)+int(isqrt(j*p*p)**2<j*p*p)) for j in range(1,r+1))
    unit_lo=F(785398163397448*harm,32*p**2)
    ratio=ceil(interval[1]/unit_lo*10**12)
    assert ratio==26768766547
    return dict(schedule_sha256=digest(source),substeps=steps,vector_error=decimal(err),
                time=decimal(work),failure=decimal(failure),retry_interval=list(map(decimal,interval)),
                retry_ratio_numerator=ratio)

if __name__=="__main__":
    base,g=gr0()
    w=restart()
    formal=F(26768771052,10**12)
    old=F(27014193664,10**12)
    out=dict(GR0=g,GR0_lower=str(base),limiting_walk=w,lean_ratio=str(formal),
             gr0_speed_lower=decimal(base/formal),limiting_speed_lower=decimal(base/F(w["retry_ratio_numerator"],10**12)),
             prior_ratio=str(old),cost_improvement_percent=decimal(100*(1-formal/old)),
             speed_improvement_percent=decimal(100*(old/formal-1)))
    (PROJECT/"independent_numbers.json").write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8")
    print(out["gr0_speed_lower"])
