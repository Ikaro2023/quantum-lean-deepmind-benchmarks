"""Independent rational Taylor enclosure for sign/weak-filter limiting schedules (width 1).
Fixed point round-down errors, truncation estimates and the final cost are all exact rationals.
The enclosed objects are mathematical limiting-walk quantities, independent of Lean semantics."""
from fractions import Fraction as F
from math import factorial,isqrt,ceil
import json,sys
from decimal import localcontext,Decimal
from pathlib import Path
from recon_input import V,unpack
here=Path(__file__).resolve().parent
S=10**26
NS=10**9
def dec(z):
    with localcontext() as ctx:
        ctx.prec=42
        return str(Decimal(z.numerator)/Decimal(z.denominator))
def verify(name):
    q=json.loads((here/(name+".json")).read_text())
    m,r=1024,512;d=r+1
    assert q["widths"]==[1]*len(q["times"])
    den=q.get("denom",NS)
    att=q.get("no_click_amplitude_numerator",[den]*len(q["times"]))
    assert len(att)==len(q["times"])==len(q["masks_le_hex"])
    v=[S]+[0]*r
    b=[isqrt(4*(w+1)*(m-w)*(r-w)*S*S) for w in range(r)]
    left=[0]+b;right=b+[0]
    # The upper bound rounds up to enclose the exact (not rounded) operator.
    norm=max(a+b for a,b in zip(left,right))+2
    ev=F(0);etime=F(0);tc=F(0);steps=0;active=0
    for t,hx,ak in zip(q["times"],q["masks_le_hex"],att):
        assert 0<=ak<=den
        tc+=F(t*sum(x*x for x in v),NS*S*S)
        etime+=F(t,NS)*(2+ev)*ev
        h=ceil(F(t*norm,NS*S))
        assert h>0
        # Round the generator edges; max-norm perturbation <= 2/S by row sums.
        ev+=F(2*t,NS*S)
        sub_err=F(24*3*23,S)+F(6,factorial(25))
        for _ in range(h):
            z=v.copy();out=v.copy();D=h*NS*S
            for j in range(1,25):
                div=D*j
                z=[t*(-la*x+rb*y)//div for la,rb,x,y in zip(left,right,[0]+z[:-1],z[1:]+[0])]
                out=[x+y for x,y in zip(out,z)]
            v=out
            ev+=sub_err
        steps+=h
        mask=unpack(hx)
        v=[-a if j in mask else a for j,a in enumerate(v)]
        if ak<den:
            active+=1
            v[-1]=v[-1]*ak//den
            ev+=F(1,S)
        assert ev<1
    psq=[F(x*x,S*S) for x in v]
    # Failure is the final unsucceeded mass with terminal bin removed. This is
    # one squared projected norm, so it incurs a single Lipschitz error bound.
    fail=sum(psq[:-1]);ep=(2+ev)*ev
    assert fail+ep<1
    cc=sum(vv*p for vv,p in zip(V[::-1],psq))/10**15
    ec=F(max(V),10**15)*ep
    Vlo,Vhi=tc+cc-etime-ec,tc+cc+etime+ec
    Rlo,Rhi=(tc-etime)/(1-fail+ep),(tc+etime)/(1-fail-ep)
    # π/4 > 785398163397448/10^15 and H512 > hLo/10^15.
    P=10**15
    hLo=sum(P*P//(isqrt(j*P*P)+(isqrt(j*P*P)**2<j*P*P)) for j in range(1,r+1))
    unit_lo=F(785398163397448*hLo,32*P*P)
    # Unit upper uses the classical 355/113 approximation above pi,
    # but tight speed lower estimates require only a lower unit enclosure.
    out=dict(name=name,steps=steps,active_weak_checks=active,vector_error=dec(ev),
        expected_walk=dec(tc),expected_walk_error=dec(etime),failure=dec(fail),failure_error=dec(ep),
        old_cost=[dec(Vlo),dec(Vhi)],retry_cost=[dec(Rlo),dec(Rhi)],
        incumbent_ratio_rational_n12=ceil(Vhi/unit_lo*10**12),retry_ratio_rational_n12=ceil(Rhi/unit_lo*10**12),
        gr0_lower_n20=6957627832198676185,gr0_lower_den=10**20)
    for mode in ("incumbent","retry"):
        ratio=F(out[mode+"_ratio_rational_n12"],10**12)
        speed=F(out["gr0_lower_n20"],10**20)/ratio
        out[mode+"_speed_lower"]=dec(speed)
    print(json.dumps(out,indent=2))
    (here/(name+"_enclosure.json")).write_text(json.dumps(out,indent=2))
if __name__=="__main__":verify(sys.argv[1])
