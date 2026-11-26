"""Combine diagonal sign corrections for a verified table on the eight frozen slices."""
from closed_forms import *


def compress(stage,ops):
    vin,vout=(ST2,ST3A) if stage=="s3aOps" else (ST3A,ST3B)
    steps=[op for op in ops if op[0] not in ("z","cz")]
    w=vin.copy()
    debt=simulate(w,steps)
    assert w==vout
    best=None
    w=vin.copy()
    for i,op in enumerate(steps):
        if op[0]=="hGadget" or i==len(steps)-1:
            try: correction=correct(w,debt,USABLE)
            except AssertionError: pass
            else:
                if best is None or len(correction)<len(best[1]):
                    best=i,correction
        simulate(w,[op])
    if best is None: return ops
    i,fix=best
    result=steps[:i]+fix+steps[i:]
    test=vin.copy()
    assert simulate(test,result)==0 and test==vout
    print(stage,len(ops),'->',len(result),'phase gates',len(fix),'at',i,flush=True)
    return result if len(result)<len(ops) else ops

if __name__=="__main__":
    inp,out=sys.argv[1:]
    src=json.loads((HERE/inp).read_text())
    data={name:compress(name,ops) for name,ops in src.items()}
    (HERE/out).write_text(json.dumps(data,separators=(",",":")),encoding="utf8")
