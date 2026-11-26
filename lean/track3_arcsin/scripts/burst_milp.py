"""Screen complete zero-return carry-save bursts, with all columns accounted for."""
from pathlib import Path
import json
import re
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp

here=Path(__file__).resolve().parent
src=here.parents[1]/"discoveries_ref/QuantumComputationDiscoveries/Primitives/Arcsin/Solution/StageTablesB.lean"
txt=src.read_text(encoding="utf8")
found=re.search(r'def bag_5_3\b[^=]*:=\s*(\[\[.*?\]\])\n',txt,re.S)
if found is None:
    txt=src.with_name("StageTablesA.lean").read_text(encoding="utf8")
    found=re.search(r'def bag_5_3\b[^=]*:=\s*(\[\[.*?\]\])\n',txt,re.S)
extra=[len(re.findall(r'\d+',c))-1 for c in re.findall(r'\[([^\[\]]*)\]',found[1][1:-1])]

def solve(B,u,cap,ceiling=165):
    # (take, carry) per column and per burst. All eight U18 helper ANDs are charged;
    # 6 preserved helper outputs remain in scratch for any later bursts.
    N=2*B*28
    rows=[];lo=[];hi=[]
    def put(terms,l,h):
        line=np.zeros(N)
        for idx,coef in terms: line[idx]+=coef
        rows.append(line);lo.append(l);hi.append(h)
    def take(b,c):return b*56+2*c
    def carry(b,c):return b*56+2*c+1
    for c in range(28):
        put([(take(b,c),1) for b in range(B)],extra[c],extra[c])
    ub=np.full(N,100)
    for b in range(B):
        for c in range(28):
            ub[take(b,c)]=extra[c]
            if c>=22 and b<u: ub[take(b,c)]=0
            terms=[(carry(b,c),2),(take(b,c),-1)]
            if c: terms.append((carry(b,c-1),-1))
            put(terms,0,1)
        put([(carry(b,c),1) for c in range(28)],0,cap-(8 if b==u else 6 if b>u else 0))
    put([(carry(b,c),1) for b in range(B) for c in range(28)],0,ceiling-8)
    obj=np.array([float(i%2) for i in range(N)])
    ans=milp(obj,integrality=np.ones(N),bounds=Bounds(np.zeros(N),ub),
        constraints=LinearConstraint(np.array(rows),lo,hi),
        options=dict(time_limit=10.0,mip_rel_gap=0.0,threads=1))
    ret=dict(bursts=B,helpers_at=u,slots=cap,ceiling=ceiling,status=int(ans.status),message=ans.message)
    if ans.x is not None:
        t=[[int(round(ans.x[take(b,c)])) for c in range(28)]+[extra[28] if b==u else 0] for b in range(B)]
        counts=[]
        for row in t:
            carry_in=0;total=0
            for tk in row[:-1]:
                carry_in=(1+tk+carry_in)//2
                total+=carry_in
            counts.append(total)
        assert [sum(r[c] for r in t) for c in range(29)]==extra
        assert all(v<=cap-(8 if b==u else 6 if b>u else 0) for b,v in enumerate(counts))
        assert sum(counts)+8<=ceiling
        ret.update(complete_takes=t,counts=counts,ands=sum(counts)+8)
    return ret
checkpoint=here/"burst_milp.json"
out=json.loads(checkpoint.read_bytes()) if checkpoint.exists() else []
out=[r for r in out if r.get("ceiling")==165 and r.get("status") in (0,2)]
control=solve(1,0,200,300)
assert "ands" in control
(here/"burst_control.json").write_text(json.dumps(control,indent=2)+"\n",encoding="utf8")
for B in range(3,7):
  for u in range(B):
    if any(r["bursts"]==B and r["helpers_at"]==u for r in out): continue
    result=solve(B,u,39)
    print(result,flush=True)
    out.append(result)
    checkpoint.write_text(json.dumps(out,indent=2)+"\n",encoding="utf8")
