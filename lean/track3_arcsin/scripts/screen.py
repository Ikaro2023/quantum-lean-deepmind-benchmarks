"""Read-only replay of the Arcsin bonus screens; also check reusable symbolic products."""
from pathlib import Path
import contextlib
import hashlib
import io
import json
import os
import re
import subprocess
import sys

here=Path(__file__).resolve().parent
base=here.parents[1]
arc=base/"track3_arcsin"
sys.dont_write_bytecode=True
sys.path.insert(0,str(arc/"codex_opt/m1"))
import lib as L

scripts=["opt_s43_s44_s51.py","opt_s53_dp.py","test_q_drop.py","codex_opt/m1/selectors.py"]
record={}
for name in scripts:
    path=arc/name
    dest=here/(path.stem+".log")
    proc=subprocess.run([sys.executable,"-B",str(path)],cwd=here,
        env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1",PYTHONIOENCODING="utf-8"),
        stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    dest.write_bytes(proc.stdout)
    assert proc.returncode==0,(path,proc.stdout[-1000:])
    record[name]=dict(sha256=hashlib.sha256(path.read_bytes()).hexdigest(),exit=proc.returncode,
                      output_sha256=hashlib.sha256(dest.read_bytes()).hexdigest())

def sym(stage, cleanname, defsname, initial=None):
    defs=[tuple(map(int,x)) for x in re.findall(r"\((\d+),\s*(\d+)\)",L.S.def_blocks[defsname][1])]
    table={tuple(sorted(p)):1<<(103+i) for i,p in enumerate(defs)}
    clean=list(map(int,re.findall(r"\d+",L.S.def_blocks[cleanname][1])))
    tr=initial.copy() if initial else [0 if i in clean else 1<<(i+1) for i in range(100)]
    ops=L.S.eval_op_list(stage)
    lastErase={}
    caches=[]
    recurrences=[]
    linear=[]
    snapshots=[]
    for idx,(kind,*args) in enumerate(ops):
        snapshots.append(tuple(tr))
        if kind=="x": tr[args[0]]^=1
        elif kind=="cx":
            a,b=args
            tr[b]^=tr[a]
        else:
            a,b,t=args
            token=table[tuple(sorted((tr[a],tr[b])))]
            if kind=="and4t":
                assert tr[t]==0
                if token in lastErase:
                    earlier,et=lastErase[token]
                    recurrences.append((earlier,idx,token))
                    # The old and new source masks are equal as polynomials under
                    # the stage's original ancilla preconditions. Only a clean
                    # untouched extra wire can store this independent helper here.
                    occupied={v for g in ops[earlier:idx+1] for v in g[1:]}
                    free=[i for i,val in enumerate(snapshots[earlier]) if val==0 and i not in occupied]
                    if free: caches.append((earlier,idx,free))
                if L.Basis([1,*tr]).solve(token) is not None: linear.append(idx)
                tr[t]=token
            elif kind=="unand":
                assert tr[t]==token
                tr[t]=0
                lastErase[token]=(idx,t)
            else: raise ValueError(kind)
    # Even if every named wire is touched, free CNOT basis changes could move
    # a cached product between slots. A full 100-wire affine space where the
    # product is independent rules this out for that fixed symbolic trace.
    saturated=[(i,b) for i,state in enumerate(snapshots)
               if all(state) and len((b:=L.Basis([1,*state])).piv)==101]
    affine_survivors=[[start,end] for start,end,term in recurrences if
                      all(b.solve(term) is not None for i,b in saturated if start<i<=end)]
    return dict(ops=len(ops),ands=sum(op[0]=="and4t" for op in ops),linear=linear,caches=caches,
                recompute_intervals=len(recurrences),saturated_states=len(saturated),
                affine_cache_survivors=affine_survivors),tr

results={}
results["s4_3"],tr43=sym("s4_3Ops","clean_4_3","defs_4_3")
results["s4_4"],_=sym("s4_4Ops","clean_4_4","defs_4_4")
results["s5_1"],_=sym("s5_1Ops","clean_4_3","defs_4_3",tr43)
results["s5_3"],_=sym("s5_3PreOps","clean_5_3","defs_5_3")

ops=L.S.eval_op_list("s3bPostOps");w=L.ST3A.copy();ph=0;dependent=[]
for i,op in enumerate(ops):
    if op[0]=="and4t":
        a,b,t=op[1:]
        if L.Basis([L.ALL]+[w[j] for j in L.ALLOWED]).solve(w[a]&w[b]) is not None:
            dependent.append(i)
    ph=L.simulate(w,[op],ph)
assert w==L.ST3B and ph==0
results["s3bPost"]=dict(ops=len(ops),ands=sum(op[0]=="and4t" for op in ops),linear=dependent,
    final_phase=ph,bins=440,output_equal=True)
replay=json.loads((arc/"codex_opt/receipts/simulation.json").read_bytes())
peaks={k:[r[0] for r in replay[k]["new"] if r[3]==50] for k in ("449","leaf_endpoints")}
report=dict(replayed=record,extra_screens=results,submitted_candidate_peaks=peaks)
(here/"results.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf8")
print(json.dumps(report,indent=1))
