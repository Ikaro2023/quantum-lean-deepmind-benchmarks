"""Replay local 21-AND obstruction witnesses by evaluating their equations on all
assignments of Hamming weight at most two. No Pfaffian linear-system solve."""
from followup import *
from collections import Counter
from math import comb
import hashlib
def check_all(partial=False):
 sel=[1,11,19,20];removed=[P5[i][2] for i in sel];V=X+Y+[p for i,(a,b,p) in enumerate(P5) if i not in sel]
 assert len(V)==len(retained(V))==35
 spaces={frozenset({0})}
 for j in range(1,16):spaces|={S|frozenset(m^j for m in S) for S in spaces}
 subspaces=[S for S in spaces if len(S)<=8];allowed=[]
 for S in subspaces:
  more=independent(V,[xorv(removed,m) for m in sorted(S)])
  if closure(X,independent(X,V+more))[0]:allowed.append(sorted(S))
 assert allowed==[[0,3,5,6,9,10,12,15]]
 W=[removed[0]^v for v in removed[1:]]
 # Coordinates describe all alternating forms whose evaluated truth table
 # equals the chosen target plus an arbitrary linear combination of live wires.
 pairs=list(combinations(range(len(V)),2));vals=[V[i]&V[j] for i,j in pairs];aug=retained(V+W)
 compatible=null_masks([nf(aug,v) for v in vals])
 tags=[sol(aug,xorv(vals,m))>>len(V) for m in compatible]
 free=[xorv(compatible,m) for m in null_masks(tags)];d=len(free)
 assert d==190
 ns=1+d+comb(d,2);allvals=(1<<ns)-1
 variables=[1<<(i+1) for i in range(d)]
 for label,(i,j) in enumerate(combinations(range(d),2),d+1):
  variables[i]|=1<<label;variables[j]|=1<<label
 quad_ids=list(combinations(range(len(V)),4))
 certs=json.loads(Path('pfaffian_witness.json').read_text());out=[]
 if not partial:assert [c['target'] for c in certs]==list(range(1,8))
 for c in certs:
  t=c['target'];particular=xorv(compatible,sol(retained(tags),t))
  edges={}
  for ei,e in enumerate(pairs):
   v=allvals if particular>>ei&1 else 0
   for var,mask in zip(variables,free):
    if mask>>ei&1:v^=var
   edges[e]=v
  result=0
  for qi in c['xor_pfaffian_indices']:
   i,j,k,l=quad_ids[qi]
   result^=(edges[i,j]&edges[k,l])^(edges[i,k]&edges[j,l])^(edges[i,l]&edges[j,k])
  assert result==allvals, ('invalid witness',t)
  out.append({'target':t,'number_of_pfaffians':len(c['xor_pfaffian_indices']),'assignments_verified':ns,'boolean_degree_at_most':2})
 result={'baseline_stage':'s5_2CoreOps','retained_baseline_AND_indices':[i for i in range(21) if i not in sel],'rewritten_AND_indices':sel,'allowed_total_intermediate_space':'span of nine linear input bits, nine frozen square output bits, and all 21 baseline paid product functions; constants implicit','proper_subspaces_examined':len(subspaces),'only_subspace_admitting_reverse_quadratic_closure':allowed[0],'live_linear_rank':len(V),'witnesses':out,'proof_source_sha256':hashlib.sha256(Path('pfaffian_witness.json').read_bytes()).hexdigest(),'conclusion':'Lower bound 21 ANDs in this family' if len(out)==7 else 'partial witness check'}
 if len(out)==7:Path('reverse_obstruction_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result))
if __name__=='__main__':check_all('--partial' in sys.argv)
