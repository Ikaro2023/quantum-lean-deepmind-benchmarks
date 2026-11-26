from lib import *
from collections import Counter

def group_stats(w, pos):
    keys = [sum(((w[j]>>i)&1)<<k for k,j in enumerate(pos)) for i in range(440)]
    return [sum(1<<i for i,k in enumerate(keys) if k==v) for v in sorted(set(keys))]

def basis(w):
    ws=[k for k in ALLOWED if w[k]]
    return Basis([ALL]+[w[k] for k in ws])

if __name__=='__main__':
    groups=[(a,group_stats(ST2,a)) for a in combinations(ADDRESS,5)]
    for nm,src in [('s3aOps',ST2),('s3bPostOps',ST3A)]:
        w=src.copy()
        def report():
            b=basis(w)
            scores=[]
            for a,rows in groups:
                b2=Basis()
                b2.piv=b.piv.copy()
                absent=sum(b2.add(v,0) for v in rows)
                scores.append((absent,len(rows),a))
            print('best', sorted(scores)[:3], 'new',next(s for s in scores if s[-1]==(41,42,43,44,46)))
        report()
        for i,op in enumerate(S.eval_op_list(nm)):
            if op[0]=='hGadget' and (op[1] in (93,50,61,73,74,77)): 
                print(nm,i,op[1])
                report()
            simulate(w,[op])
