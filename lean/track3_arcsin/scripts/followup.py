from hyper import *
import struct,sys
def make():
 W=next(w for h,w in hyperplanes() if list(inds(h))==[1,11,19,20])
 plan=reach(X+Y+W,X+Y,2);V=X+Y+[p for a,b,p in plan];extra=independent(V,W)
 print('V,extra',len(V),len(extra),'paid',len(plan))
 B=retained(V+extra);R=random.Random(98512347);hashes=[R.getrandbits(60) for _ in range(512)]
 def code(p):
  resid=nf(B,p);c=sol(B,p^resid);tag=c>>len(V)
  return xorv(hashes,resid)|(tag<<60)
 codes=[code(a&b) for a in V for b in V]
 with open('bridge_codes.bin','wb') as f:f.write(struct.pack('<II',len(V),len(extra))+struct.pack('<'+'Q'*len(codes),*codes))
 Path('bridge_basis.json').write_text(json.dumps({'V':V,'extra':extra,'paid':plan}))
if __name__=='__main__':make()
