from pathlib import Path
from math import isqrt, ceil, factorial
from fractions import Fraction as F
from decimal import Decimal, getcontext
import re
s=next(Path("discoveries_ref").rglob("RampKickMuxHiCert1024.lean")).read_text(encoding="utf8")
def ints(pat):
    return [int(i) for i in re.findall(r"\d+",re.search(pat,s,re.S)[1])]
V=sum((ints(r"def rkmVPotHi_m1024_p"+str(i)+r" [^=]*:= \[([^]]+)\]") for i in range(4)),[])
flip=[]
for i in range(7):
    pos=-1
    sign=[]
    for g in ints(r"def rkmMkHi_m1024_r512_s"+str(i)+r" [^=]*:= rkmGapsToMaskHi1024 \[([^]]+)\]"):
        pos+=1+g
        sign.append(pos)
    flip.append(set(sign))
flip.append(set())
assert len(V)==513 and all(max(row,default=-1)<513 for row in flip)
scale=10**26
def unpack(hexword):
    bits=int.from_bytes(bytes.fromhex(hexword),"little")
    assert bits.bit_length()<=513
    return {j for j in range(513) if (bits>>j)&1}
X=unpack("c63bb635dbffa0828090c0fd6364cec10f8e89f071624b0e2b1fb9116ee18f098da687d0a5d1f58f6952c6e7a83d7c79b51c5b273b16d1c56576724faa4a670000")
Y=unpack("e6708e1ce3793311e8ddf50fdf1f5e1f96b7385fa6a5d89deb1263ea62e4ecd44be913126b95373039e16c405e2749cdb9793fefc1f0d957a1bd605eecea250400")
flip=[flip[0],flip[1],X,flip[2],Y,flip[3],*flip[4:]]
times=[12969116,13608050,405190,462679,191850,227435,211863,292038,369164,300160]
