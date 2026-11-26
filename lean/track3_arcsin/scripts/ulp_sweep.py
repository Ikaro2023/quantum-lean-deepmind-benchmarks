"""Exhaust all permitted magnitudes against arcsin using rigorous Arb enclosures."""
import bisect
import hashlib
import json
import re
import time
from pathlib import Path
import flint
import numpy as np
from flint import arb, ctx
from slice_ops import HOME, sim

SCALE = 1 << 23
MOD = 1 << 25
CHUNK = 32768
SOURCE = Path(sim.SOL_DIR)
P = (SOURCE / 'PolyTables.lean').read_text(encoding='utf8')
pattern = r'⟨(\d+), (\d+), (\d+), (\d+), (\d+), (\d+), (\d+), (\d+), (\d+)⟩'
LEAVES = [tuple(map(int, m)) for m in re.findall(pattern, P)]
WORDS = list(map(int, re.findall(r'\d+', re.search(r'def sq9Words[^\[]*\[([^\]]*)\]', P, re.S)[1])))
assert len(WORDS) == 9 and len(LEAVES) == 1064
assert LEAVES[0][0] == 0 and LEAVES[-1][1] == SCALE
assert all(a[1] == b[0] for a,b in zip(LEAVES,LEAVES[1:]))
assert all(a < b for a,b,*_ in LEAVES)
SQ9 = np.array([sum((word >> i & 1) << k for k, word in enumerate(WORDS)) for i in range(512)],dtype=np.int64)
LEAF_STARTS = [leaf[0] for leaf in LEAVES]
stage_b = (SOURCE/'StageProofB.lean').read_text(encoding='utf8')
ENDPOINT = int(re.search(r'theorem rawDelta25_8388608 : rawDelta25 8388608 = (\d+)',stage_b)[1])

def positive_delta(leaf,us):
    # uRotSrc indexes modulo 22, while the leading 16*u term uses the full magnitude.
    start,stop,_,_,base,kv,lv,shift,_ = leaf
    word = us & ((1<<22)-1)
    upper = ((word << shift) | (word >> (22-shift))) & 65535
    d9 = (upper >> 6) & 511
    sq9 = SQ9[np.where((upper>>15) != 0, d9, 511-d9)]
    curv = 2*sq9
    for k in range(8):
        term = sq9 >> (7-k)
        curv += ((1<<(k+2))-1)-term if lv>>k&1 else term
    signed_slope = 4*upper
    for k in range(15):
        term = upper>>(13-k) if k<14 else 2*upper
        signed_slope += term if kv>>k&1 else -term
    # diff27 is Nat.sub and deltaPos25 divides the nonnegative integer by 16.
    return np.maximum(16*us+base+signed_slope+curv-1024,0)//16

def blocks():
    for idx,leaf in enumerate(LEAVES):
        for start in range(leaf[0],leaf[1],CHUNK):
            xs=np.arange(start,min(leaf[1],start+CHUNK),dtype=np.int64)
            yield idx,xs,positive_delta(leaf,xs)
    yield None,np.array([SCALE],dtype=np.int64),np.array([ENDPOINT],dtype=np.int64)

def filehash(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check_original_sim():
    checked=[]
    for j,(y,b) in enumerate(sim.test_inputs):
        signed_y = y if y<MOD//2 else y-MOD
        mag=abs(signed_y)
        if mag==SCALE:
            delta=ENDPOINT
        else:
            leaf = LEAVES[bisect.bisect_right(LEAF_STARTS,mag)-1]
            delta=int(positive_delta(leaf,np.array([mag],dtype=np.int64))[0])
        expected=(-delta if signed_y<0 else delta)%MOD
        b_final=sum(((sim.wires[k]>>j)&1)<<k for k in range(25))
        got=(b_final-b)%MOD
        assert got==expected,(j,y,b,got,expected)
        checked.append([j,y,b,got])
    assert len(checked)==449
    return hashlib.sha256(json.dumps(checked,separators=(',',':')).encode()).hexdigest()

def main():
    t=time.perf_counter()
    sample_hash=check_original_sim()
    # Fast pass only chooses an efficient threshold. Every magnitude is subsequently
    # certified using an Arb enclosure, irrespective of the double-precision screening.
    top=[]
    digest=hashlib.sha256()
    count=0
    for i,xs,zs in blocks():
        digest.update(zs.astype('<u4').tobytes())
        approx=np.abs(zs-SCALE*np.arcsin(xs/SCALE))
        keep=min(16,len(xs))
        ix=np.argpartition(approx,-keep)[-keep:]
        top=sorted(top+[(float(approx[j]),int(xs[j])) for j in ix],reverse=True)[:16]
        count+=len(xs)
    assert count==SCALE+1
    threshold=str(round(top[-1][0]-1e-8,12))
    ctx.prec=128
    cutoff=arb(threshold)
    denom=arb(SCALE)
    near=[]
    certified_below=0
    for i,xs,zs in blocks():
        start=int(xs[0])
        for j,z in enumerate(zs.tolist(),start):
            err=abs(arb(z)-(arb(j)/denom).asin()*denom)
            if err<cutoff:
                certified_below+=1
            else:
                near.append((err,j,z,i))
    assert certified_below+len(near)==count
    near.sort(key=lambda r:float(r[0].mid()),reverse=True)
    assert len(near)>=2 and near[1][0]>cutoff
    assert near[0][0]>near[1][0] and all(near[1][0]>r[0] for r in near[2:])
    limit=arb(1048576)/1000000
    assert near[0][0]<limit
    ctx.prec=256
    for ix in range(2):
        _,u,z,leaf=near[ix]
        err=abs(arb(z)-(arb(u)/SCALE).asin()*SCALE)
        near[ix]=(err,u,z,leaf)
    # Arb's bracketed numbers include the rounding radius of the displayed decimal.
    def summary(q):
        e,u,z,i=q
        return dict(u=u,positive_delta=z,leaf_index_zero_based=i,abs_error_ulp_arb=e.str(66))
    out=dict(scope='frozen integer deltaPos25, positive magnitudes; negative follows z25Delta and odd arcsin',
             leaves=len(LEAVES),positive_interior_including_zero=SCALE,endpoint=ENDPOINT,magnitude_count=count,
             signed_domain_count=2*SCALE+1,chunk_size=CHUNK,numpy=np.__version__,python_flint=flint.__version__,
             arb_pass_bits=128,arb_top_two_bits=256,uncertain_or_above_threshold=len(near),threshold_ulp=threshold,
             proved_strictly_below_threshold=certified_below,top_two_strictly_ordered_against_all=True,
             worst=summary(near[0]),runner_up=summary(near[1]),
             worst_minus_runner_up_ulp=(near[0][0]-near[1][0]).str(66),
             benchmark_limit_minus_max_ulp=(arb(1048576)/1000000-near[0][0]).str(66),
             positive_delta_le_uint32_sha256=digest.hexdigest(),original_op102_sim_exact_matches=sim.M,
             original_op102_sim_input_output_rows_sha256=sample_hash,
             source_sha256={name:filehash(SOURCE/name) for name in ('PolyTables.lean','PolyDefs.lean','StageProofB.lean')},
             script_sha256=filehash(Path(__file__)),seconds=round(time.perf_counter()-t,2))
    (HOME/'ulp_sweep.json').write_text(json.dumps(out,indent=2),encoding='utf8')
    print(json.dumps(out,indent=2))
if __name__=='__main__':
    main()
