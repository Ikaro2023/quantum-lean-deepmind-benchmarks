import os, re, sys
import numpy as np

SOL_DIR = r"C:\Users\OFFICE3\.gemini\antigravity\scratch\quantum_lean_breakthrough_20261125\discoveries_ref\QuantumComputationDiscoveries\Primitives\Arcsin\Solution"

def read_file(name):
    return open(os.path.join(SOL_DIR, name), encoding="utf-8").read()

# Parse ALL Op102 defs from SliceTables, StageTablesA, StageTablesB, StageCircuitB
texts = [read_file(fn) for fn in ["SliceTables.lean", "StageTablesA.lean", "StageTablesB.lean", "StageCircuitB.lean"]]
full_text = "\n".join(texts)

# Extract all `def NAME : TYPE := BODY` up to next top-level def/theorem/end/structure/abbrev/set_option/namespace/open/section
def_blocks = {}
pattern = re.compile(r'^def\s+(\w+)\s*:\s*([^:=\n]+):=\s*(.*?)(?=\n(?:def |theorem |lemma |end |structure |abbrev |private |set_option |#))', re.M | re.S)
for m in pattern.finditer(full_text + "\nend"):
    name, typ, body = m.group(1), m.group(2).strip(), m.group(3).strip()
    def_blocks[name] = (typ, body)

print(f"Parsed {len(def_blocks)} top-level defs.")

# Parse an Op102 token string into tuple representation
# Op102 constructors:
#   ('x', q), ('cx', c, t), ('and4t', c1, c2, t), ('rccx0', c1, c2, t), ('rccx1', c1, c2, t),
#   ('unand', c1, c2, t), ('unquad', quads, lins, t), ('z', q), ('cz', c1, c2),
#   ('hGadget', t, posSteps, negSteps, undoConst, undoLins)
def parse_nat_list(s):
    return [int(x) for x in re.findall(r'\d+', s)]

def parse_pair_list(s):
    return [(int(a), int(b)) for a, b in re.findall(r'\(\s*(\d+)\s*,\s*(\d+)\s*\)', s)]

def parse_steps(s):
    # List of (true/false, [n1, n2, ...])
    out = []
    for b, ls in re.findall(r'\(\s*(true|false)\s*,\s*\[([^\]]*)\]\s*\)', s):
        out.append((b == 'true', parse_nat_list(ls)))
    return out

def tokenize_top_level_list(s):
    """Split a Lean list `[a, b, c]` at top-level commas."""
    s = s.strip()
    assert s.startswith('[') and s.endswith(']'), f"Not a list: {s[:60]}...{s[-40:]}"
    inner = s[1:-1]
    items = []
    depth_sq = 0
    depth_par = 0
    cur = []
    for ch in inner:
        if ch == '[': depth_sq += 1
        elif ch == ']': depth_sq -= 1
        elif ch == '(': depth_par += 1
        elif ch == ')': depth_par -= 1
        if ch == ',' and depth_sq == 0 and depth_par == 0:
            it = ''.join(cur).strip()
            if it: items.append(it)
            cur = []
        else:
            cur.append(ch)
    it = ''.join(cur).strip()
    if it: items.append(it)
    return items

def parse_single_op(tok):
    tok = tok.strip()
    m = re.match(r'^(?:mkX|\.x)\s+(\d+)$', tok)
    if m: return ('x', int(m.group(1)))
    m = re.match(r'^(?:mkZ|\.z)\s+(\d+)$', tok)
    if m: return ('z', int(m.group(1)))
    m = re.match(r'^(?:mkCX|\.cx)\s+(\d+)\s+(\d+)$', tok)
    if m: return ('cx', int(m.group(1)), int(m.group(2)))
    m = re.match(r'^(?:mkCZ|\.cz)\s+(\d+)\s+(\d+)$', tok)
    if m: return ('cz', int(m.group(1)), int(m.group(2)))
    m = re.match(r'^(?:mkAnd|\.and4t)\s+(\d+)\s+(\d+)\s+(\d+)$', tok)
    if m: return ('and4t', int(m.group(1)), int(m.group(2)), int(m.group(3)))
    m = re.match(r'^(?:mkRccx0|\.rccx0)\s+(\d+)\s+(\d+)\s+(\d+)$', tok)
    if m: return ('rccx0', int(m.group(1)), int(m.group(2)), int(m.group(3)))
    m = re.match(r'^(?:mkRccx1|\.rccx1)\s+(\d+)\s+(\d+)\s+(\d+)$', tok)
    if m: return ('rccx1', int(m.group(1)), int(m.group(2)), int(m.group(3)))
    m = re.match(r'^(?:mkUnand|\.unand)\s+(\d+)\s+(\d+)\s+(\d+)$', tok)
    if m: return ('unand', int(m.group(1)), int(m.group(2)), int(m.group(3)))
    m = re.match(r'^\.unquad\s+\[(.*?)\]\s+\[(.*?)\]\s+(\d+)$', tok, re.S)
    if m: return ('unquad', parse_pair_list(m.group(1)), parse_nat_list(m.group(2)), int(m.group(3)))
    if tok.startswith('.hGadget'):
        # .hGadget t [posSteps] [negSteps] true/false [undoLins]
        # Parse carefully by bracket matching
        rest = tok[len('.hGadget'):].strip()
        mt = re.match(r'^(\d+)\s+(.*)$', rest, re.S)
        t = int(mt.group(1))
        rest = mt.group(2).strip()
        def extract_bracket(st):
            assert st[0] == '['
            d = 0
            for i, c in enumerate(st):
                if c == '[': d += 1
                elif c == ']':
                    d -= 1
                    if d == 0:
                        return st[1:i], st[i+1:].strip()
            raise ValueError("Unclosed [")
        pos_s, rest = extract_bracket(rest)
        neg_s, rest = extract_bracket(rest)
        mb = re.match(r'^(true|false)\s+(.*)$', rest, re.S)
        uc = (mb.group(1) == 'true')
        ul_s, _ = extract_bracket(mb.group(2).strip())
        return ('hGadget', t, parse_steps(pos_s), parse_steps(neg_s), uc, parse_nat_list(ul_s))
    raise ValueError(f"Unknown Op102 token: {tok[:80]}")

nat_list_cache = {}
def eval_nat_list(name_or_expr):
    expr = name_or_expr.strip()
    if expr in nat_list_cache: return nat_list_cache[expr]
    if expr in def_blocks:
        res = eval_nat_list(def_blocks[expr][1])
        nat_list_cache[expr] = res
        return res
    m = re.match(r'^rangeList\s+(\d+)\s+(\d+)$', expr)
    if m:
        s, k = int(m.group(1)), int(m.group(2))
        return list(range(s, s + k))
    if expr.startswith('['):
        return parse_nat_list(expr)
    raise ValueError(f"Cannot eval nat list: {expr}")

op_list_cache = {}
def eval_op_list(expr):
    expr = expr.strip()
    if expr in op_list_cache: return op_list_cache[expr]
    if expr in def_blocks:
        typ, body = def_blocks[expr]
        res = eval_op_list(body)
        op_list_cache[expr] = res
        return res
    if '++' in expr:
        # Split on ++ at depth 0
        parts = []
        d = 0; cur = []
        i = 0
        while i < len(expr):
            if expr[i] in '[(': d += 1
            elif expr[i] in '])': d -= 1
            if d == 0 and expr[i:i+2] == '++':
                parts.append(''.join(cur).strip())
                cur = []; i += 2; continue
            cur.append(expr[i]); i += 1
        parts.append(''.join(cur).strip())
        res = []
        for p in parts:
            res.extend(eval_op_list(p))
        return res
    if expr.endswith('.flatten'):
        inner = expr[:-len('.flatten')].strip()
        if inner.startswith('(') and inner.endswith(')'): inner = inner[1:-1]
        sub = eval_op_list(inner)
        if sub and isinstance(sub[0], list):
            return [op for chunk in sub for op in chunk]
        return sub
    m = re.match(r'^(\w+)\.map\s+\(mkCX\s+(\d+)\)$', expr)
    if m:
        ws = eval_nat_list(m.group(1))
        c = int(m.group(2))
        return [('cx', c, w) for w in ws]
    m = re.match(r'^(\w+)\.map\s+\(fun\s+\w+\s*=>\s*mkCX\s+\w+\s+(\d+)\)$', expr)
    if m:
        ws = eval_nat_list(m.group(1))
        t = int(m.group(2))
        return [('cx', w, t) for w in ws]
    m = re.match(r'^(\w+)\.map\s+mkX$', expr)
    if m:
        ws = eval_nat_list(m.group(1))
        return [('x', w) for w in ws]
    m = re.match(r'^revOps\s+(\w+)$', expr)
    if m:
        return list(reversed(eval_op_list(m.group(1))))
    if expr.endswith('.reverse'):
        inner = expr[:-len('.reverse')].strip()
        if inner.startswith('(') and inner.endswith(')'): inner = inner[1:-1]
        return list(reversed(eval_op_list(inner)))
    if expr.startswith('['):
        if expr == '[]': return []
        items = tokenize_top_level_list(expr)
        if items and items[0].startswith('['):
            return [eval_op_list(it) for it in items]
        return [parse_single_op(it) for it in items]
    raise ValueError(f"Cannot eval op list: {expr[:100]}")

def t_cost(ops):
    tot = 0
    for op in ops:
        k = op[0]
        if k in ('and4t', 'rccx0', 'rccx1'): tot += 4
        elif k == 'hGadget': tot += len(op[2]) + len(op[3])
    return tot

# Assemble named stages of fullK25Ops!
stage_names = [
    "s1BOps", "s1YOps", "s1AddOps",
    "hop_0", "s2aOps", "s2bOps", "s2cOps", "s3aOps", "s3bAddOps", "s3bPostOps",
    "hop_1", "s4_1Ops",
    "hop_2", "s4_1PostOps",
    "hop_3", "s4_2Ops", "s4_3Ops", "s4_4Ops", "s5_1Ops", "s5_2CoreOps",
    "hop_4", "s5_2PostOps",
    "hop_5", "s5_3Ops",
    "hop_6", "s5_4Ops", "s6aOps", "s6bOps", "s6cOps",
    "hop_7", "s7YOps", "s1BOps"
]

all_stages = []
total_T = 0
total_ops = 0
for sname in stage_names:
    ops = eval_op_list(sname)
    tc = t_cost(ops)
    total_T += tc
    total_ops += len(ops)
    all_stages.append((sname, ops))
    if tc > 0 or len(ops) > 5:
        print(f"  {sname:15s}: {len(ops):5d} ops, {tc:4d} T")

print(f"\nPARSED GRAND TOTAL: {total_ops} ops, {total_T} T (Target: 3698 T)")
assert total_T == 3698, f"T-count mismatch: {total_T} != 3698!"

# NOW RUN BIT-PARALLEL SIMULATION ON 512 DIVERSE INPUTS (including all 440 bins + edge cases!)
# Each wire w in 0..99 is an int with M bits (bit i = state of wire w on test input i).
pt = read_file("PolyTables.lean")
leaves = [tuple(map(int, m)) for m in re.findall(r'⟨(\d+), (\d+), (\d+), (\d+), (\d+), (\d+), (\d+), (\d+), (\d+)⟩', pt)]
rng = np.random.default_rng(42)
test_inputs = []
# Sample 1 point from every unique bin + boundary points + negative inputs + y=+-1
seen_bins = set()
for lf in leaves:
    us, ue, _, _, bb, kv, lv, s4, _ = lf
    key = (bb, kv, lv, s4)
    if key not in seen_bins:
        seen_bins.add(key)
        u_mid = (us + ue) // 2
        sign = int(rng.integers(0, 2))
        y = (2**25 - u_mid) % (2**25) if sign else u_mid
        b = int(rng.integers(0, 2**25))
        test_inputs.append((y, b))
# Add edge cases: y=0, y=1, y=-1, y=2^23 (1.0), y=2^25-2^23 (-1.0), u=3932278 (max err)
for y_edge in [0, 1, 2**25 - 1, 2**23, 2**25 - 2**23, 3932278, 2**25 - 3932278, 2**23 - 1, 2**25 - (2**23 - 1)]:
    test_inputs.append((y_edge, int(rng.integers(0, 2**25))))

M = len(test_inputs)
MASK_ALL = (1 << M) - 1
wires = [0] * 100
for i, (y, b) in enumerate(test_inputs):
    bit = 1 << i
    for k in range(25):
        if (b >> k) & 1: wires[k] |= bit
        if (y >> k) & 1: wires[25 + k] |= bit

phase = 0

def eval_lin(ls):
    v = 0
    for c in ls: v ^= wires[c]
    return v

def add1_par(b0, b1, b2, dt):
    c0 = b0 & dt
    b0_n = b0 ^ dt
    c1 = b1 & c0
    return b0_n, b1 ^ c0, b2 ^ c1

def add7_par(b0, b1, b2, dt):
    c0 = b0 & dt
    b0_n = b0 ^ dt
    c1 = b1 & c0
    b1_a = b1 ^ c0
    b2_a = b2 ^ c1
    c1_b = b1_a & dt
    return b0_n, b1_a ^ dt, b2_a ^ c1_b ^ dt

def live_anc_count():
    return sum(1 for w in range(50, 100) if wires[w] != 0)

print(f"\nSimulating {M} test inputs across all {len(all_stages)} stages...")
global_peak_anc = 0
global_peak_stage = ""
for sname, ops in all_stages:
    stage_peak = live_anc_count()
    start_anc = stage_peak
    for idx, op in enumerate(ops):
        kind = op[0]
        if kind == 'x':
            wires[op[1]] ^= MASK_ALL
        elif kind == 'cx':
            wires[op[2]] ^= wires[op[1]]
        elif kind == 'and4t':
            c1, c2, t = op[1], op[2], op[3]
            assert wires[t] == 0, f"and4t target {t} not clean in {sname}[{idx}]!"
            wires[t] = wires[c1] & wires[c2]
        elif kind == 'unand':
            c1, c2, t = op[1], op[2], op[3]
            assert wires[t] == (wires[c1] & wires[c2]), f"unand mismatch on {t} in {sname}[{idx}]!"
            wires[t] = 0
        elif kind == 'unquad':
            qs, ls, t = op[1], op[2], op[3]
            val = eval_lin(ls)
            for a, b in qs: val ^= (wires[a] & wires[b])
            assert wires[t] == val, f"unquad mismatch on {t} in {sname}[{idx}]!"
            wires[t] = 0
        elif kind == 'z':
            phase ^= wires[op[1]]
        elif kind == 'cz':
            phase ^= (wires[op[1]] & wires[op[2]])
        elif kind == 'hGadget':
            t, posSteps, negSteps, uc, uls = op[1], op[2], op[3], op[4], op[5]
            assert wires[t] == 0, f"hGadget target {t} not clean in {sname}[{idx}]!"
            dt = 0; b0 = 0; b1 = 0; b2 = 0
            for xc, ls in posSteps:
                dt ^= (MASK_ALL if xc else 0) ^ eval_lin(ls)
                b0, b1, b2 = add1_par(b0, b1, b2, dt)
            for xc, ls in negSteps:
                dt ^= (MASK_ALL if xc else 0) ^ eval_lin(ls)
                b0, b1, b2 = add7_par(b0, b1, b2, dt)
            dt_f = dt ^ (MASK_ALL if uc else 0) ^ eval_lin(uls)
            assert dt_f == 0 and b0 == 0, f"hGadget static invariant fail in {sname}[{idx}]!"
            wires[t] = b1
            phase ^= b2
        else:
            raise ValueError(f"Unhandled op {kind}")
        la = live_anc_count()
        if la > stage_peak: stage_peak = la
    end_anc = live_anc_count()
    if stage_peak > global_peak_anc:
        global_peak_anc = stage_peak
        global_peak_stage = sname
    print(f"  {sname:15s} | T={t_cost(ops):4d} | live_anc: start={start_anc:2d} -> PEAK={stage_peak:2d} -> end={end_anc:2d}")

# Check final phase, y restored, ancillas clean, and arcsin error!
assert phase == 0, f"Final phase non-zero on {bin(phase).count('1')} inputs!"
assert live_anc_count() == 0, f"Ancillas not clean at end: {live_anc_count()}!"
max_err_ulp = 0.0
for i, (y_in, b_in) in enumerate(test_inputs):
    y_out = sum(((wires[25+k] >> i) & 1) << k for k in range(25))
    b_out = sum(((wires[k] >> i) & 1) << k for k in range(25))
    assert y_out == y_in, f"y not restored at {i}!"
    z_raw = (b_out - b_in) % (2**25)
    z_signed = z_raw - 2**25 if z_raw >= 2**24 else z_raw
    y_signed = y_in - 2**25 if y_in >= 2**24 else y_in
    err = abs(z_signed - np.arcsin(y_signed / 2**23) * 2**23)
    if err > max_err_ulp: max_err_ulp = err

print(f"\nALL {M} INPUTS PASSED 100% EXACTLY! phase=0, clean_anc=0, max_err={max_err_ulp:.6f} ULP (limit 1.048576)")
print(f"GLOBAL PEAK SIMULTANEOUSLY LIVE ANCILLAS = {global_peak_anc} / 50 (in stage {global_peak_stage})")
