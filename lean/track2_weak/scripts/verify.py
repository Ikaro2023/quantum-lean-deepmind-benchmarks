"""Build every new source from a clean module root, then replay the exact emitted objects."""
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from collections import Counter
from datetime import datetime, timezone
import argparse
import ctypes
import json
import os
from pathlib import Path
import re
import time
from lean_tools import BIN, LEAN, PROJECT, RECEIPTS, REPO, digest, environment, record

IMPORT_RE=re.compile(r"^(?:(?:public|private) )?import (?:all )?((?:Track2Weak|Track2Grover)\.[\w.]+)",re.M)
PARTS=(".olean",".olean.private",".olean.server",".ir",".ir.sig")

def code_only(s):
    # Lean comments can nest and strings can contain quoted identifiers or comment delimiters.
    ans=[]; level=0; i=0; in_string=False
    while i<len(s):
        c=s[i]; pair=s[i:i+2]
        if in_string:
            if c=="\\": i+=2;continue
            if c=='"':in_string=False
            ans.append(" ");i+=1;continue
        if level:
            if pair=="/-":level+=1;i+=2;continue
            if pair=="-/":level-=1;i+=2;continue
            ans.append("\n" if c=="\n" else " ");i+=1;continue
        if pair=="--":
            j=s.find("\n",i);i=len(s) if j<0 else j;continue
        if pair=="/-":level=1;ans.append(" ");i+=2;continue
        if c=='"':in_string=True;ans.append(" ");i+=1;continue
        ans.append(c);i+=1
    if level or in_string:raise ValueError("Unclosed comment or string")
    return "".join(ans)

def source_info(path):
    src=code_only(path.read_text(encoding="utf-8"))
    forbidden=re.findall(r"(?<![\w'])(?:sorry|admit|native_decide|axiom)(?![\w'])",src)
    if forbidden: raise ValueError((path,forbidden))
    return dict(source_sha256=digest(path),local_imports=sorted(set(IMPORT_RE.findall(src))))

class Mem(ctypes.Structure):
    _fields_=[("length",ctypes.c_ulong),("load",ctypes.c_ulong)]+[(x,ctypes.c_ulonglong) for x in ("total","free","limit","commit","address","free_address","ext")]

def capacity(max_jobs):
    if os.name!="nt": return max_jobs
    s=Mem();s.length=ctypes.sizeof(s)
    if not ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(s)):return 1
    if s.commit<4*2**30:return 0
    if s.commit<11*2**30 or s.free<4*2**30:return 1
    return max_jobs

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("-j",type=int,default=2)
    args=parser.parse_args()
    srcdir=LEAN/"Track2Weak"
    sources={"Track2Weak."+p.stem:p for p in srcdir.glob("*.lean")}
    info={n:source_info(p) for n,p in sources.items()}
    tag=datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    fresh=srcdir/"verification"/tag
    (fresh/"Track2Weak").mkdir(parents=True)
    env=environment()
    vendor=srcdir/"vendor"
    if not (vendor/"Track2Grover/Engine/Rk128kEngine.olean").is_file():
        raise RuntimeError("Run package_sources.py before the standalone replay")
    env["LEAN_PATH"]=os.pathsep.join([str(fresh),str(vendor)]+[p for p in env["LEAN_PATH"].split(os.pathsep) if Path(p) not in (LEAN,REPO,vendor)])
    def compile_one(n):
        inp=sources[n]
        olean=fresh/"Track2Weak"/inp.with_suffix(".olean").name
        for attempt in range(3):
            rc,log=record(n+"_clean_lean",[BIN/"lean.exe","-j1","-R",LEAN,"-o",olean,inp],cwd=fresh,env=env)
            if not rc:break
            msg=log.read_text(encoding="utf-8",errors="replace").lower()
            if not any(s in msg for s in ("failed to read file","not enough memory","out of memory","failed to map","page file","failed to read","cannot allocate","insufficient system resources")):break
            time.sleep(5*(attempt+1))
        if rc or digest(inp)!=info[n]["source_sha256"]: raise RuntimeError(str(log))
        obj={suffix:digest(olean.with_suffix(suffix)) for suffix in PARTS if olean.with_suffix(suffix).is_file()}
        return dict(lean_exit=rc,lean_log=log.name,objects=obj)
    graph={n:{d for d in v["local_imports"] if d.startswith("Track2Weak.")} for n,v in info.items()}
    done=set();live={}; started=time.monotonic()
    with ThreadPoolExecutor(args.j) as pool:
        while graph or live:
            ready=sorted(n for n,ds in graph.items() if ds<=done)
            room=capacity(args.j)
            for n in ready[:max(0,room-len(live))]:
                live[pool.submit(compile_one,n)]=n
                del graph[n]
            if not live:
                if not ready:raise RuntimeError(graph)
                time.sleep(3);continue
            finished,_=wait(live,return_when=FIRST_COMPLETED)
            for f in finished:
                n=live.pop(f);info[n].update(f.result());done.add(n)
                (fresh/(n+".json")).write_text(json.dumps(info[n],indent=2),encoding="utf-8")
                print(f"{len(done)}/{len(info)} {n}",flush=True)
    rc,log=record("clean_all_checker",[BIN/"leanchecker.exe","--verbose","Track2Weak"],cwd=fresh,env=env)
    lines=log.read_text(encoding="utf-8").splitlines()
    seen=[s.removeprefix("replaying ") for s in lines if s.startswith("replaying ")]
    if rc or Counter(seen)!=Counter(info.keys()):raise RuntimeError(str(log))
    for n,p in sources.items():
        if info[n]["source_sha256"]!=digest(p):raise RuntimeError(f"Source changed: {p}")
        for suff,sha in info[n]["objects"].items():
            if digest((fresh/"Track2Weak"/p.name).with_suffix(suff))!=sha:raise RuntimeError(n)
        info[n].update(checker_exit=0,checker_log=log.name)
    out=dict(start_utc=tag,elapsed_seconds=round(time.monotonic()-started,2),fresh_root=str(fresh),
             source_module_count=len(info),checker_modules=seen,checker_exit=rc,
             binary_sha256={x:digest(BIN/x) for x in ("lean.exe","leanchecker.exe")},
             forbidden_source_tokens={"sorry":0,"admit":0,"native_decide":0,"axiom":0},modules=info)
    (PROJECT/"verification.json").write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8")
    print("Verified",len(info),"modules",flush=True)

if __name__=="__main__":main()
