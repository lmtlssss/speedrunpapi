# Placed-and-routed timing on Lattice ECP5 (LUT4 + carry chains), open flow: Yosys synth_ecp5 + nextpnr-ecp5.
# Run from any directory: python3 ecp5_place_route.py   (writes pnr-out/)
import sys, os, re, json, subprocess
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from threshold_compiler import compile_threshold
from independent_threshold_checker import verify, parse_blif
env=dict(os.environ)   # needs yosys and nextpnr-ecp5 on PATH (oss-cad-suite)
def lutv(raw, n):
    ins,outs,tabs=parse_blif(raw)
    L=["module core(input [%d:0] A, output maj);"%(n-1)]
    wires=[o for o in tabs if o!="maj"]
    for i in range(0,len(wires),16): L.append("  wire "+", ".join(wires[i:i+16])+";")
    for idx,(o,(fan,on)) in enumerate(tabs.items()):
        k=len(fan); init=0
        for r in on: init|=1<<sum(1<<i for i,ch in enumerate(r) if ch=="1")
        full=0
        for row in range(16):
            if (init>>(row&((1<<k)-1)))&1: full|=1<<row
        pins=fan+["1'b0"]*(4-k)
        L.append("  (* keep *) LUT4 #(.INIT(16'h%04X)) u%d (.A(%s), .B(%s), .C(%s), .D(%s), .Z(%s));"%(full,idx,pins[0],pins[1],pins[2],pins[3],o))
    L.append("endmodule"); return "\n".join(L)+"\n"
def wrap(n):
    return ("module top(input clk, input din, output reg q);\n  reg [%d:0] sr; wire m;\n  always @(posedge clk) begin sr <= {sr[%d:0], din}; q <= m; end\n  core c(.A(sr), .maj(m));\nendmodule\n"%(n-1,n-2))
def rtl(n,T):
    return ("module core(input [%d:0] A, output maj);\n  integer i; reg [10:0] c;\n  always @* begin c=0; for(i=0;i<%d;i=i+1) c=c+A[i]; end\n  assign maj = (c >= %d);\nendmodule\n"%(n-1,n,T))
def flow(name, core, n, seeds=(1,2,3)):
    d='pnr-out/'+name; os.makedirs(d,exist_ok=True)
    open(d+'/d.v','w').write(core+wrap(n))
    r=subprocess.run(["yosys","-q","-p","read_verilog %s/d.v; synth_ecp5 -top top -json %s/d.json"%(d,d)],capture_output=True,text=True,env=env)
    if r.returncode: return {"error":r.stderr[-300:]}
    best=None; util=None
    for s in seeds:
        p=subprocess.run(["nextpnr-ecp5","--85k","--package","CABGA381","--json",d+"/d.json","--freq","200","--seed",str(s),"--timing-allow-fail"],capture_output=True,text=True,env=env)
        log=p.stderr+p.stdout
        f=re.findall(r"Max frequency for clock\s+'\S+':\s+([\d.]+) MHz",log)
        u=re.search(r"TRELLIS_COMB:\s+(\d+)/",log)
        if u: util=int(u.group(1))
        if f:
            fm=float(f[-1]); best=fm if best is None or fm>best else best
    return {"fmax_mhz":best,"period_ns":round(1000/best,3) if best else None,"comb_cells":util}
rows=[]
for n,T in ((36,32),(64,56),(127,64),(255,160)):
    row={"n":n,"T":T,"baseline_rtl":flow("b%d"%n, rtl(n,T), n)}
    for obj in ("size","depth"):
        raw,cert=compile_threshold(n,T,k=4,objective=obj,wallace=2)
        assert verify(raw,cert)["ok"]
        row["colony_k4_"+obj]=dict(flow("c%d%s"%(n,obj), lutv(raw,n), n), luts=cert["lut_count"], levels=cert["levels"])
    rows.append(row); print(json.dumps(row)); sys.stdout.flush()
json.dump(rows,open('pnr-out/ecp5.json','w'),indent=1)
