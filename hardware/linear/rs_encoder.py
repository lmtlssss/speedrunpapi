"""RS(544,514) over GF(2^10), field polynomial x^10 + x^3 + 1, generator roots a^0 .. a^29.
Writes the encoder register update for PAR symbols per clock as a GF(2) matrix: one hex row per line,
over (300 state bits, then 10 * PAR data bits).  usage: rs_encoder.py PAR > rs.rows"""
import sys
PRIM=0x409; M=10; T2=30
def gmul(a,b):
    r=0
    while b:
        if b&1: r^=a
        b>>=1; a<<=1
        if a>>M: a^=PRIM
    return r
exp=[1]
for i in range(1,1023): exp.append(gmul(exp[-1],2))
g=[1]
for i in range(T2):
    r=exp[i]; ng=[0]*(len(g)+1)
    for j,c in enumerate(g):
        ng[j]^=gmul(c,r); ng[j+1]^=c
    g=ng
assert len(g)==T2+1 and g[-1]==1
def const_rows(c):
    # multiply-by-c as 10 masks over the 10 input bits
    cols=[gmul(c,1<<j) for j in range(M)]
    return [sum(((cols[j]>>i)&1)<<j for j in range(M)) for i in range(M)]
def step(state, din):
    # state: list of 30 symbols, each a list of 10 masks; din: 10 masks. LFSR division by g.
    fb=[state[T2-1][i]^din[i] for i in range(M)]
    ns=[]
    for k in range(T2):
        cr=const_rows(g[k])
        term=[0]*M
        for i in range(M):
            m=cr[i]; v=0; j=0
            while m:
                if m&1: v^=fb[j]
                m>>=1; j+=1
            term[i]=v
        prev=state[k-1] if k else [0]*M
        ns.append([prev[i]^term[i] for i in range(M)])
    return ns
def rows(par):
    nin=300+10*par
    state=[[1<<(10*k+i) for i in range(M)] for k in range(T2)]
    for p in range(par):
        din=[1<<(300+10*p+i) for i in range(M)]
        state=step(state,din)
    return [state[k][i] for k in range(T2) for i in range(M)], nin
if __name__ == "__main__":
    r, nin = rows(int(sys.argv[1]))
    sys.stdout.write("\n".join("%x" % m for m in r) + "\n")
