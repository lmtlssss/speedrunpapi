// cutprove.c: exhaustive proof that the y term of a netlist is on only at table points.
//
// The netlist is given with the index wires cut open: its inputs are
//   x (NX bits), A (n bits), B (n bits), then NC cut wires.
// For x fixed to X0 and for every one of the 2^NC values of the cut wires, the cut wires
// and everything that depends only on them are constants. Constants are propagated, and
// what is left of each output (a function of A and B alone) is multiplied out into a sum
// of products. Every product must be an input point (A,B) of the table whose word has
// that output bit set. Since the real netlist drives the cut wires from (A,B), every
// behaviour of the real netlist at x = X0 is one of the enumerated cases.
//
// usage: cutprove cut.aig NX n NC X0 pol points.bin
//   pol = 1 if the outputs are complemented (the y term is the complement of the output)
//   points.bin: records of 6 u64: A lo, A hi, B lo, B hi, word lo, word hi
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned u; typedef uint64_t w;
typedef struct{w m[4],v[4];}Cube;
typedef struct{Cube*a;size_t n,cap;}Vec;
static void push(Vec*x,const Cube*c){if(x->n==x->cap){x->cap=x->cap?x->cap*2:8;x->a=realloc(x->a,x->cap*sizeof(Cube));}x->a[x->n++]=*c;}
static u rd(FILE *f){u x=0,i=0;int c;while((c=getc(f))&0x80)x|=(u)(c&0x7f)<<(7*i++);return x|((u)c<<(7*i));}
static u M,I,L,O,A;static u*f0,*f1,*g0,*g1,*rep;
static size_t LIMIT=200000;static int overflow=0;
// expand the function of literal lit over the reduced graph (g0,g1 are reduced fanins of kept nodes)
static void ex(u lit,Vec*out){
  for(;;){
    if(out->n>LIMIT){overflow=1;return;}
    u v=lit>>1,n=lit&1;
    if(v==0){if(n){Cube c;memset(&c,0,sizeof c);push(out,&c);}return;}
    if(v<=I){Cube c;memset(&c,0,sizeof c);u i=v-1;c.m[i>>6]|=(w)1<<(i&63);if(!n)c.v[i>>6]|=(w)1<<(i&63);push(out,&c);return;}
    if(n){ex(g0[v]^1,out);lit=g1[v]^1;continue;}
    Vec x={0,0,0},y={0,0,0};ex(g0[v],&x);ex(g1[v],&y);
    for(size_t i=0;i<x.n&&!overflow;i++)for(size_t j=0;j<y.n;j++){Cube c;int bad=0;
      for(int k=0;k<4;k++){if((x.a[i].m[k]&y.a[j].m[k])&(x.a[i].v[k]^y.a[j].v[k])){bad=1;break;}c.m[k]=x.a[i].m[k]|y.a[j].m[k];c.v[k]=x.a[i].v[k]|y.a[j].v[k];}
      if(!bad)push(out,&c);if(out->n>LIMIT){overflow=1;break;}}
    free(x.a);free(y.a);return;
  }
}
// table of points
typedef struct{w k[4];w p[2];int used;}Ent;
static Ent*tab;static size_t tsz;
static size_t hsh(const w*k){w h=k[0]*0x9e3779b97f4a7c15ULL^k[1]*0xc2b2ae3d27d4eb4fULL^k[2]*0x165667b19e3779f9ULL^k[3]*0x27d4eb2f165667c5ULL;h^=h>>29;return (size_t)(h%tsz);}
static Ent*find(const w*k){size_t i=hsh(k);while(tab[i].used){if(!memcmp(tab[i].k,k,32))return &tab[i];i=(i+1)%tsz;}return 0;}
static void ins(const w*k,const w*p){size_t i=hsh(k);while(tab[i].used)i=(i+1)%tsz;memcpy(tab[i].k,k,32);tab[i].p[0]=p[0];tab[i].p[1]=p[1];tab[i].used=1;}
static int getbit(const w*a,u i){return (a[i>>6]>>(i&63))&1;}
static void setbit(w*a,u i){a[i>>6]|=(w)1<<(i&63);}
int main(int argc,char**argv){
  if(argc<8){fprintf(stderr,"usage\n");return 1;}
  u NX=atoi(argv[2]),n=atoi(argv[3]),NC=atoi(argv[4]);w X0=strtoull(argv[5],0,0);int pol=atoi(argv[6]);
  FILE*f=fopen(argv[1],"rb");
  if(!f||fscanf(f,"aig %u %u %u %u %u\n",&M,&I,&L,&O,&A)!=5)return 1;
  if(I!=NX+2*n+NC||O!=n){fprintf(stderr,"unexpected interface: %u inputs %u outputs\n",I,O);return 1;}
  u*out=malloc(O*sizeof(u));char buf[64];
  for(u i=0;i<O;i++){fgets(buf,64,f);out[i]=strtoul(buf,0,10);}
  f0=malloc((M+1)*sizeof(u));f1=malloc((M+1)*sizeof(u));g0=malloc((M+1)*sizeof(u));g1=malloc((M+1)*sizeof(u));rep=malloc((M+1)*sizeof(u));
  unsigned char*sym=calloc(M+1,1);
  for(u i=NX;i<NX+2*n;i++)sym[i+1]=1;
  u ns=0;
  for(u k=0;k<A;k++){u v=I+1+k;u lhs=2*v;u d0=rd(f),d1=rd(f);f0[v]=lhs-d0;f1[v]=f0[v]-d1;sym[v]=sym[f0[v]>>1]|sym[f1[v]>>1];ns+=sym[v];}
  fclose(f);
  u*sl=malloc((ns+1)*sizeof(u));u q=0;for(u v=I+1;v<=M;v++)if(sym[v])sl[q++]=v;
  // points
  FILE*p=fopen(argv[7],"rb");fseek(p,0,SEEK_END);size_t np=ftell(p)/48;fseek(p,0,SEEK_SET);
  tsz=np*3+17;tab=calloc(tsz,sizeof(Ent));
  for(size_t i=0;i<np;i++){w r[6];if(fread(r,8,6,p)!=6)return 1;w k[4]={r[0],r[1],r[2],r[3]};ins(k,r+4);}
  fclose(p);
  w*val=malloc((M+1)*sizeof(w));val[0]=0;
  unsigned long long cases=0,products=0,partial=0,maxp=0,fails=0;
  for(w base=0;base<((w)1<<NC);base+=64){
    for(u i=0;i<I;i++){w x=0;
      if(i<NX)x=((X0>>i)&1)?~(w)0:0;
      else if(i>=NX+2*n){u c=i-NX-2*n;if(c<6){static const w pat[6]={0xAAAAAAAAAAAAAAAAULL,0xCCCCCCCCCCCCCCCCULL,0xF0F0F0F0F0F0F0F0ULL,0xFF00FF00FF00FF00ULL,0xFFFF0000FFFF0000ULL,0xFFFFFFFF00000000ULL};x=pat[c];}else x=((base>>c)&1)?~(w)0:0;}
      val[i+1]=x;}
    for(u v=I+1;v<=M;v++)if(!sym[v]){u a=f0[v],c=f1[v];val[v]=(val[a>>1]^-(w)(a&1))&(val[c>>1]^-(w)(c&1));}
    int nb=NC<6?(1<<NC):64;
    for(int b=0;b<nb;b++){
      // literal resolution: constant nodes give 0/1, symbolic inputs give themselves, symbolic nodes rep[]
      #define RES(e) (sym[(e)>>1]?(((e)>>1)<=I?(e):(rep[(e)>>1]^((e)&1))):(u)((((val[(e)>>1]>>b)&1)^((e)&1))))
      for(u k=0;k<ns;k++){u v=sl[k];u a=RES(f0[v]),c=RES(f1[v]);
        if(a==0||c==0||a==(c^1))rep[v]=0;else if(a==1)rep[v]=c;else if(c==1||a==c)rep[v]=a;else{rep[v]=2*v;g0[v]=a;g1[v]=c;}}
      cases++;
      for(u o=0;o<O;o++){
        u e=out[o]^(u)pol;u l=RES(e);
        if(l==0)continue;
        if(l==1){fails++;if(fails<10)fprintf(stderr,"cut value %llu: output %u is on for every (A,B)\n",(unsigned long long)(base+b),o);continue;}
        Vec x={0,0,0};overflow=0;ex(l,&x);
        if(overflow){fails++;fprintf(stderr,"cut value %llu output %u: expansion too large\n",(unsigned long long)(base+b),o);free(x.a);continue;}
        if(x.n>maxp)maxp=x.n;
        for(size_t i=0;i<x.n;i++){Cube*c=&x.a[i];products++;
          u freeb[16];int nf=0,bad=0;
          for(u j=0;j<NX+2*n+NC;j++){int inm=getbit(c->m,j);
            if(j<NX||j>=NX+2*n){if(inm)bad=1;}
            else if(!inm){if(nf<16)freeb[nf]=j;nf++;}}
          if(bad||nf>12){fails++;if(fails<10)fprintf(stderr,"cut value %llu output %u: product with %d free bits\n",(unsigned long long)(base+b),o,nf);continue;}
          if(nf)partial++;
          for(u comb=0;comb<(1u<<nf);comb++){
            w k[4]={0,0,0,0};
            for(u j=0;j<n;j++){int bit=getbit(c->v,NX+j);for(int z=0;z<nf;z++)if(freeb[z]==NX+j)bit=(comb>>z)&1;if(bit)k[j>>6]|=(w)1<<(j&63);}
            for(u j=0;j<n;j++){int bit=getbit(c->v,NX+n+j);for(int z=0;z<nf;z++)if(freeb[z]==NX+n+j)bit=(comb>>z)&1;if(bit)k[2+(j>>6)]|=(w)1<<(j&63);}
            Ent*en=find(k);
            if(!en||!((en->p[o>>6]>>(o&63))&1)){fails++;if(fails<10)fprintf(stderr,"cut value %llu output %u: on at a point outside the table: A=%016llx%016llx B=%016llx%016llx\n",(unsigned long long)(base+b),o,(unsigned long long)k[1],(unsigned long long)k[0],(unsigned long long)k[3],(unsigned long long)k[2]);}
          }
        }
        free(x.a);
      }
    }
  }
  printf("cut values enumerated: %llu\nproducts checked: %llu (largest sum %llu, %llu with free bits)\nfailures: %llu\n",cases,products,maxp,partial,fails);
  (void)setbit;
  return fails?2:0;
}
