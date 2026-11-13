// sop.c: exact sum-of-products expansion of every output of a binary AIGER file.
//
// Every AIG node is an AND of two edges; a complemented edge to an AND is an OR of
// the negated fanins (De Morgan). Expanding AND as a cross product and OR as a union
// gives, for each output, a list of products of input literals whose union is exactly
// the output function. For each output the polarity (output or its complement) with
// the smaller expansion is used and recorded.
//
// usage: sop file.aig out.bin [limit]
// out.bin: header "SOP1", u32 I, u32 O; per output: u32 polarity (1 = the list is the
//          complement of the output), u32 count, then count records of 6 u64:
//          mask[3], val[3]  (bit i = input i; val is the required value where mask is set)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned u; typedef uint64_t w;
typedef struct{w m[3],v[3];}Cube;
typedef struct{Cube*a;size_t n,cap;}Vec;
static void push(Vec*x,const Cube*c){if(x->n==x->cap){x->cap=x->cap?x->cap*2:8;x->a=realloc(x->a,x->cap*sizeof(Cube));}x->a[x->n++]=*c;}
static u rd(FILE *f){u x=0,i=0;int c;while((c=getc(f))&0x80)x|=(u)(c&0x7f)<<(7*i++);return x|((u)c<<(7*i));}
static u M,I,L,O,A;static u*f0,*f1;static double*pos,*neg;
static void ex(u lit,Vec*out){
  for(;;){
    u v=lit>>1,n=lit&1;
    if(v==0){if(n){Cube c;memset(&c,0,sizeof c);push(out,&c);}return;}
    if(v<=I){Cube c;memset(&c,0,sizeof c);u i=v-1;c.m[i>>6]|=(w)1<<(i&63);if(!n)c.v[i>>6]|=(w)1<<(i&63);push(out,&c);return;}
    if(n){ // OR of negated fanins: recurse on the smaller side, loop on the other
      u a=f0[v]^1,b=f1[v]^1;ex(a,out);lit=b;continue;}
    Vec x={0,0,0},y={0,0,0};ex(f0[v],&x);ex(f1[v],&y);
    for(size_t i=0;i<x.n;i++)for(size_t j=0;j<y.n;j++){Cube c;int bad=0;
      for(int k=0;k<3;k++){if((x.a[i].m[k]&y.a[j].m[k])&(x.a[i].v[k]^y.a[j].v[k])){bad=1;break;}c.m[k]=x.a[i].m[k]|y.a[j].m[k];c.v[k]=x.a[i].v[k]|y.a[j].v[k];}
      if(!bad)push(out,&c);}
    free(x.a);free(y.a);return;
  }
}
int main(int argc,char**argv){
  double limit=argc>3?atof(argv[3]):5e6;
  FILE*f=fopen(argv[1],"rb");
  if(!f||fscanf(f,"aig %u %u %u %u %u\n",&M,&I,&L,&O,&A)!=5)return 1;
  u*out=malloc(O*sizeof(u));char buf[64];
  for(u i=0;i<O;i++){fgets(buf,64,f);out[i]=strtoul(buf,0,10);}
  f0=malloc((M+1)*sizeof(u));f1=malloc((M+1)*sizeof(u));
  pos=malloc((M+1)*sizeof(double));neg=malloc((M+1)*sizeof(double));
  pos[0]=0;neg[0]=1;for(u i=1;i<=I;i++)pos[i]=neg[i]=1;
  for(u k=0;k<A;k++){u v=I+1+k;u lhs=2*v;u d0=rd(f),d1=rd(f);u r0=lhs-d0,r1=r0-d1;f0[v]=r0;f1[v]=r1;
    double p0=(r0&1)?neg[r0>>1]:pos[r0>>1],p1=(r1&1)?neg[r1>>1]:pos[r1>>1];
    double n0=(r0&1)?pos[r0>>1]:neg[r0>>1],n1=(r1&1)?pos[r1>>1]:neg[r1>>1];
    pos[v]=p0*p1;neg[v]=n0+n1;}
  fclose(f);
  FILE*g=fopen(argv[2],"wb");fwrite("SOP1",1,4,g);fwrite(&I,4,1,g);fwrite(&O,4,1,g);
  double tot=0;
  for(u o=0;o<O;o++){
    u lit=out[o];double asis=(lit&1)?neg[lit>>1]:pos[lit>>1],comp=(lit&1)?pos[lit>>1]:neg[lit>>1];
    u pol=comp<asis;double c=pol?comp:asis;
    if(c>limit){fprintf(stderr,"output %u: expansion %.3g exceeds limit\n",o,c);return 2;}
    Vec x={0,0,0};ex(lit^pol,&x);
    u n=(u)x.n;fwrite(&pol,4,1,g);fwrite(&n,4,1,g);fwrite(x.a,sizeof(Cube),x.n,g);free(x.a);tot+=n;
  }
  fclose(g);fprintf(stderr,"%s: %u outputs, %.0f products\n",argv[1],O,tot);return 0;
}
