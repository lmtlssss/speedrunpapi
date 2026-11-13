// xsim.c: simulate a binary AIGER file on all 2^NX assignments of inputs 0..NX-1 with every
// other input held at 1. Nodes that do not depend on inputs 0..NX-1 are evaluated once.
// usage: xsim file.aig NX out.bin
// out.bin: one 64-bit word per (block, output); bit p of block b is the output at x = 64*b + p.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned u; typedef uint64_t w;
static u rd(FILE *f){u x=0,i=0;int c;while((c=getc(f))&0x80)x|=(u)(c&0x7f)<<(7*i++);return x|((u)c<<(7*i));}
int main(int argc,char**argv){
  if(argc<4)return 1;
  u NX=atoi(argv[2]);
  FILE*f=fopen(argv[1],"rb");u M,I,L,O,A;
  if(!f||fscanf(f,"aig %u %u %u %u %u\n",&M,&I,&L,&O,&A)!=5)return 1;
  u*out=malloc(O*sizeof(u));char buf[64];
  for(u i=0;i<O;i++){fgets(buf,64,f);out[i]=strtoul(buf,0,10);}
  u*f0=malloc((M+1)*sizeof(u)),*f1=malloc((M+1)*sizeof(u));
  unsigned char*dep=calloc(M+1,1);w*val=malloc((M+1)*sizeof(w));val[0]=0;
  for(u i=1;i<=I;i++){dep[i]=(i-1<NX);val[i]=~(w)0;}
  u nd=0;
  for(u k=0;k<A;k++){u v=I+1+k;u lhs=2*v;u d0=rd(f),d1=rd(f);f0[v]=lhs-d0;f1[v]=f0[v]-d1;
    dep[v]=dep[f0[v]>>1]|dep[f1[v]>>1];nd+=dep[v];
    if(!dep[v]){u a=f0[v],c=f1[v];val[v]=(val[a>>1]^-(w)(a&1))&(val[c>>1]^-(w)(c&1));}}
  fclose(f);
  u*dl=malloc((nd+1)*sizeof(u));u q=0;for(u v=I+1;v<=M;v++)if(dep[v])dl[q++]=v;
  static const w pat[6]={0xAAAAAAAAAAAAAAAAULL,0xCCCCCCCCCCCCCCCCULL,0xF0F0F0F0F0F0F0F0ULL,0xFF00FF00FF00FF00ULL,0xFFFF0000FFFF0000ULL,0xFFFFFFFF00000000ULL};
  FILE*g=fopen(argv[3],"wb");u nb=NX>6?1u<<(NX-6):1;w*ow=malloc(O*sizeof(w));
  for(u b=0;b<nb;b++){
    for(u i=0;i<NX;i++)val[i+1]=i<6?pat[i]:(((b>>(i-6))&1)?~(w)0:0);
    for(u k=0;k<nd;k++){u v=dl[k];u a=f0[v],c=f1[v];val[v]=(val[a>>1]^-(w)(a&1))&(val[c>>1]^-(w)(c&1));}
    for(u o=0;o<O;o++)ow[o]=val[out[o]>>1]^-(w)(out[o]&1);
    fwrite(ow,sizeof(w),O,g);
  }
  fclose(g);return 0;
}
