// psim.c: simulate a binary AIGER file on a list of input patterns.
// usage: psim file.aig patterns.txt out.txt
// patterns.txt: one hex number per line, bit i = input i.
// out.txt:      one hex number per line, bit o = output o.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned u; typedef uint64_t w;
static u rd(FILE *f){u x=0,i=0;int c;while((c=getc(f))&0x80)x|=(u)(c&0x7f)<<(7*i++);return x|((u)c<<(7*i));}
static int hv(int c){return c<='9'?c-'0':(c|32)-'a'+10;}
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"rb");u M,I,L,O,A;
  if(!f||fscanf(f,"aig %u %u %u %u %u\n",&M,&I,&L,&O,&A)!=5)return 1;
  u*out=malloc(O*sizeof(u));char buf[1024];
  for(u i=0;i<O;i++){fgets(buf,64,f);out[i]=strtoul(buf,0,10);}
  u*f0=malloc((M+1)*sizeof(u)),*f1=malloc((M+1)*sizeof(u));
  for(u k=0;k<A;k++){u v=I+1+k;u lhs=2*v;u d0=rd(f),d1=rd(f);f0[v]=lhs-d0;f1[v]=f0[v]-d1;}
  fclose(f);
  w*val=malloc((M+1)*sizeof(w));val[0]=0;
  FILE*p=fopen(argv[2],"r"),*g=fopen(argv[3],"w");
  w*ow=malloc(O*sizeof(w));int done=0;
  while(!done){
    for(u i=1;i<=I;i++)val[i]=0;
    int n=0;
    for(;n<64;n++){
      if(!fgets(buf,sizeof buf,p)){done=1;break;}
      int len=strlen(buf);while(len&&(buf[len-1]=='\n'||buf[len-1]=='\r'||buf[len-1]==' '))len--;
      if(!len){n--;continue;}
      for(int k=0;k<len;k++){int d=hv(buf[len-1-k]);for(int b=0;b<4;b++){u i=4*k+b;if(i<I&&((d>>b)&1))val[i+1]|=(w)1<<n;}}
    }
    if(n==0)break;
    for(u v=I+1;v<=M;v++){u a=f0[v],c=f1[v];val[v]=(val[a>>1]^-(w)(a&1))&(val[c>>1]^-(w)(c&1));}
    for(u o=0;o<O;o++)ow[o]=val[out[o]>>1]^-(w)(out[o]&1);
    int nd=(O+3)/4;
    for(int q=0;q<n;q++){
      for(int k=nd-1;k>=0;k--){int d=0;for(int b=0;b<4;b++){u o=4*k+b;if(o<O&&((ow[o]>>q)&1))d|=1<<b;}fputc("0123456789abcdef"[d],g);}
      fputc('\n',g);
    }
  }
  fclose(g);return 0;
}
