#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int L; uint32_t mask;
static inline uint32_t mul(uint32_t a,uint32_t b){uint32_t c=0; for(int i=0;i<L;i++) if((a>>i)&1) c ^= (b<<i); return c&mask;}
int main(int argc,char**argv){int n=2,M=atoi(argv[1]); L=2*M-2; int N=1<<L; mask=N-1;
 uint32_t *mt=malloc((size_t)N*N*sizeof(uint32_t));
 for(int a=0;a<N;a++)for(int b=0;b<N;b++) mt[(size_t)a*N+b]=mul(a,b);
 int Rbits=2*(M-1)-2; // reduce to M-1: L'=2(M-1)-2, entries mask
 uint32_t rmask=(1u<<Rbits)-1; int RN=1<<Rbits;
 char *seen=calloc((size_t)RN*RN*RN*RN,1); long long cnt=0; int reds=0;
 for(int a=0;a<N;a++)for(int b=0;b<N;b++)for(int c=0;c<N;c++)for(int d=0;d<N;d++){uint32_t X[2][2]={{a,b},{c,d}}; int ok=1; for(int i=0;i<2&&ok;i++)for(int j=0;j<2&&ok;j++){uint32_t s=X[i][j]^X[j][i]; for(int k=0;k<2;k++) s ^= (mt[(size_t)X[k][i]*N+X[k][j]]<<2)&mask; if(s) ok=0;} if(ok){cnt++; uint32_t aa=a&rmask,bb=b&rmask,cc=c&rmask,dd=d&rmask; size_t idx=(((size_t)aa*RN+bb)*RN+cc)*RN+dd; if(!seen[idx]){seen[idx]=1;reds++;}}}
 printf("M=%d sols=%lld reductions=%d\n",M,cnt,reds);
}
