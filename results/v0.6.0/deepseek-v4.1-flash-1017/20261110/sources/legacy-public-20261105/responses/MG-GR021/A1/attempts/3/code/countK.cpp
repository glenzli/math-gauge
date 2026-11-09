#include <bits/stdc++.h>
using namespace std;
int L;
inline unsigned mul(unsigned a,unsigned b){
    unsigned c=0;
    for(int i=0;i<L;i++) if((a>>i)&1){
        c ^= (b<<i);
    }
    return c & ((1u<<L)-1);
}
int main(int argc,char**argv){
    int n=atoi(argv[1]); int M=atoi(argv[2]); L=2*M-2;
    int N=1<<L; long long total=1; for(int i=0;i<n*n;i++) total*=N;
    cerr<<"N="<<N<<" total="<<total<<"\n";
    // precompute mul table N*N if manageable
    vector<unsigned> els(N); for(int i=0;i<N;i++) els[i]=i;
    vector<vector<unsigned>> mt(N, vector<unsigned>(N));
    for(int a=0;a<N;a++)for(int b=0;b<N;b++) mt[a][b]=mul(a,b);
    unsigned mask=N-1;
    long long cnt=0;
    if(n==1){
      for(int x=0;x<N;x++){
        unsigned F=x^x; // x+x^T=0 since scalar commute, but in char2 2x? Wait X+X^T=2x = theta^2*x? Need actual ring multiplication by 2 == theta^2 shift.
        // For scalar, X+X^T=2x = theta^2 * x in R.
        unsigned sh=(x<<2)&mask;
        F=sh ^ ((mt[x][x]<<2)&mask);
        if(F==0) cnt++;
      }
    } else if(n==2){
      for(int a=0;a<N;a++)for(int b=0;b<N;b++)for(int c=0;c<N;c++)for(int d=0;d<N;d++){
        unsigned X[2][2]={{ (unsigned)a,(unsigned)b},{(unsigned)c,(unsigned)d}};
        bool ok=true;
        for(int i=0;i<2&&ok;i++)for(int j=0;j<2&&ok;j++){
          unsigned s=X[i][j]^X[j][i];
          for(int k=0;k<2;k++){
            unsigned prod=mt[X[k][i]][X[k][j]];
            s ^= (prod<<2)&mask;
          }
          if(s!=0) ok=false;
        }
        if(ok)cnt++;
      }
    }
    cout<<"n="<<n<<" M="<<M<<" L="<<L<<" cnt="<<cnt<<"\n";
}
