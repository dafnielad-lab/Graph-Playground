#include <bits/stdc++.h>
using namespace std;
int n; int adj[8];
int pairIdx[8][8];
vector<vector<int>> cells; int perm[8]; // perm[pos]=vertex
unsigned best; long long cnt;
void rec(int ci, int pos){
  if(ci==(int)cells.size()){
    unsigned code=0;
    for(int i=0;i<n;i++)for(int j=i+1;j<n;j++) if(adj[perm[i]]>>perm[j]&1) code|=1u<<pairIdx[i][j];
    if(code<best){best=code;cnt=1;} else if(code==best)cnt++;
    return;
  }
  vector<int> c=cells[ci]; sort(c.begin(),c.end());
  do{ for(size_t k=0;k<c.size();k++)perm[pos+k]=c[k]; rec(ci+1,pos+c.size()); }while(next_permutation(c.begin(),c.end()));
}
pair<unsigned,long long> canon(){
  vector<int> col(n);
  for(int i=0;i<n;i++)col[i]=__builtin_popcount(adj[i]);
  for(int r=0;r<4;r++){
    vector<pair<vector<int>,int>> sig(n);
    for(int i=0;i<n;i++){vector<int> s; for(int j=0;j<n;j++)if(adj[i]>>j&1)s.push_back(col[j]); sort(s.begin(),s.end()); s.insert(s.begin(),col[i]); sig[i]={s,i};}
    vector<vector<int>> u; for(auto&p:sig)u.push_back(p.first); sort(u.begin(),u.end()); u.erase(unique(u.begin(),u.end()),u.end());
    for(int i=0;i<n;i++)col[i]=lower_bound(u.begin(),u.end(),sig[i].first)-u.begin();
  }
  map<int,vector<int>> m; for(int i=0;i<n;i++)m[col[i]].push_back(i);
  cells.clear(); for(auto&p:m)cells.push_back(p.second);
  best=~0u;cnt=0; rec(0,0); return {best,cnt};
}
int main(){
  vector<unsigned> prev={0}; // n=1
  for(n=1;n<=8;n++){
    int k=0; for(int i=0;i<n;i++)for(int j=i+1;j<n;j++)pairIdx[i][j]=k++;
    map<unsigned,long long> cur;
    if(n==1){cur[0]=1;}
    else{
      // prev codes use pair indexing of n-1; decode
      int pi[8][8];int kk=0; for(int i=0;i<n-1;i++)for(int j=i+1;j<n-1;j++)pi[i][j]=kk++;
      for(unsigned g:prev){
        int base[8]={0};
        for(int i=0;i<n-1;i++)for(int j=i+1;j<n-1;j++)if(g>>pi[i][j]&1){base[i]|=1<<j;base[j]|=1<<i;}
        for(int nb=0;nb<(1<<(n-1));nb++){
          for(int i=0;i<n-1;i++)adj[i]=base[i]|((nb>>i&1)<<(n-1));
          adj[n-1]=nb;
          auto r=canon(); cur[r.first]=r.second;
        }
      }
    }
    prev.clear();
    for(auto&p:cur){prev.push_back(p.first); printf("%d %u %lld\n",n,p.first,p.second);}
    fprintf(stderr,"n=%d count=%zu\n",n,cur.size());
  }
}
