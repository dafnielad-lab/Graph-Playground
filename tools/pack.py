import json, math, networkx as nx
from collections import defaultdict
B="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
def enc(bits,nb):
    L=(nb+5)//6 or 1
    return "".join(B[(bits>>(6*i))&63] for i in range(L))
G=defaultdict(lambda:["",[]])
tot=defaultdict(int)
for line in open("graphs.txt"):
    n,c,a=map(int,line.split())
    G[n][0]+=enc(c,n*(n-1)//2); G[n][1].append(a); tot[n]+=math.factorial(n)//a
for n in sorted(G): assert tot[n]==2**(n*(n-1)//2),(n,tot[n]); print(n,len(G[n][1]))
# trees 9..12
def aut_tree(T):
    c=nx.center(T)
    def canon(v,p):
        ch=sorted(canon(u,v) for u in T[v] if u!=p)
        a=1
        from collections import Counter
        for s,k in Counter(x[0] for x in ch).items(): a*=math.factorial(k)
        for x in ch: a*=x[1]
        return ("("+"".join(x[0] for x in ch)+")",a)
    if len(c)==1: return canon(c[0],None)[1]
    x=canon(c[0],c[1]); y=canon(c[1],c[0])
    return x[1]*y[1]*(2 if x[0]==y[0] else 1)
T={}
for n in range(9,13):
    s="";al=[];t=0
    for tr in nx.nonisomorphic_trees(n):
        bits=0;k=0
        for i in range(n):
            for j in range(i+1,n):
                if tr.has_edge(i,j): bits|=1<<k
                k+=1
        a=aut_tree(tr); s+=enc(bits,n*(n-1)//2); al.append(a); t+=math.factorial(n)//a
    assert t==n**(n-2),(n,t); T[n]=[s,al]; print("tree",n,len(al))
json.dump({"G":{n:G[n] for n in G},"T":T},open("data.json","w"),separators=(",",":"))
