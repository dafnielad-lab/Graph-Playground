const {chromium}=require('playwright'),path=require('path');
/* the relations playground: every function against an independent check, on random relations and on all relations over three elements */
(async()=>{const b=await chromium.launch(process.env.CHROMIUM||require('fs').existsSync('/opt/pw-browsers/chromium')?{executablePath:process.env.CHROMIUM||'/opt/pw-browsers/chromium'}:{});const p=await b.newPage();
const errs=[];p.on('pageerror',e=>errs.push(e.message));
await p.goto(process.env.PAGE||'file://'+path.resolve(__dirname,'..','index.html'));
const res=await p.evaluate(()=>{const L=REL.lib,bad=[];let cnt=0,orders=0,equivs=0;
  const check=(M,id)=>{cnt++;const n=M.length,h=(i,j)=>M[i]>>j&1,P=L.analyze(M),I=L.ident(n),inv=L.inverse(M),sq=L.compose(M,M);
    const all=(f,k)=>{const idx=[];const go=d=>{if(d===k)return f(...idx);for(let i=0;i<n;i++){idx[d]=i;if(!go(d+1))return false}return true};return go(0)};
    const T={refl:all(a=>h(a,a),1),irr:all(a=>!h(a,a),1),sym:all((a,c)=>!h(a,c)||h(c,a),2),anti:all((a,c)=>!(h(a,c)&&h(c,a))||a===c,2),trans:all((a,c,d)=>!(h(a,c)&&h(c,d))||h(a,d),3),comp:all((a,c)=>a===c||h(a,c)||h(c,a),2)};
    for(const k in T){if(P[k].ok!==T[k])bad.push([id,k,'property']);
      /* a witness must really be a counterexample: its pairs are in, its missing pairs are out */
      if(!P[k].ok){if(!P[k].inn.every(([i,j])=>h(i,j))||!P[k].out.every(([i,j])=>!h(i,j))||!(P[k].inn.length+P[k].out.length))bad.push([id,k,'witness'])}}
    /* the algebraic forms shown next to each property */
    const A={refl:L.subset(I,M),irr:L.inter(M,I).every(r=>r===0),sym:L.same(inv,M),anti:L.subset(L.inter(M,inv),I),trans:L.subset(sq,M),comp:L.same(L.union(L.union(M,inv),I),L.full(n))};
    for(const k in A)if(A[k]!==T[k])bad.push([id,k,'algebraic form']);
    /* inverse twice, complement twice, composition by definition */
    if(!L.same(L.inverse(inv),M)||!L.same(L.compl(L.compl(M)),M))bad.push([id,'involution']);
    for(let a=0;a<n;a++)for(let c=0;c<n;c++){let e=false;for(let d=0;d<n;d++)if(h(a,d)&&h(d,c))e=true;if(e!==!!(sq[a]>>c&1))bad.push([id,'compose'])}
    /* closures: contain the relation, have the property, and lie inside every relation with the property that contains it (checked through the known formula by powers) */
    const tc=L.tclose(M);let pw=M,un=M;for(let k=1;k<n;k++){pw=L.compose(pw,M);un=L.union(un,pw)}if(!L.same(tc,un)||!L.analyze(tc).trans.ok||!L.subset(M,tc))bad.push([id,'transitive closure']);
    const ec=L.tclose(L.union(L.union(M,inv),I)),Pe=L.analyze(ec);if(!Pe.equiv||!L.subset(M,ec))bad.push([id,'equivalence closure']);
    { /* the classes of the equivalence closure are the connected components of the underlying graph */
      const C=L.classes(ec),seen=new Set();for(const c of C)for(const x of c){if(seen.has(x))bad.push([id,'classes overlap']);seen.add(x)}if(seen.size!==n)bad.push([id,'classes cover']);
      for(const c of C)for(const x of c)for(let y=0;y<n;y++)if(!!(ec[x]>>y&1)!==c.includes(y))bad.push([id,'class content'])}
    if(P.equiv)equivs++;
    if(P.weak||P.strict){orders++;const O=L.order(M),S=M.map((r,i)=>r&~(1<<i)),cov=L.empty(n);for(const [a,c] of O.cover)cov[a]|=1<<c;
      if(!L.same(L.tclose(cov),S))bad.push([id,'Hasse: closure of the covering pairs is not the order']);
      for(const [a,c] of O.cover)for(let d=0;d<n;d++)if((S[a]>>d&1)&&(S[d]>>c&1))bad.push([id,'Hasse: a covering pair with an element between']);
      for(const [a,c] of O.cover)if(O.lev[a]>=O.lev[c])bad.push([id,'Hasse: a line that does not go up']);
      const mn=[],mx=[];for(let a=0;a<n;a++){let lo=false,hi=false;for(let d=0;d<n;d++){if(S[d]>>a&1)lo=true;if(S[a]>>d&1)hi=true}if(!lo)mn.push(a);if(!hi)mx.push(a)}
      if(mn.join()!==O.min.join()||mx.join()!==O.max.join())bad.push([id,'minimal or maximal']);
      const le=a=>{for(let d=0;d<n;d++)if(d!==a&&!(S[a]>>d&1))return false;return true},ge=a=>{for(let d=0;d<n;d++)if(d!==a&&!(S[d]>>a&1))return false;return true};
      const l=[...Array(n).keys()].filter(le),g=[...Array(n).keys()].filter(ge);if((l.length?l[0]:-1)!==O.least||(g.length?g[0]:-1)!==O.greatest)bad.push([id,'least or greatest']);
      for(let i=1;i<O.chain.length;i++)if(!(S[O.chain[i-1]]>>O.chain[i]&1))bad.push([id,'chain']);
      /* the longest chain and the largest antichain, by trying every subset */
      let bc=0,ba=0;for(let s=1;s<1<<n;s++){const e=[];for(let a=0;a<n;a++)if(s>>a&1)e.push(a);let ch=true,an=true;for(const x of e)for(const y of e)if(x!==y){if(!(S[x]>>y&1)&&!(S[y]>>x&1))ch=false;if(S[x]>>y&1)an=false}if(ch)bc=Math.max(bc,e.length);if(an)ba=Math.max(ba,e.length)}
      if(bc!==O.chain.length||ba!==O.anti.length)bad.push([id,`chain ${O.chain.length}/${bc}, antichain ${O.anti.length}/${ba}`]);
      if((O.inc.length===0)!==P.total)bad.push([id,'total'])}};
  /* every relation on one, two and three elements */
  for(let n=1;n<=3;n++)for(let code=0;code<1<<n*n;code++){const M=[];for(let i=0;i<n;i++)M.push(code>>i*n&((1<<n)-1));check(M,n+':'+code)}
  /* random relations, and random orders and equivalences so that those branches are well covered */
  let seed=12345;const rnd=()=>(seed=(seed*1103515245+12345)&0x7fffffff)/0x7fffffff;
  for(let t=0;t<4000;t++){const n=4+Math.floor(rnd()*4),d=rnd();const M=Array.from({length:n},()=>{let r=0;for(let j=0;j<n;j++)if(rnd()<d)r|=1<<j;return r});check(M,'r'+t);
    if(t%4===0){const up=M.map((r,i)=>r&~((1<<i+1)-1)),st=L.tclose(up);check(st,'strict'+t);check(L.union(st,L.ident(n)),'weak'+t)}
    if(t%4===1)check(L.tclose(L.union(L.union(M,L.inverse(M)),L.ident(n))),'eq'+t)}
  return{bad:bad.slice(0,30),total:bad.length,cnt,orders,equivs}});
console.log(JSON.stringify(res),'page errors',errs);
await b.close();process.exit(res.total||errs.length?1:0)})();
