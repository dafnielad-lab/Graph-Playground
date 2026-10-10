const {chromium}=require('playwright'),path=require('path');
/* the cardinalities playground: the arithmetic against the laws every cardinal obeys, finite cases against real counting, and known values */
(async()=>{const b=await chromium.launch(process.env.CHROMIUM||require('fs').existsSync('/opt/pw-browsers/chromium')?{executablePath:process.env.CHROMIUM||'/opt/pw-browsers/chromium'}:{});const p=await b.newPage();
const errs=[];p.on('pageerror',e=>errs.push(e.message));
await p.goto(process.env.PAGE||'file://'+path.resolve(__dirname,'..','index.html'));
const res=await p.evaluate(()=>{const L=CARD.lib,bad=[];let laws=0,counts=0,known=0;
  const C=[];for(let n=0;n<=5;n++)C.push(L.F(n));for(let k=0;k<=3;k++)C.push(L.B(k));
  const eq=(x,y,what,...a)=>{laws++;if(!L.same(x,y))bad.push([what,...a.map(L.fmt),L.fmt(x),L.fmt(y)])},le=(x,y)=>L.cmp(x,y)<=0;
  for(const x of C)for(const y of C){eq(L.add(x,y),L.add(y,x),'a+b=b+a',x,y);eq(L.mul(x,y),L.mul(y,x),'ab=ba',x,y);
    /* Cantor, and monotonicity */
    laws++;if(L.cmp(L.pow(L.F(2),x),x)<=0)bad.push(['2^a > a',L.fmt(x)]);
    for(const z of C){eq(L.add(L.add(x,y),z),L.add(x,L.add(y,z)),'(a+b)+c',x,y,z);eq(L.mul(L.mul(x,y),z),L.mul(x,L.mul(y,z)),'(ab)c',x,y,z);eq(L.mul(x,L.add(y,z)),L.add(L.mul(x,y),L.mul(x,z)),'a(b+c)',x,y,z);
      eq(L.pow(L.pow(x,y),z),L.pow(x,L.mul(y,z)),'(a^b)^c = a^(bc)',x,y,z);eq(L.pow(x,L.add(y,z)),L.mul(L.pow(x,y),L.pow(x,z)),'a^(b+c) = a^b a^c',x,y,z);eq(L.pow(L.mul(x,y),z),L.mul(L.pow(x,z),L.pow(y,z)),'(ab)^c = a^c b^c',x,y,z);
      if(le(x,y)){laws+=3;if(!le(L.add(x,z),L.add(y,z)))bad.push(['a≤b ⇒ a+c≤b+c',L.fmt(x),L.fmt(y),L.fmt(z)]);if(!le(L.mul(x,z),L.mul(y,z)))bad.push(['a≤b ⇒ ac≤bc',L.fmt(x),L.fmt(y),L.fmt(z)]);if(!le(L.pow(x,z),L.pow(y,z)))bad.push(['a≤b ⇒ a^c≤b^c',L.fmt(x),L.fmt(y),L.fmt(z)]);
        /* the exponent is monotone except for base zero */
        if(!(x.t==='f'&&x.n===0n)&&!(z.t==='f'&&z.n===0n)){laws++;if(!le(L.pow(z,x),L.pow(z,y)))bad.push(['a≤b ⇒ c^a≤c^b',L.fmt(x),L.fmt(y),L.fmt(z)])}}}}
  /* finite sets: count the real objects */
  const run=l=>L.solve(l).map(r=>r.c),num=c=>c.t==='f'?Number(c.n):null;
  for(let n=0;n<=4;n++)for(let m=0;m<=4;m++){
    /* functions from a set of n to a set of m, by listing them */
    let f=0;const go=d=>{if(d===n){f++;return}for(let v=0;v<m;v++)go(d+1)};go(0);
    const r=run([{name:'A',kind:'fin',n},{name:'B',kind:'fin',n:m},{name:'C',kind:'fun',a:'A',b:'B'},{name:'D',kind:'prod',a:'A',b:'B'},{name:'E',kind:'sum',a:'A',b:'B'},{name:'G',kind:'pow',a:'A'},{name:'H',kind:'pfin',a:'A'},{name:'J',kind:'tup',a:'B',n}]);counts+=6;
    let sub=0;for(let s=0;s<1<<n;s++)sub++;
    if(num(r[2])!==f)bad.push(['functions',n,m,num(r[2]),f]);if(num(r[3])!==n*m)bad.push(['product',n,m]);if(num(r[4])!==n+m)bad.push(['sum',n,m]);if(num(r[5])!==sub||num(r[6])!==sub)bad.push(['subsets',n]);if(num(r[7])!==f)bad.push(['tuples',n,m])}
  /* values every textbook states */
  const A0='ℵ₀',Cc='2<sup>ℵ₀</sup>',CC='2<sup>2<sup>ℵ₀</sup></sup>',want=(l,v,what)=>{known++;const r=L.solve(l),g=L.fmt(r[r.length-1].c);if(g!==v)bad.push(['known value',what,g,v])};
  const N={name:'A',kind:'N'},R={name:'A',kind:'R'},two={name:'B',kind:'fin',n:2},nat={name:'B',kind:'N'},real={name:'B',kind:'R'};
  want([N,{name:'C',kind:'prod',a:'A',b:'A'}],A0,'N × N');want([N,{name:'C',kind:'star',a:'A'}],A0,'finite sequences of naturals');want([N,{name:'C',kind:'pfin',a:'A'}],A0,'finite subsets of N');
  want([N,{name:'C',kind:'pow',a:'A'}],Cc,'P(N)');want([N,two,{name:'C',kind:'fun',a:'A',b:'B'}],Cc,'N → {0,1}');want([N,{name:'C',kind:'seq',a:'A'}],Cc,'N → N');want([R,{name:'C',kind:'seq',a:'A'}],Cc,'N → R');
  want([R,{name:'C',kind:'prod',a:'A',b:'A'}],Cc,'R × R');want([R,{name:'C',kind:'star',a:'A'}],Cc,'finite sequences of reals');want([R,nat,{name:'C',kind:'fun',a:'A',b:'B'}],CC,'R → N');want([R,{name:'C',kind:'fun',a:'A',b:'A'}],CC,'R → R');
  want([R,{name:'C',kind:'pow',a:'A'}],CC,'P(R)');want([R,two,{name:'C',kind:'fun',a:'A',b:'B'}],CC,'R → {0,1}');want([{name:'A',kind:'Q'},{name:'B',kind:'Z'},{name:'C',kind:'sum',a:'A',b:'B'}],A0,'Q ⊔ Z');
  want([{name:'A',kind:'fin',n:0},{name:'C',kind:'star',a:'A'}],'1','sequences over the empty set');want([{name:'A',kind:'fin',n:1},{name:'C',kind:'star',a:'A'}],A0,'sequences over one letter');
  want([{name:'A',kind:'fin',n:0},nat,{name:'C',kind:'fun',a:'A',b:'B'}],'1','∅ → N');want([N,{name:'B',kind:'fin',n:0},{name:'C',kind:'fun',a:'A',b:'B'}],'0','N → ∅');want([N,{name:'B',kind:'fin',n:1},{name:'C',kind:'fun',a:'A',b:'B'}],'1','N → {1}');
  want([N,{name:'B',kind:'fin',n:0},{name:'C',kind:'prod',a:'A',b:'B'}],'0','N × ∅');want([{name:'A',kind:'I'},nat,{name:'C',kind:'prod',a:'A',b:'B'}],Cc,'(0,1) × N');
  /* the steps shown: for every construction over every pair of cardinals, the last line must end at the value computed */
  let shown=0;{const atoms=[{kind:'fin',n:0},{kind:'fin',n:1},{kind:'fin',n:2},{kind:'fin',n:3},{kind:'N'},{kind:'R'}];
    const lift=(a,nm,k)=>{const l=[Object.assign({name:nm+'0'},a)];let prev=nm+'0';for(let i=1;i<=k;i++){l.push({name:nm+i,kind:'pow',a:prev});prev=nm+i}return l};
    for(const a of atoms)for(const ka of [0,1,2])for(const b of atoms)for(const kb of [0,1,2])for(const kind of Object.keys(L.KINDS)){if(!L.KINDS[kind].src)continue;
      const la=lift(a,'A',ka),lb=lift(b,'B',kb),R=L.solve([...la,...lb,{name:'X',kind,a:la[la.length-1].name,b:lb[lb.length-1].name,n:3}]),x=R[R.length-1];shown++;
      const last=x.steps[x.steps.length-1][0],v=L.fmt(x.c);if(!last.endsWith(v)&&!(kind==='pow'&&last.includes(' > ')))bad.push(['steps do not end at the value',kind,last,v])}}
  return{bad:bad.slice(0,30),total:bad.length,laws,counts,known,shown}});
console.log(JSON.stringify(res),'page errors',errs);
await b.close();process.exit(res.total||errs.length?1:0)})();
