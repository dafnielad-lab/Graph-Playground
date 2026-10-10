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
      const last=x.steps[x.steps.length-1][0],v=x.c?L.fmt(x.c):L.fmt(x.hi);if(!last.endsWith(v)&&!(kind==='pow'&&last.includes(' > ')))bad.push(['steps do not end at the value',kind,last,v])}}
  /* ---- union, intersection, difference, symmetric difference ---- */
  let pairsN=0,tight=0,nested=0;
  { /* every pair of subsets of a set of six elements: the true size must lie in the range, under no assumption and under every assumption that is true for the pair */
    const pc=x=>{let c=0;while(x){c++;x&=x-1}return c},seenR={},inR=(r,v)=>L.cmp(r.lo,L.F(v))<=0&&L.cmp(L.F(v),r.hi)<=0;
    for(let A=0;A<64;A++)for(let Bm=0;Bm<64;Bm++){pairsN++;const a=pc(A),b=pc(Bm),T={uni:pc(A|Bm),int:pc(A&Bm),dif:pc(A&~Bm),sym:pc(A^Bm)},rels=[''];if(!(A&Bm))rels.push('dis');if(!(A&~Bm))rels.push('sub');if(!(Bm&~A))rels.push('sup');
      for(const k in T)for(const rel of rels){const r=L.setOp(k,rel,L.F(a),L.F(b),'X','A','B');if(!inR(r,T[k]))bad.push(['set operation out of range',k,rel||'none',a,b,T[k],L.fmt(r.lo),L.fmt(r.hi)]);
        if(rel!==''&&!L.same(r.lo,r.hi))bad.push(['finite sets with a known relation must give one value',k,rel,a,b]);
        if(rel===''&&a<=3&&b<=3){const key=k+'|'+a+'|'+b,e=seenR[key]||(seenR[key]={lo:99,hi:-1,r});e.lo=Math.min(e.lo,T[k]);e.hi=Math.max(e.hi,T[k])}}}
    /* with no assumption the range is exactly what really occurs: six elements leave room for every case when both sets have at most three */
    for(const key in seenR){tight++;const e=seenR[key];if(Number(e.r.lo.n)!==e.lo||Number(e.r.hi.n)!==e.hi)bad.push(['range not tight',key,e.lo,e.hi,L.fmt(e.r.lo),L.fmt(e.r.hi)])}}
  { /* random lists of finite sets, built for real as sets of strings: every cardinality claimed must contain the true size, and every relation read off the structure must be true */
    const tuples=(A,n)=>{let o=[[]];for(let t=0;t<n;t++)o=o.flatMap(x=>A.map(y=>[...x,y]));return o.map(x=>'('+x.join(',')+')')},subsets=A=>{const o=[];for(let m=0;m<1<<A.length;m++)o.push('{'+A.filter((_,t)=>m>>t&1).join(',')+'}');return o};
    const build=(s,A,Bq)=>{const k=s.kind;if(k==='fin')return Array.from({length:s.n},(_,t)=>String(t+1));if(k==='prod')return A.flatMap(x=>Bq.map(y=>'<'+x+'|'+y+'>'));if(k==='tup')return tuples(A,s.n);if(k==='pow'||k==='pfin')return subsets(A);
      if(k==='sum')return [...A.map(x=>'L:'+x),...Bq.map(y=>'R:'+y)];if(k==='fun'){let o=[[]];for(const x of A)o=o.flatMap(f=>Bq.map(y=>[...f,x+'↦'+y]));return o.map(f=>'['+f.join(';')+']')}
      const SA=new Set(A),SB=new Set(Bq);if(k==='uni')return [...new Set([...A,...Bq])];if(k==='int')return A.filter(x=>SB.has(x));if(k==='dif')return A.filter(x=>!SB.has(x));return [...A.filter(x=>!SB.has(x)),...Bq.filter(x=>!SA.has(x))]};
    let seed=24681357;const rnd=()=>(seed=(seed*1103515245+12345)&0x7fffffff)/0x7fffffff;
    const kinds=['prod','prod','tup','pow','pfin','fun','sum','uni','int','dif','sym','uni','int','dif','sym','dif','int'],names='ABCDEFGHJK';let exactN=0,relN=0;
    for(let t=0;t<4000;t++){const list=[],real=[];for(let q=0;q<3;q++){list.push({name:names[q],kind:'fin',n:Math.floor(rnd()*4)});real.push(build(list[q]))}
      for(let q=3;q<9;q++){for(let tries=0;tries<20;tries++){const k=kinds[Math.floor(rnd()*kinds.length)],a=Math.floor(rnd()*q),b2=Math.floor(rnd()*q),s={name:names[q],kind:k,a:names[a],b:names[b2],n:Math.floor(rnd()*3)};
          if((k==='pow'||k==='pfin')&&real[a].length>6)continue;if(k==='fun'&&Math.pow(Math.max(real[b2].length,1),real[a].length)>300)continue;if(k==='tup'&&Math.pow(Math.max(real[a].length,1),s.n)>300)continue;if(k==='prod'&&real[a].length*real[b2].length>300)continue;
          list.push(s);real.push(build(s,real[a],real[b2]));break}if(list.length<=q)break}
      const R=L.solve(list),memo=new Map();
      for(let q=0;q<list.length;q++){nested++;const x=R[q],v=L.F(real[q].length);if(x.bad){bad.push(['unexpected bad set',JSON.stringify(list)]);continue}if(x.c)exactN++;
        if(L.cmp(x.lo,v)>0||L.cmp(v,x.hi)>0)bad.push(['true size outside the claim',list[q].name,real[q].length,L.fmt(x.lo),L.fmt(x.hi),JSON.stringify(list)])}
      for(let q=0;q<list.length;q++)for(let w=0;w<list.length;w++){const r=L.relOf(q,w,list,memo);if(!r)continue;relN++;const SA=new Set(real[q]),SB=new Set(real[w]),sub=real[q].every(x=>SB.has(x)),sup=real[w].every(x=>SA.has(x)),dis=!real[q].some(x=>SB.has(x));
        if((r==='eq'&&!(sub&&sup))||(r==='sub'&&!sub)||(r==='sup'&&!sup)||(r==='dis'&&!dis))bad.push(['false relation between sets',r,list[q].name,list[w].name,JSON.stringify(list)])}}
    tight=[tight,exactN,relN].join('/')}
  /* infinite sets whose answer is known */
  const wantR=(l,v,what)=>{known++;const r=L.solve(l),x=r[r.length-1],g=x.c?L.fmt(x.c):L.fmt(x.lo)+' … '+L.fmt(x.hi);if(v==='range'?!!x.c:g!==v)bad.push(['known value',what,g,v])};
  const at=(n,k,x)=>Object.assign({name:n,kind:k},x||{});
  wantR([at('A','R'),at('B','Q'),at('C','dif',{a:'A',b:'B'})],Cc,'the irrationals');wantR([at('A','R'),at('B','N'),at('C','uni',{a:'A',b:'B'})],Cc,'R ∪ N');wantR([at('A','N'),at('B','R'),at('C','int',{a:'A',b:'B'})],A0,'N ∩ R');
  wantR([at('A','Z'),at('B','N'),at('C','dif',{a:'A',b:'B'})],'0 … '+A0,'Z ∖ N: not settled by cardinalities alone');wantR([at('A','N'),at('B','Z'),at('C','dif',{a:'A',b:'B'})],'0','N ∖ Z');
  wantR([at('A','N'),at('B','pow',{a:'A'}),at('C','pfin',{a:'A'}),at('D','dif',{a:'B',b:'C',rel:'sup'})],Cc,'the infinite subsets of N');wantR([at('A','N'),at('B','pow',{a:'A'}),at('C','pfin',{a:'A'}),at('D','dif',{a:'B',b:'C'})],Cc,'the same, with nothing said about the relation');
  wantR([at('A','R'),at('B','Q'),at('C','sym',{a:'A',b:'B'})],Cc,'R △ Q');wantR([at('A','I'),at('B','Z'),at('C','int',{a:'A',b:'B'})],'0','(0,1) ∩ Z');wantR([at('A','I'),at('B','N'),at('C','uni',{a:'A',b:'B'})],Cc,'(0,1) ∪ N');
  wantR([at('A','N'),at('B','seq',{a:'A'}),at('C','star',{a:'A'}),at('D','uni',{a:'B',b:'C'})],Cc,'infinite and finite sequences together');wantR([at('A','fin',{n:5}),at('B','fin',{n:3}),at('C','dif',{a:'A',b:'B'})],'2','{1..5} ∖ {1..3}');
  /* what the structure settles */
  const RR=[at('A','R'),at('M','Q'),at('B','prod',{a:'A',b:'A'}),at('C','prod',{a:'M',b:'A'})];
  wantR([...RR,at('D','dif',{a:'B',b:'C'})],Cc,'(R × R) ∖ (Q × R)');wantR([...RR,at('D','int',{a:'B',b:'C'})],Cc,'(R × R) ∩ (Q × R)');wantR([...RR,at('E','prod',{a:'A',b:'M'}),at('D','int',{a:'C',b:'E'})],A0,'(Q × R) ∩ (R × Q) = Q × Q');
  wantR([...RR,at('D','dif',{a:'B',b:'B'})],'0','a set minus itself');wantR([...RR,at('E','prod',{a:'M',b:'M'}),at('D','dif',{a:'B',b:'E'})],Cc,'R² ∖ Q²');
  wantR([at('A','N'),at('B','fin',{n:2}),at('C','fun',{a:'A',b:'B'}),at('D','R'),at('E','seq',{a:'D'}),at('K','int',{a:'C',b:'E'})],Cc,'functions from N into {1,2}, against sequences of reals: a sequence is such a function');
  wantR([at('A','fin',{n:2}),at('D','R'),at('C','seq',{a:'A'}),at('E','seq',{a:'D'}),at('K','int',{a:'C',b:'E'})],Cc,'binary sequences ∩ real sequences');wantR([at('A','R'),at('M','Q'),at('B','pow',{a:'A'}),at('C','pow',{a:'M'}),at('D','dif',{a:'B',b:'C'})],CC,'P(R) ∖ P(Q)');
  wantR([at('A','R'),at('M','Q'),at('B','seq',{a:'A'}),at('C','seq',{a:'M'}),at('D','dif',{a:'B',b:'C'})],Cc,'real sequences that are not all rational');wantR([at('A','N'),at('M','fin',{n:2}),at('B','star',{a:'A'}),at('C','star',{a:'M'}),at('D','dif',{a:'B',b:'C'})],A0,'N* ∖ {1,2}*');
  wantR([at('A','N'),at('B','pow',{a:'A'}),at('C','pow',{a:'A'}),at('D','sym',{a:'B',b:'C'})],'0','P(N) △ P(N)');wantR([at('A','R'),at('B','seq',{a:'A'}),at('C','cond',{a:'A',cond:'evconst'}),at('D','dif',{a:'B',b:'C'})],'0 … '+Cc,'sequences that are not eventually constant: equal cardinalities, not settled');
  /* ---- infinite sequences with a condition ---- */
  let cons=0;
  { const srcs={e:[at('A','fin',{n:0})],one:[at('A','fin',{n:1})],two:[at('A','fin',{n:2})],three:[at('A','fin',{n:3})],N:[at('A','N')],Z:[at('A','Z')],Q:[at('A','Q')],R:[at('A','R')],I:[at('A','I')],PR:[at('A0','R'),at('A','pow',{a:'A0'})]};
    const get=(src,cond,n)=>{const r=L.solve([...srcs[src],at('S','cond',{a:'A',cond,n})]),x=r[r.length-1];return x.bad?null:x},val=(src,cond,n)=>{const x=get(src,cond,n);return x&&x.c?L.fmt(x.c):x?'range':'bad'};
    /* 1. relations that must hold between the conditions, whatever the set: parts add up to the whole, a narrower condition is not larger */
    for(const src in srcs){const c=(cond,n)=>{const x=get(src,cond,n);return x&&x.c},all=L.solve([...srcs[src],at('S','seq',{a:'A'})]).pop().c,k=L.solve(srcs[src]).pop().c;
      const eqc=(x,y,w)=>{cons++;if(!x||!y||!L.same(x,y))bad.push(['conditions: '+w,src,x&&L.fmt(x),y&&L.fmt(y)])},lec=(x,y,w)=>{cons++;if(!x||!y||L.cmp(x,y)>0)bad.push(['conditions: '+w,src,x&&L.fmt(x),y&&L.fmt(y)])};
      eqc(L.add(c('never'),c('once')),all,'never + at least once = all');eqc(L.add(c('fintimes'),c('inf')),all,'finitely often + infinitely often = all');lec(c('never'),c('fintimes'),'never ≤ finitely often');lec(c('inf'),c('once'),'infinitely often ≤ at least once');
      eqc(c('const'),k,'constant = the set');eqc(c('per',1),c('const'),'period 1 = constant');eqc(c('per',2),L.mul(k,k),'period 2 = pairs');lec(c('const'),c('per',3),'constant ≤ period 3');lec(c('per',3),c('anyper'),'period 3 ≤ periodic');lec(c('anyper'),all,'periodic ≤ all');
      lec(c('const'),c('evconst'),'constant ≤ eventually constant');lec(c('finsup'),c('evconst'),'finite support ≤ eventually constant');lec(c('evconst'),all,'eventually constant ≤ all');lec(c('inj'),all,'one-to-one ≤ all');lec(c('surj'),all,'onto ≤ all');
      for(const f of ['fixk','fixeven','pairs'])eqc(c(f,2),all,f+' = all');
      if(get(src,'nd')){lec(c('si'),c('nd'),'increasing ≤ non-decreasing');lec(c('sd'),c('ni'),'decreasing ≤ non-increasing');lec(c('si'),c('inj'),'increasing ≤ one-to-one');lec(c('sd'),c('inj'),'decreasing ≤ one-to-one');lec(c('const'),c('nd'),'constant ≤ non-decreasing');lec(c('const'),c('ni'),'constant ≤ non-increasing')}}
    /* 2. values written down by hand, independently of the code */
    const CCC='2<sup>2<sup>ℵ₀</sup></sup>',T={two:{evconst:A0,anyper:A0,finsup:A0,never:'1',fintimes:A0,inf:Cc,once:Cc,inj:'0',surj:Cc,nd:A0,ni:A0,si:'0',sd:'0',const:'2'},
      N:{const:A0,anyper:A0,evconst:A0,finsup:A0,inj:Cc,surj:Cc,nd:Cc,si:Cc,ni:A0,sd:'0',never:Cc,fintimes:Cc,inf:Cc,once:Cc},R:{const:Cc,anyper:Cc,evconst:Cc,finsup:Cc,inj:Cc,surj:'0',nd:Cc,si:Cc,ni:Cc,sd:Cc,never:Cc},
      Z:{ni:Cc,sd:Cc,nd:Cc,si:Cc,surj:Cc},Q:{si:Cc,sd:Cc,evconst:A0},I:{sd:Cc,si:Cc,nd:Cc},PR:{const:CCC,evconst:CCC,anyper:CCC,inj:CCC,surj:'0',nd:'bad',never:CCC},
      one:{const:'1',anyper:'1',evconst:'1',finsup:'1',never:'0',once:'1',inf:'1',fintimes:'0',inj:'0',surj:'1',nd:'1',ni:'1',si:'0',sd:'0'},three:{never:Cc,fintimes:Cc,surj:Cc,nd:A0,evconst:A0,inj:'0'},
      e:{const:'0',anyper:'0',evconst:'0',finsup:'0',never:'0',once:'0',inf:'0',fintimes:'0',inj:'0',surj:'0',nd:'0',si:'0'}};
    for(const src in T)for(const cond in T[src]){known++;const g=val(src,cond,2);if(g!==T[src][cond])bad.push(['condition value',src,cond,g,T[src][cond]])}
    /* 3. the steps end at the value */
    for(const src in srcs)for(const cond in L.CONDS){const x=get(src,cond,3);if(!x||!x.c)continue;shown++;const last=x.steps[x.steps.length-1][0];if(!last.endsWith(L.fmt(x.c)))bad.push(['condition steps do not end at the value',src,cond,last])}}
  /* ---- conditions against real sequences: words over a small alphabet, checked by rules written here and not taken from the page ---- */
  let prefixes=0,parts=0;
  { const condVal=(n,cond,p)=>{const r=L.solve([at('A','fin',{n}),at('S','cond',{a:'A',cond,n:p})]),x=r[1];return x};
    /* conditions that a finite beginning can violate. ok(w): the word w does not violate it yet. Places are numbered from 1; c is the letter 0; given values are 0 */
    const LOCAL={const:w=>w.every(x=>x===w[0]),per:(w,p)=>w.every((x,i)=>i<p||x===w[i-p]),fixk:(w,p)=>w.every((x,i)=>i>=p||x===0),fixeven:w=>w.every((x,i)=>(i+1)%2||x===0),pairs:w=>w.every((x,i)=>(i+1)%2||x===w[i-1]),
      never:w=>w.every(x=>x!==0),inj:w=>new Set(w).size===w.length,nd:w=>w.every((x,i)=>!i||w[i-1]<=x),si:w=>w.every((x,i)=>!i||w[i-1]<x),ni:w=>w.every((x,i)=>!i||w[i-1]>=x),sd:w=>w.every((x,i)=>!i||w[i-1]>x)};
    /* the number of beginnings of length len that can still be continued for extra more places: for these conditions a sequence exists exactly when every beginning can be continued */
    const count=(n,ok,len,extra,p)=>{let c=0;const ext=(w,d)=>{if(d===0)return true;for(let v=0;v<n;v++){w.push(v);const g=ok(w,p)&&ext(w,d-1);w.pop();if(g)return true}return false};
      const go=w=>{if(w.length===len){if(ext(w,extra))c++;return}for(let v=0;v<n;v++){w.push(v);if(ok(w,p))go(w);w.pop()}};go([]);return c};
    for(const n of [1,2,3])for(const cond in LOCAL)for(const p of (cond==='per'||cond==='fixk'?[1,2,3]:[2])){prefixes++;const x=condVal(n,cond,p),c6=count(n,LOCAL[cond],6,n+2,p),c9=count(n,LOCAL[cond],9,n+2,p),tag=[cond,'n='+n,'p='+p,L.fmt(x.c),c6,c9];
      /* a finite set of sequences has exactly that many beginnings once they are long enough to tell the sequences apart */
      if(x.c.t==='f'){if(c9!==Number(x.c.n)||c6!==c9)bad.push(['finite claim against counted beginnings',...tag])}
      /* countable here means: grows without bound, but only like a polynomial. The continuum means: doubles again and again */
      else if(x.c.k===0){if(!(c9>c6)||c9>Math.pow(10,n))bad.push(['countable claim against counted beginnings',...tag])}
      else if(c9<8*c6/4||c9<16)bad.push(['continuum claim against counted beginnings',...tag])}
    /* the pieces of the unions: sequences constant from place m, with period m, equal to c after place m. Counted as words of length 8 */
    const PIECE={evconst:(w,m)=>w.every((x,i)=>i<m-1||x===w[m-1]),anyper:(w,m)=>w.every((x,i)=>i<m||x===w[i-m]),finsup:(w,m)=>w.every((x,i)=>i<m||x===0)};
    for(const n of [2,3])for(const cond in PIECE){const x=condVal(n,cond,2),from=x.steps.parts?x.steps.parts.from:null;if(from===null){bad.push(['no pieces recorded',cond]);continue}
      for(let m=from;m<=4;m++){parts++;let c=0;const go=w=>{if(w.length===8){if(PIECE[cond](w,m))c++;return}for(let v=0;v<n;v++){w.push(v);go(w);w.pop()}};go([]);if(c!==Math.pow(n,m))bad.push(['piece of the union is not A^m',cond,'n='+n,'m='+m,c,Math.pow(n,m)])}
      if(from===1){let c=0;const go=w=>{if(w.length===8){if(PIECE[cond](w,0))c++;return}for(let v=0;v<n;v++){w.push(v);go(w);w.pop()}};/* nothing to check below the first piece */}}}
  return{bad:bad.slice(0,30),total:bad.length,laws,counts,known,shown,pairsN,tight,nested,cons,prefixes,parts}});
console.log(JSON.stringify(res),'page errors',errs);
await b.close();process.exit(res.total||errs.length?1:0)})();
