const {chromium}=require('playwright');
(async()=>{const b=await chromium.launch({executablePath:'/opt/pw-browsers/chromium'});const p=await b.newPage();
p.on('pageerror',e=>console.log('PAGEERR',e.message));
await p.goto('file:///home/claude/graph-playground/index.html');
const MAXN=Number(process.argv[2]||7),STEP=Number(process.argv[3]||1);
const res=await p.evaluate(({MAXN,STEP})=>{
  const truth=(a,n)=>{const d=degs(a),m=nEdges(a),c=nComps(a,n),al=alpha(a,n),nu=maxMatch(a,n),pl=isPlanar(a,n)?1:0;
    return{n,m,c,D:Math.max(...d),dl:Math.min(...d),chi:chi(a,n),al,nu,be:n-al,om:omega(a,n),pl,bp:isBip(a,n)?1:0,fo:m===n-c?1:0,ham:isHam(a,n)?1:0,eu:isEuler(a,n)&&m>0?1:0,
      f:pl?m-n+c+1:null,rho:Math.min(...d)>=1?n-nu:null,lv:d.filter(x=>x===1).length,reg:Math.max(...d)===Math.min(...d),tf:nTri(a,n)===0?1:0,a,d}};
  const G=(name,o)=>Object.assign({t:'g',name},o),bad=[],cnt={};
  const insight={ 'הגרף קשיר':t=>t.c===1,'הגרף המילטוני':t=>t.ham,'הגרף אוילרי':t=>t.eu,'הגרף אינו מישורי':t=>!t.pl,'הגרף אינו דו-צדדי':t=>!t.bp,'הגרף הוא עץ':t=>t.fo&&t.c===1,'הגרף הוא יער':t=>t.fo,
    'יש זיווג מושלם':t=>2*t.nu===t.n,'אין זיווג מושלם':t=>2*t.nu!==t.n,'יש בגרף מעגל אחד בדיוק':t=>t.m===t.n-t.c+1,'הגרף מלא':t=>t.m===t.n*(t.n-1)/2,'יש בגרף מעגל, ולכן הוא אינו יער':t=>!t.fo,
    'מספר הצמתים זוגי':t=>t.n%2===0,'העץ הוא מסלול':t=>t.fo&&t.c===1&&t.D<=2,'העץ הוא כוכב':t=>t.fo&&t.c===1&&t.D===t.n-1,'הגרף אינו אוילרי: כל הדרגות אי-זוגיות':t=>!t.eu,
    'כל הפאות משולשים, ואי אפשר להוסיף קשת בלי לאבד מישוריות':t=>t.pl&&t.m===3*t.n-6,'כל הפאות מרובעות':t=>t.pl&&t.tf&&t.m===2*t.n-4};
  const check=(tag,id,r,t)=>{cnt[tag]=(cnt[tag]||0)+1;if(!r){bad.push([tag,id,'missing']);return}if(r.bad){bad.push([tag,id,'FALSE CONTRADICTION']);return}
    for(const k in r.B){const tv=t[k];if(tv===null||tv===undefined)continue;const [lo,hi]=r.B[k];if(tv<lo||(hi!=='inf'&&tv>hi))bad.push([tag,id,`${k}: true ${tv} not in [${lo},${hi}]`])}
    for(const s of r.N){const f=insight[s];if(f){if(!f(t))bad.push([tag,id,'false insight: '+s])}else if(/מעגל פשוט על/.test(s)){}else bad.push([tag,id,'unchecked insight: '+s])}
    if(r.P){let aL=1e9,aH=-1,nL=1e9,nH=-1;for(let i=0;i<t.n;i++)for(let j=i+1;j<t.n;j++){const sm=t.d[i]+t.d[j];if(t.a[i]>>j&1){aL=Math.min(aL,sm);aH=Math.max(aH,sm)}else{nL=Math.min(nL,sm);nH=Math.max(nH,sm)}}
      if(aH>=0){if(aL<r.P.adjLo)bad.push([tag,id,`adj sum ${aL} < ${r.P.adjLo}`]);if(r.P.adjHi!=='inf'&&aH>r.P.adjHi)bad.push([tag,id,`adj sum ${aH} > ${r.P.adjHi}`])}
      if(nH>=0){if(nL<r.P.nadjLo)bad.push([tag,id,`nonadj sum ${nL} < ${r.P.nadjLo}`]);if(r.P.nadjHi!=='inf'&&nH>r.P.nadjHi)bad.push([tag,id,`nonadj sum ${nH} > ${r.P.nadjHi}`])}
      if(r.P.ore&&!t.ham)bad.push([tag,id,'Ore says Hamiltonian, false'])}};
  const yn=x=>x?'y':'n';
  for(let n=2;n<=MAXN;n++){const U=universe('G',n).graphs;for(let i=0;i<U.length;i+=(n>=7?STEP:1)){const a=U[i],t=truth(a,n),id=n+'#'+i;if(bad.length>60)break;
    const run=l=>{try{return SHEET.solve(l)}catch(e){bad.push(['throw',id,e.message]);return[]}};
    const tr=t.fo?(t.c===1?'y':'f'):'n';
    check('S1 n,m,c,flags',id,run([G('G',{n,m:t.m,c:t.c,pl:yn(t.pl),bp:yn(t.bp),tr,tf:yn(t.tf),sc:isoCount(a,compl(a,n),n,true)?'y':'u'})])[0],t);
    check('S2 n,degrees',id,run(t.reg?[G('G',{n}),{t:'v',name:'a',in:'G',q:'all',d:t.D,cut:false}]:[G('G',{n,D:t.D,dl:t.dl})])[0],t);
    check('S3 n,chi,alpha,omega',id,run([G('G',{n,chi:t.chi,al:t.al,om:t.om})])[0],t);
    check('S4 n,nu,props',id,run([G('G',{n,nu:t.nu,eu:t.eu?'y':'u',ha:t.ham?'y':'u',pm:2*t.nu===n?'y':'u'})])[0],t);
    check('S4b only n,m',id,run([G('G',{n,m:t.m})])[0],t);
    { const ca=compl(a,n),tc=truth(ca,n),r=run([G('G',{n,m:t.m,c:t.c,D:t.D,dl:t.dl,al:t.al,om:t.om,pl:yn(t.pl),bp:yn(t.bp)}),G('K',{op:'compl',src:'G'})]);check('S5 G with complement: G',id,r[0],t);check('S5 complement',id,r[1],tc)}
    if(n>=3){const v=i%n,kv=delVertex(a,n,v),tk=truth(kv,n-1),cut=tk.c>t.c;
      const r=run([G('G',{n,m:t.m,c:t.c,D:t.D,dl:t.dl,chi:t.chi,pl:yn(t.pl),bp:yn(t.bp),tr,ha:t.ham?'y':'u',eu:t.eu?'y':'u'}),{t:'v',name:'v',in:'G',q:'one',d:t.d[v],cut},G('K',{op:'delv',src:'G',arg:'v'})]);
      check('S6 G−v: G',id,r[0],t);check('S6 G−v: result',id,r[1],tk);
      const r2=run([G('G',{}),{t:'v',name:'v',in:'G',q:'one',d:t.d[v],cut},G('K',{op:'delv',src:'G',arg:'v',n:n-1,m:tk.m,c:tk.c,chi:tk.chi,al:tk.al,nu:tk.nu,om:tk.om,D:tk.D,dl:tk.dl,pl:yn(tk.pl),bp:yn(tk.bp)})]);
      check('S7 back from G−v',id,r2[0],t)}
    if(t.m>=1){let u=0,w=0;outer:for(u=0;u<n;u++)for(w=u+1;w<n;w++)if(a[u]>>w&1)break outer;const ae=a.slice();ae[u]&=~(1<<w);ae[w]&=~(1<<u);const te=truth(ae,n),bridge=te.c>t.c;
      const r=run([G('G',{n,m:t.m,c:t.c,D:t.D,dl:t.dl,chi:t.chi,nu:t.nu,al:t.al,pl:yn(t.pl),bp:yn(t.bp),tr,ha:t.ham?'y':'u',eu:t.eu?'y':'u'}),{t:'e',name:'e',in:'G',bridge},G('K',{op:'dele',src:'G',arg:'e'})]);
      check('S8 G−e: result',id,r[1],te);
      const r2=run([G('G',{}),{t:'e',name:'e',in:'G',bridge},G('K',{op:'dele',src:'G',arg:'e',n,m:te.m,c:te.c,chi:te.chi,al:te.al,nu:te.nu,om:te.om,D:te.D,dl:te.dl})]);check('S9 back from G−e',id,r2[0],t);
      /* two adjacent vertices removed as a clique */
      if(n>=4){const k1=delVertex(a,n,w),k2=delVertex(k1,n-1,u),t2=truth(k2,n-2);
        const r3=run([G('G',{n,m:t.m,c:t.c,D:t.D,dl:t.dl,chi:t.chi,nu:t.nu,al:t.al,om:t.om,tf:yn(t.tf)}),{t:'s',name:'S',in:'G',k:2,prop:'clique'},G('K',{op:'delS',src:'G',arg:'S'})]);check('S10 remove 2 adjacent: result',id,r3[1],t2);
        const r4=run([G('G',{n,tf:yn(t.tf),D:t.D,dl:t.dl}),{t:'s',name:'S',in:'G',k:2,prop:'clique'},G('K',{op:'delS',src:'G',arg:'S',m:t2.m,chi:t2.chi,al:t2.al,nu:t2.nu,om:t2.om})]);check('S11 back from 2 adjacent',id,r4[0],t)}}
    /* two non-adjacent */
    if(n>=4){let u=-1,w=-1;outer2:for(let x=0;x<n;x++)for(let y=x+1;y<n;y++)if(!(a[x]>>y&1)){u=x;w=y;break outer2}
      if(u>=0){const k1=delVertex(a,n,w),k2=delVertex(k1,n-1,u),t2=truth(k2,n-2);
        const r3=run([G('G',{n,m:t.m,c:t.c,D:t.D,dl:t.dl,chi:t.chi,nu:t.nu,al:t.al,om:t.om}),{t:'s',name:'S',in:'G',k:2,prop:'indep'},G('K',{op:'delS',src:'G',arg:'S'})]);check('S12 remove 2 non-adjacent: result',id,r3[1],t2);
        const r4=run([G('G',{n,D:t.D,dl:t.dl}),{t:'s',name:'S',in:'G',k:2,prop:'indep'},G('K',{op:'delS',src:'G',arg:'S',m:t2.m,chi:t2.chi,al:t2.al,nu:t2.nu,om:t2.om})]);check('S13 back from 2 non-adjacent',id,r4[0],t)}}
    /* components */
    if(t.c>=2){let rem=(1<<n)-1;const comps=[];while(rem){const S=flood(a,low(rem),rem);rem&=~S;comps.push(S)}
      const sub=S=>{const idx=[];for(let x=0;x<n;x++)if(S>>x&1)idx.push(x);return idx.map(x=>idx.reduce((acc,y,j)=>acc|((a[x]>>y&1)<<j),0))};
      const ts=comps.map(S=>{const g=sub(S);return truth(g,g.length)});
      const r=run([G('G',{n,c:t.c,tr:t.fo?'f':'u'}),...ts.slice(0,-1).map((x,j)=>G('C'+j,{op:'comp',src:'G',n:x.n,m:x.m}))]);check('S14 components: G',id,r[0],t);ts.slice(0,-1).forEach((x,j)=>check('S14 component',id,r[j+1],x));
      const r2=run([G('G',{n,m:t.m,c:t.c,D:t.D,dl:t.dl,chi:t.chi,al:t.al,nu:t.nu,om:t.om}),...ts.map((x,j)=>G('C'+j,{op:'comp',src:'G'}))]);ts.forEach((x,j)=>check('S15 component from G',id,r2[j+1],x))}
  }}
  return{bad:bad.slice(0,60),cnt}},{MAXN,STEP});
console.log(res.cnt);console.log(res.bad.length?res.bad.map(x=>x.join(' | ')).join('\n'):'NO VIOLATIONS');
await b.close()})();
