const {chromium}=require('playwright');
(async()=>{const b=await chromium.launch({executablePath:'/opt/pw-browsers/chromium'});const errs=[];
const p=await b.newPage({viewport:{width:1500,height:950}});p.on('pageerror',e=>errs.push(e.message));
await p.goto('file:///home/claude/graph-playground/index.html');await p.click('[data-act="part"][data-v="gf"]');
console.log((await p.locator('#main').innerText()).replace(/\n+/g,' | ').slice(0,900));
console.log((await p.locator('#card').innerText()).replace(/\n+/g,' | ').slice(0,500));
await p.screenshot({path:'gf.png',fullPage:true});
// independent check: random variable lists, four ways must agree; plus an independent brute force written here
const res=await p.evaluate(()=>{const types=['any','min','max','range','exact','even','odd','mult','mod','gen'];let bad=[],n=0,fm=0;
  const allowed=(v,x)=>{const t=v.type,lo=Number(v.lo||0),hi=v.hi===''||v.hi===undefined?Infinity:Number(v.hi),d=Number(v.d||1),r=Number(v.r||0);
    if(t==='any')return true;if(t==='min')return x>=lo;if(t==='max')return x<=hi;if(t==='range')return x>=lo&&x<=hi;if(t==='exact')return x===lo;if(t==='even')return x%2===0;if(t==='odd')return x%2===1;if(t==='mult')return x%d===0;if(t==='mod')return x%d===r%d;return x>=lo&&x<=hi&&x%d===r%d};
  for(let t=0;t<300;t++){const k=1+t%4,L=[];for(let i=0;i<k;i++){const ty=types[(t*3+i*7)%10];L.push({type:ty,c:1+((t+i)%5===0?1:0)+((t+i)%11===0?1:0),lo:(t+i)%4,hi:(t+i)%4+((t*5+i)%6),d:1+(t+2*i)%4,r:(t+i)%3})}
    const N=40,R=GF.solve(L,N);if(R){fm+=R.fm?1:0}const brute=m=>{let c=0;const go=(i,rest)=>{if(i===L.length){if(rest===0)c++;return}for(let x=0;x*L[i].c<=rest;x++)if(allowed(L[i],x))go(i+1,rest-x*L[i].c)};go(0,m);return c};
    if(!R){let any=false;for(let m=0;m<=N;m++)if(brute(m))any=true;if(any)bad.push(['null but solutions',JSON.stringify(L)]);continue}
    for(let m=0;m<=N;m++){n++;const tr=String(brute(m));if(R.product[m]!==tr||R.closed[m]!==tr||(R.rec[m]!==null&&R.rec[m]!==tr)||(R.formula[m]!==null&&R.formula[m]!==tr)||(R.binomial[m]!==null&&R.binomial[m]!==tr)||(R.count[m]!==null&&String(R.count[m])!==tr)){bad.push([m,tr,R.product[m],R.closed[m],R.binomial[m],JSON.stringify(L)]);break}}}
  // known: x1+x2+x3=n, no conditions: C(n+2,2); dice: two dice sum 7 -> 6
  const k1=GF.solve([{type:'any',c:1},{type:'any',c:1},{type:'any',c:1}],10).product[10],dice=GF.solve([{type:'range',lo:1,hi:6,c:1},{type:'range',lo:1,hi:6,c:1}],12).product[7],coins=GF.solve([{type:'any',c:1},{type:'any',c:5},{type:'any',c:10}],100).closed[100];
  return{bad:bad.slice(0,4),n,withFormula:fm,k1,dice,coins}});
console.log(JSON.stringify(res));console.log('errs',errs);await b.close()})();
