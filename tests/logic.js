const {chromium}=require('playwright');
(async()=>{const b=await chromium.launch({executablePath:'/opt/pw-browsers/chromium'});const errs=[];
const p=await b.newPage({viewport:{width:1500,height:950}});p.on('pageerror',e=>errs.push(e.message));
await p.goto('file:///home/claude/graph-playground/index.html');
await p.click('[data-act="part"][data-v="logic"]');
console.log('head:',await p.locator('.lgtab thead th').allInnerTexts());
console.log('rows:',await p.locator('.lgtab tbody tr').evaluateAll(a=>a.map(r=>(r.className||'ok')+':'+r.innerText.replace(/\s+/g,''))));
console.log('card:',(await p.locator('#card').innerText()).replace(/\n+/g,' | ').slice(0,700));
// build: D = A ∧ B, E = D → C  (should be a tautology)
await p.click('.lg [data-add="f"]');await p.locator('.lg select[data-k="a"]').last().selectOption('A').catch(()=>{});
let i=await p.locator('#lgobjs .qbox').count()-1;
await p.locator(`.lg select[data-i="${i}"][data-k="op"]`).selectOption('and');await p.locator(`.lg select[data-i="${i}"][data-k="a"]`).selectOption('A');await p.locator(`.lg select[data-i="${i}"][data-k="b"]`).selectOption('B');
await p.click('.lg [data-add="f"]');i++;
await p.locator(`.lg select[data-i="${i}"][data-k="op"]`).selectOption('imp');await p.locator(`.lg select[data-i="${i}"][data-k="a"]`).selectOption('D');await p.locator(`.lg select[data-i="${i}"][data-k="b"]`).selectOption('C');
console.log('texts:',await p.locator('.lgtxt').allInnerTexts());
console.log('self:',(await p.locator('#card').innerText()).split('כל פסוק בפני עצמו')[1].replace(/\n+/g,' | ').slice(0,500));
// type switch and delete
await p.locator('.lg select[data-i="1"][data-k="t"]').selectOption('f');console.log('after switch:',await p.locator('#lgobjs .name').allInnerTexts(),await p.locator('.lgtab tbody tr').count());
await p.locator('.lg [data-del="0"]').click();console.log('after delete p:',await p.locator('#lgobjs .name').allInnerTexts(),await p.locator('.lgtxt').allInnerTexts());
await p.click('[data-act="part"][data-v="graphs"]');console.log('back to graphs:',await p.locator('[data-act="mode"]').count()>0);
await p.click('[data-act="part"][data-v="logic"]');await p.screenshot({path:'lg.png'});
// independent check of the evaluator against JS on random formulas
const res=await p.evaluate(()=>{const ops=['not','and','or','imp','iff','xor'],ev={not:a=>!a,and:(a,b)=>a&&b,or:(a,b)=>a||b,imp:(a,b)=>!a||b,iff:(a,b)=>a===b,xor:(a,b)=>a!==b};let bad=0,n=0;
  for(let t=0;t<400;t++){const k=1+t%4,L=[];for(let i=0;i<k;i++)L.push({name:'pqrs'[i],t:'v'});const m=1+t%6;for(let j=0;j<m;j++){const op=ops[(t*7+j*3)%6],a=L[(t+j*5)%L.length].name,bn=L[(t*3+j)%L.length].name;L.push({name:'F'+j,t:'f',op,a,b:op==='not'?null:bn})}
    const r=LOGIC.solve(L);if(r.rows.length!==(1<<k))bad++;r.rows.forEach((row,ri)=>{const val={};L.forEach((x,i)=>{if(x.t==='v'){const vi='pqrs'.indexOf(x.name);val[x.name]=!((ri>>(k-1-vi))&1)}else val[x.name]=x.op==='not'?ev.not(val[x.a]):ev[x.op](val[x.a],val[x.b]);n++;if(val[x.name]!==row.vals[i])bad++})})}
  // known laws
  const taut=l=>LOGIC.solve(l).facts[l.length-1].kind;const V=(n)=>({name:n,t:'v'}),Fm=(name,op,a,b)=>({name,t:'f',op,a,b:b||null});
  const laws={deMorgan:taut([V('p'),V('q'),Fm('A','and','p','q'),Fm('B','not','A'),Fm('C','not','p'),Fm('D','not','q'),Fm('E','or','C','D'),Fm('F','iff','B','E')]),
    contrapositive:taut([V('p'),V('q'),Fm('A','imp','p','q'),Fm('B','not','q'),Fm('C','not','p'),Fm('D','imp','B','C'),Fm('E','iff','A','D')]),
    excludedMiddle:taut([V('p'),Fm('A','not','p'),Fm('B','or','p','A')]),contradiction:taut([V('p'),Fm('A','not','p'),Fm('B','and','p','A')]),converse:taut([V('p'),V('q'),Fm('A','imp','p','q'),Fm('B','imp','q','p'),Fm('C','iff','A','B')])};
  // modus tollens through the data
  const mt=LOGIC.solve([V('p'),V('q'),Object.assign(Fm('A','imp','p','q'),{given:'T'}),Object.assign(Fm('B','not','q'),{given:'T'}),Fm('C','not','p')]).facts[4].forced;
  const aff=LOGIC.solve([V('p'),Object.assign(V('q'),{given:'T'}),Object.assign(Fm('A','imp','p','q'),{given:'T'})]).facts[0].forced;
  return{bad,n,laws,mt,affirmingConsequent:aff}});
console.log(JSON.stringify(res));console.log('errs',errs);await b.close()})();
