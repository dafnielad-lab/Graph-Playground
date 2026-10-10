/* ---------- the generating-functions playground: x1 + x2 + ... = n over the naturals, with a condition on every variable ---------- */
const GF=(()=>{
/* each variable: c (its coefficient in the sum), and the set of values it may take: lo <= v <= hi (hi null = no bound), v ≡ r (mod d) */
let VS=[{c:1,type:'any'},{c:1,type:'range',lo:1,hi:6},{c:1,type:'even'}],TARGET=10,SHOW=20;
const TYPES={any:'כל טבעי, כולל אפס',min:'לפחות',max:'לכל היותר',range:'בין שני ערכים',exact:'ערך קבוע',even:'זוגי',odd:'אי-זוגי',mult:'כפולה של',mod:'שארית נתונה בחלוקה',gen:'צירוף: תחום, קפיצה ושארית'};
const NEED={any:[],min:['lo'],max:['hi'],range:['lo','hi'],exact:['lo'],even:[],odd:[],mult:['d'],mod:['d','r'],gen:['lo','hi','d','r']};
const LAB={lo:'מ־',hi:'עד',d:'קפיצה',r:'שארית'};
const int=(x,def)=>{const n=Math.floor(Number(x));return Number.isFinite(n)&&String(x).trim()!==''?n:def};
/* the allowed values as: first value, step, number of values (Infinity when unbounded); null when no value is allowed */
function spec(v){let lo=0,hi=Infinity,d=1,r=0;const t=v.type;
  if(t==='min')lo=int(v.lo,0);else if(t==='max')hi=int(v.hi,0);else if(t==='range'){lo=int(v.lo,0);hi=int(v.hi,lo)}else if(t==='exact'){lo=hi=int(v.lo,0)}
  else if(t==='even')d=2;else if(t==='odd'){d=2;r=1}else if(t==='mult')d=Math.max(1,int(v.d,2));else if(t==='mod'){d=Math.max(1,int(v.d,2));r=int(v.r,0)}
  else if(t==='gen'){lo=int(v.lo,0);hi=v.hi===''||v.hi===undefined||v.hi===null?Infinity:int(v.hi,Infinity);d=Math.max(1,int(v.d,1));r=int(v.r,0)}
  lo=Math.max(0,lo);r=((r%d)+d)%d;const first=lo+((r-lo)%d+d)%d;if(first>hi)return null;
  const c=Math.max(1,int(v.c,1));return{first,d,count:hi===Infinity?Infinity:Math.floor((hi-first)/d)+1,c,e0:c*first,step:c*d}}
/* ---- exact arithmetic on truncated series, with BigInt ---- */
const zero=N=>Array.from({length:N+1},()=>0n);
const mul=(a,b,N)=>{const o=zero(N);for(let i=0;i<=N;i++)if(a[i])for(let j=0;i+j<=N;j++)if(b[j])o[i+j]+=a[i]*b[j];return o};
/* way 1: the definition. Each factor is the series of its allowed exponents; multiply them. */
function byProduct(S,N){let p=zero(N);p[0]=1n;for(const s of S){const f=zero(N);for(let j=0;j<s.count&&s.e0+j*s.step<=N;j++)f[s.e0+j*s.step]=1n;p=mul(p,f,N)}return p}
/* way 2: the closed form. x^A * prod(1 - x^L) / prod(1 - x^s): expand the numerator, then divide by each (1 - x^s) as a running sum. */
function closed(S){let A=0;const num=[],den=new Map();
  for(const s of S){A+=s.e0;if(s.count===1)continue;den.set(s.step,(den.get(s.step)||0)+1);if(s.count!==Infinity)num.push(s.step*s.count)}
  /* cancel (1 - x^L) against (1 - x^s) when L = s */
  for(let i=num.length-1;i>=0;i--)if(den.get(num[i])){den.set(num[i],den.get(num[i])-1);if(!den.get(num[i]))den.delete(num[i]);num.splice(i,1)}
  return{A,num:num.sort((a,b)=>a-b),den:[...den.entries()].sort((a,b)=>a[0]-b[0])}}
function numTerms(C){/* prod(1 - x^L) as a list of signed monomials */
  let T=new Map([[0,1n]]);for(const Lx of C.num){const U=new Map(T);for(const [e,k] of T)U.set(e+Lx,(U.get(e+Lx)||0n)-k);T=U}
  return[...T.entries()].filter(([,k])=>k!==0n).sort((a,b)=>a[0]-b[0])}
function byClosed(C,N){const p=zero(N);for(const [e,k] of numTerms(C))if(C.A+e<=N)p[C.A+e]+=k;for(const [s,mult] of C.den)for(let t=0;t<mult;t++)for(let i=s;i<=N;i++)p[i]+=p[i-s];return p}
/* way 3: count the solutions themselves, one by one (only while there are few enough) */
function byCount(S,n,cap){let cnt=0,steps=0;const go=(i,rest)=>{if(steps>cap)return;if(i===S.length){if(rest===0)cnt++;return}const s=S[i];
    for(let j=0;j<s.count;j++){const e=s.e0+j*s.step;if(e>rest)break;steps++;go(i+1,rest-e)}};go(0,n);return steps>cap?null:cnt}
const binom=(n,k)=>{if(k<0n||n<k)return 0n;let r=1n;for(let i=1n;i<=k;i++)r=r*(n-k+i)/i;return r};
/* way 4: when every denominator is (1 - x), the coefficient is a signed sum of binomials */
function byBinomial(C,n){if(!(C.den.length===1&&C.den[0][0]===1)&&C.den.length!==0)return null;const k=C.den.length?C.den[0][1]:0;let t=0n;
  for(const [e,sg] of numTerms(C)){const m=n-C.A-e;if(m<0)continue;t+=sg*(k===0?(m===0?1n:0n):binom(BigInt(m+k-1),BigInt(k-1)))}return t}
/* ---- typesetting ---- */
const X=e=>e===0?'1':e===1?'x':`x<sup>${e}</sup>`,fr=(a,b)=>`<span class="gfr"><span>${a}</span><span>${b}</span></span>`;
const one=e=>`1 − ${X(e)}`,pw=(base,k)=>k===1?`(${base})`:`(${base})<sup>${k}</sup>`;
function openForm(s){/* first terms, dots, and the last term when there is one */
  const t=[];for(let j=0;j<Math.min(s.count,4);j++)t.push(X(s.e0+j*s.step));if(s.count===Infinity)t.push('…');else if(s.count>4){if(s.count>5)t.push('…');t.push(X(s.e0+(s.count-1)*s.step))}return `<span class="gbr">(</span>${t.join(' + ')}<span class="gbr">)</span>`}
function factorClosed(s){const top=s.count===Infinity||s.count===1?X(s.e0):s.e0?`${X(s.e0)}(${one(s.step*s.count)})`:one(s.step*s.count);return s.count===1?top:fr(top,one(s.step))}
function closedHtml(C){const top=[C.A?X(C.A):''].concat(C.num.map(Lx=>`(${one(Lx)})`)).filter(Boolean).join(' ')||'1',bot=C.den.map(([s,m])=>pw(one(s),m)).join(' ');return bot?fr(top,bot):top}
function sumHtml(C){const T=numTerms(C),bot=C.den.map(([s,m])=>pw(one(s),m)).join(' ');if(T.length<2)return null;
  const top=T.map(([e,k],i)=>{const a=k<0n?-k:k,mon=X(C.A+e),body=a===1n?mon:(mon==='1'?String(a):`${a}${mon}`);return (i?(k<0n?' − ':' + '):(k<0n?'−':''))+body}).join('');return bot?fr(top,bot):top}
function binomHtml(C){if(!(C.den.length===1&&C.den[0][0]===1))return null;const k=C.den[0][1],T=numTerms(C);if(T.length>12)return null;
  const term=e=>{const sh=C.A+e;return `<span class="gbn"><span>${sh?`n − ${sh} + ${k-1}`:`n + ${k-1}`}</span><span>${k-1}</span></span>`};
  return T.map(([e,sg],i)=>{const a=sg<0n?-sg:sg;return (i?(sg<0n?' − ':' + '):(sg<0n?'−':''))+(a===1n?'':a+'·')+term(e)}).join('')}
const esc=x=>String(x??'').replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const opt=(list,cur)=>list.map(([v,l])=>`<option value="${v}" ${v===cur?'selected':''}>${l}</option>`).join('');
const nm=i=>`x<sub>${i+1}</sub>`;
function describe(v,s){if(!s)return 'אין ערך מותר';const set=s.count===Infinity?`${s.first}, ${s.first+s.d}, ${s.first+2*s.d}, …`:s.count<=5?Array.from({length:s.count},(_,j)=>s.first+j*s.d).join(', '):`${s.first}, ${s.first+s.d}, …, ${s.first+(s.count-1)*s.d}`;return `{${set}}`}
function renderList(){
  document.getElementById('gfobjs').innerHTML=VS.map((v,i)=>{const s=spec(v);
    return `<div class="qbox"><div class="qrow"><span class="name v gfn">${nm(i)}</span><select data-i="${i}" data-k="type" aria-label="תנאי">${opt(Object.entries(TYPES),v.type)}</select><button class="x" data-del="${i}" aria-label="הסר משתנה" ${VS.length>1?'':'disabled'}>×</button></div>
      <div class="qrow">${NEED[v.type].map(k=>`<label class="cell">${LAB[k]}<input type="number" min="0" class="rn" dir="ltr" data-i="${i}" data-k="${k}" value="${esc(v[k])}" placeholder="${k==='hi'?'∞':'0'}"></label>`).join('')}<label class="cell">מקדם בסכום<input type="number" min="1" class="rn" dir="ltr" data-i="${i}" data-k="c" value="${esc(v.c)}"></label></div>
      <div class="gfset fx">${nm(i)} ∈ ${describe(v,s)}</div></div>`}).join('')}
function renderMain(){
  const S=VS.map(spec),ok=S.every(Boolean),N=Math.max(SHOW,TARGET);
  const eq=VS.map((v,i)=>`${int(v.c,1)>1?int(v.c,1):''}${nm(i)}`).join(' + ')+' = n';
  if(!ok){document.getElementById('main').innerHTML=`<div class="gfwrap"><div class="gfeq fx">${eq}</div><div class="qwarn">לאחד המשתנים אין אף ערך מותר, ולכן אין פתרונות לאף n.</div></div>`;document.getElementById('card').innerHTML='';return}
  const C=closed(S),a1=byProduct(S,N),a2=byClosed(C,N),sum=sumHtml(C),bin=binomHtml(C);
  /* verification: the ways must agree on every coefficient shown */
  let agree=true,counted=0,cntOk=true,binOk=true,binN=0;for(let n=0;n<=N;n++){if(a1[n]!==a2[n])agree=false;const b=byBinomial(C,n);if(b!==null){binN++;if(b!==a1[n])binOk=false}
    if(n<=Math.min(N,24)){const c=byCount(S,n,300000);if(c!==null){counted++;if(BigInt(c)!==a1[n])cntOk=false}}}
  const blk=(t,sub,body)=>`<section class="gfb"><h3>${t}</h3>${sub?`<p class="hint">${sub}</p>`:''}<div class="gfm fx">${body}</div></section>`;
  document.getElementById('main').innerHTML=`<div class="gfwrap">
    <div class="gfeq fx">${eq}</div>
    ${blk('הצורה הפתוחה','לכל משתנה סוגריים, ובהם חזקה אחת לכל ערך שהוא יכול לתרום לסכום.',`F(x) = ${S.map(openForm).join(' · ')}`)}
    ${blk('הצורה הסגורה, גורם לכל משתנה','כל סוגריים הם טור הנדסי.',`F(x) = ${S.map(factorClosed).join(' · ')}`)}
    ${blk('הצורה הסגורה המפושטת, כמכפלה','',`F(x) = ${closedHtml(C)}`)}
    ${sum?blk('אותה פונקציה, כסכום','המונה נפתח לסכום של חזקות.',`F(x) = ${sum}`):''}
    ${bin?blk('המקדם של x<sup>n</sup>, כנוסחה','בינום שהמספר העליון שלו שלילי שווה אפס.',`a<sub>n</sub> = ${bin}`):''}
  </div>`;
  const row=(lab,st,txt)=>`<div class="gfv ${st}"><b>${st==='ok'?'✓':st==='bad'?'✗':'·'}</b><span>${lab}</span><span class="lab">${txt}</span></div>`;
  document.getElementById('card').innerHTML=`<div class="gfcard"><div class="cardhead"><h2>מספר הפתרונות</h2></div>
    <label class="cell gft">n =<input type="number" min="0" max="200" class="rn" dir="ltr" id="gfn" value="${TARGET}"></label>
    <div class="gfans fx">a<sub>${TARGET}</sub> = <b>${a1[TARGET]}</b></div>
    <h3>אימות</h3>
    ${row('מכפלת הטורים מול הצורה הסגורה',agree?'ok':'bad',`n = 0 … ${N}`)}
    ${binN?row('הנוסחה עם הבינומים',binOk?'ok':'bad',`n = 0 … ${N}`):row('הנוסחה עם הבינומים','na','לא קיימת כאן: במכנה יש גורם שאינו (1 − x)')}
    ${counted?row('ספירת הפתרונות אחד אחד',cntOk?'ok':'bad',`n = 0 … ${counted-1}`):row('ספירת הפתרונות אחד אחד','na','יותר מדי פתרונות')}
    <p class="hint">כל שורה היא חישוב נפרד של אותם מקדמים. סימן ✓ אומר שהתוצאות זהות בכל הטווח.</p>
    <h3>המקדמים הראשונים</h3><div class="gfco" dir="ltr">${Array.from({length:SHOW+1},(_,n)=>`<span class="${n===TARGET?'cur':''}"><i>${n}</i><b>${a1[n]}</b></span>`).join('')}</div></div>`}
function renderAll(){renderList();renderMain()}
document.addEventListener('input',ev=>{const t=ev.target;if(t.id==='gfn'){TARGET=Math.max(0,Math.min(200,int(t.value,0)));renderMain();const e=document.getElementById('gfn');if(e){e.focus()}return}
  if(!t.closest||!t.closest('.gf'))return;const i=Number(t.dataset.i),k=t.dataset.k;if(!VS[i]||!k||k==='type')return;VS[i][k]=t.value;
  const s=spec(VS[i]),el=t.closest('.qbox').querySelector('.gfset');if(el)el.innerHTML=`${nm(i)} ∈ ${describe(VS[i],s)}`;renderMain()});
document.addEventListener('change',ev=>{const t=ev.target;if(!t.closest||!t.closest('.gf')||t.dataset.k!=='type')return;const v=VS[Number(t.dataset.i)];v.type=t.value;
  if(NEED[v.type].includes('lo')&&(v.lo===undefined||v.lo===''))v.lo=v.type==='min'?1:0;if(NEED[v.type].includes('hi')&&v.type!=='gen'&&(v.hi===undefined||v.hi===''))v.hi=5;if(NEED[v.type].includes('d')&&(v.d===undefined||v.d===''))v.d=v.type==='gen'?1:3;if(NEED[v.type].includes('r')&&(v.r===undefined||v.r===''))v.r=v.type==='gen'?0:1;renderAll()});
document.addEventListener('click',ev=>{if(!ev.target.closest||!ev.target.closest('.gf'))return;const a=ev.target.closest('[data-add]'),d=ev.target.closest('[data-del]');
  if(a&&VS.length<12){VS.push({c:1,type:'any'});renderAll()}else if(d&&VS.length>1){VS.splice(Number(d.dataset.del),1);renderAll()}});
return{
/* for tests: coefficients by each way, for a list of variables */
solve(list,N){const S=list.map(spec);if(!S.every(Boolean))return null;const C=closed(S),a=byProduct(S,N),b=byClosed(C,N);
  return{product:a.map(String),closed:b.map(String),binomial:a.map((_,n)=>{const x=byBinomial(C,n);return x===null?null:String(x)}),count:a.map((_,n)=>n<=18?byCount(S,n,400000):null),C}},
render(){
  document.getElementById('conds').innerHTML=`<div class="qb lg gf"><div class="colhead"><h2>המשתנים</h2><span class="lab">תנאי לכל משתנה</span></div><div id="gfobjs" class="qlist"></div>
    <div class="qbox"><div class="addrow"><button class="addb" data-add="1">+ משתנה</button></div><p class="hint">המשתנים הם מספרים טבעיים, כולל אפס. מקדם בסכום גדול מאחת אומר שהמשתנה נספר כמה פעמים, כמו מטבע בשווי המקדם.</p></div></div>`;
  renderAll()}};
})();
