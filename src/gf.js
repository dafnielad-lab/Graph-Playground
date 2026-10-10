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
/* ---- the sequence a_n itself: a recurrence read off the denominator, and a formula for every n ---- */
/* the denominator prod(1 - x^s) multiplied out, as integer coefficients q[0..deg] with q[0] = 1 */
function denomPoly(C){let q=[1n];for(const [s,m] of C.den)for(let t=0;t<m;t++){const o=Array.from({length:q.length+s},()=>0n);q.forEach((v,i)=>{o[i]+=v;o[i+s]-=v});q=o}return q}
/* F·Q = P gives a_n = -(q1·a_{n-1} + q2·a_{n-2} + ...) once n is past the degree of the numerator */
function recurrence(C){const q=denomPoly(C),degQ=q.length-1,T=numTerms(C),degP=C.A+(T.length?T[T.length-1][0]:0);
  return{terms:q.slice(1).map((v,i)=>[i+1,-v]).filter(([,v])=>v!==0n),degQ,from:Math.max(degP+1,degQ)}}
/* exact fractions with BigInt */
const gcd=(a,b)=>{a=a<0n?-a:a;b=b<0n?-b:b;while(b){[a,b]=[b,a%b]}return a};
const Fr=(n,d=1n)=>{if(d<0n){n=-n;d=-d}const g=gcd(n,d)||1n;return{n:n/g,d:d/g}},fadd=(a,b)=>Fr(a.n*b.d+b.n*a.d,a.d*b.d),fsub=(a,b)=>Fr(a.n*b.d-b.n*a.d,a.d*b.d),fmul=(a,b)=>Fr(a.n*b.n,a.d*b.d),fdiv=(a,b)=>Fr(a.n*b.d,a.d*b.n);
/* the polynomial of degree < k through k points (x_i, y_i), by exact elimination */
function fit(xs,ys){const k=xs.length,M=xs.map((x,i)=>{const row=[];let pw=1n;for(let j=0;j<k;j++){row.push(Fr(pw));pw*=BigInt(x)}row.push(Fr(ys[i]));return row});
  for(let c=0;c<k;c++){let p=c;while(p<k&&M[p][c].n===0n)p++;if(p===k)return null;[M[c],M[p]]=[M[p],M[c]];const pv=M[c][c];for(let j=c;j<=k;j++)M[c][j]=fdiv(M[c][j],pv);
    for(let r=0;r<k;r++)if(r!==c&&M[r][c].n!==0n){const f=M[r][c];for(let j=c;j<=k;j++)M[r][j]=fsub(M[r][j],fmul(f,M[c][j]))}}
  return M.map(row=>row[k])}
const evalPoly=(cf,n)=>{let t=Fr(0n),pw=1n;for(const c of cf){t=fadd(t,fmul(c,Fr(pw)));pw*=BigInt(n)}return t};
/* a_n is a polynomial in n on every residue class modulo the least common multiple of the steps, from n0 = deg P - deg Q + 1 on.
   The polynomials are found by fitting and are then checked on further terms; a class that fails the check is not shown. */
function formula(C){const k=C.den.reduce((t,[,m])=>t+m,0),T=numTerms(C);if(!k)return{k:0};
  const lcm=(a,b)=>a/Number(gcd(BigInt(a),BigInt(b)))*b,M=C.den.reduce((t,[s])=>lcm(t,s),1);if(M>12||k>10)return{k,M,skip:true};
  const degP=C.A+(T.length?T[T.length-1][0]:0),degQ=C.den.reduce((t,[s,m])=>t+s*m,0),n0=Math.max(0,degP-degQ+1),need=n0+M*(k+8)+M,a=byClosed(C,need),cls=[];
  for(let r=0;r<M;r++){const xs=[],ys=[];let n=n0+((r-n0)%M+M)%M;for(let j=0;j<k;j++,n+=M){xs.push(n);ys.push(a[n])}
    const cf=fit(xs,ys);if(!cf)return{k,M,skip:true};let good=true;for(let j=0;j<8;j++,n+=M){const v=evalPoly(cf,n);if(v.d!==1n||v.n!==a[n])good=false}if(!good)return{k,M,skip:true};
    while(cf.length>1&&cf[cf.length-1].n===0n)cf.pop();cls.push({r,cf})}
  const key=c=>c.cf.map(f=>f.n+'/'+f.d).join(','),same=cls.every(c=>key(c)===key(cls[0]));
  return{k,M,n0,cls:same?[{r:null,cf:cls[0].cf}]:cls,degP}}
/* ---- typesetting ---- */
const X=e=>e===0?'1':e===1?'x':`x<sup>${e}</sup>`,fr=(a,b)=>`<span class="gfr"><span>${a}</span><span>${b}</span></span>`;
const one=e=>`1 − ${X(e)}`,pw=(base,k)=>k===1?`(${base})`:`(${base})<sup>${k}</sup>`;
function openForm(s){/* first terms, dots, and the last term when there is one */
  const t=[];for(let j=0;j<Math.min(s.count,4);j++)t.push(X(s.e0+j*s.step));if(s.count===Infinity)t.push('…');else if(s.count>4){if(s.count>5)t.push('…');t.push(X(s.e0+(s.count-1)*s.step))}return `<span class="gbr">(</span>${t.join(' + ')}<span class="gbr">)</span>`}
/* a factor as a series in sigma notation: the index runs over the values of the variable when they are consecutive */
const sig=(from,to,term)=>`<span class="gsg"><span>${to}</span><span class="S">Σ</span><span>i = ${from}</span></span>${term}`;
const xe=(k,add)=>{const e=(k===1?'i':k+'i')+(add?` + ${add}`:'');return `x<sup>${e}</sup>`};
function sigmaForm(s){if(s.count===1)return X(s.e0);
  return s.d===1?sig(s.first,s.count===Infinity?'∞':s.first+s.count-1,xe(s.c,0)):sig(0,s.count===Infinity?'∞':s.count-1,xe(s.step,s.e0))}
/* the whole function as one series: the first terms that are not zero */
function seriesForm(a,N){const t=[];for(let n=0;n<=N&&t.length<7;n++)if(a[n]!==0n)t.push((a[n]===1n?'':a[n])+(n===0?(a[n]===1n?'1':''):X(n)));return t.join(' + ')+' + …'}
function factorClosed(s){const top=s.count===Infinity||s.count===1?X(s.e0):s.e0?`${X(s.e0)}(${one(s.step*s.count)})`:one(s.step*s.count);return s.count===1?top:fr(top,one(s.step))}
function closedHtml(C){const top=[C.A?X(C.A):''].concat(C.num.map(Lx=>`(${one(Lx)})`)).filter(Boolean).join(' ')||'1',bot=C.den.map(([s,m])=>pw(one(s),m)).join(' ');return bot?fr(top,bot):top}
function sumHtml(C){const T=numTerms(C),bot=C.den.map(([s,m])=>pw(one(s),m)).join(' ');if(T.length<2)return null;
  const top=T.map(([e,k],i)=>{const a=k<0n?-k:k,mon=X(C.A+e),body=a===1n?mon:(mon==='1'?String(a):`${a}${mon}`);return (i?(k<0n?' − ':' + '):(k<0n?'−':''))+body}).join('');return bot?fr(top,bot):top}
function sumSeries(C){const T=numTerms(C);if(!C.den.length||T.length>12)return null;const pure=C.den.length===1&&C.den[0][0]===1,k=pure?C.den[0][1]:0;
  const coef=pure?(k===1?'':`<span class="gbn"><span>n + ${k-1}</span><span>${k-1}</span></span>`):'b<sub>n</sub>';
  const html=T.map(([e,sg],i)=>{const a=sg<0n?-sg:sg,sh=C.A+e;return (i?(sg<0n?' − ':' + '):(sg<0n?'−':''))+(a===1n?'':a+'·')+`<span class="gsg"><span>∞</span><span class="S">Σ</span><span>n = 0</span></span>${coef}x<sup>n${sh?' + '+sh:''}</sup>`}).join('');
  if(pure)return{html,hint:'כל חזקה במונה מזיזה את הטור של המכנה.'};
  /* the series of 1 / denominator, with its own formula when there is one */
  const D={A:0,num:[],den:C.den},Fd=formula(D),bot=C.den.map(([s,m])=>pw(one(s),m)).join(' ');
  const def=`<div class="gin">${fr('1',bot)} = <span class="gsg"><span>∞</span><span class="S">Σ</span><span>n = 0</span></span>b<sub>n</sub>x<sup>n</sup>${Fd.cls?',   '+(Fd.cls.length===1?`b<sub>n</sub> = ${polyHtml(Fd.cls[0].cf)}`:`<span class="gcs">${Fd.cls.map(c=>`<span><span>b<sub>n</sub> = ${polyHtml(c.cf)}</span><span class="gcd">n ≡ ${c.r} (mod ${Fd.M})</span></span>`).join('')}</span>`):''}</div>`;
  return{html:html+def,hint:'כל חזקה במונה מזיזה את הטור של המכנה. המקדמים של הטור הזה מסומנים b.'}}
function explicitSeries(Fm,a){const t=[];for(let n=0;n<Fm.n0;n++)if(a[n]!==0n){const m=a[n]<0n?-a[n]:a[n];t.push((t.length?(a[n]<0n?' − ':' + '):(a[n]<0n?'−':''))+(m===1n?'':m)+(n===0?(m===1n?'1':''):X(n)))}
  const one=Fm.cls.length===1;
  return t.join('')+Fm.cls.map((c,i)=>(t.length||i?' + ':'')+`<span class="gsg"><span>∞</span><span class="S">Σ</span><span>n = ${Fm.n0}${one?'':`<br>n ≡ ${c.r} (mod ${Fm.M})`}</span></span><span class="gbr">(</span>${polyHtml(c.cf)}<span class="gbr">)</span>x<sup>n</sup>`).join('')}
function binomHtml(C){if(!(C.den.length===1&&C.den[0][0]===1))return null;const k=C.den[0][1],T=numTerms(C);if(T.length>12)return null;
  const term=e=>{const sh=C.A+e;return `<span class="gbn"><span>${sh?`n − ${sh} + ${k-1}`:`n + ${k-1}`}</span><span>${k-1}</span></span>`};
  return T.map(([e,sg],i)=>{const a=sg<0n?-sg:sg;return (i?(sg<0n?' − ':' + '):(sg<0n?'−':''))+(a===1n?'':a+'·')+term(e)}).join('')}
/* a polynomial in n with rational coefficients, over its common denominator */
function polyHtml(cf){let L=1n;for(const c of cf)L=L/gcd(L,c.d)*c.d;const ints=cf.map(c=>c.n*(L/c.d)),parts=[];
  for(let j=ints.length-1;j>=0;j--){const v=ints[j];if(v===0n)continue;const a=v<0n?-v:v,mon=j===0?'':j===1?'n':`n<sup>${j}</sup>`,body=mon?(a===1n?mon:`${a}${mon}`):String(a);parts.push((parts.length?(v<0n?' − ':' + '):(v<0n?'−':''))+body)}
  const top=parts.join('')||'0';return L===1n?top:fr(top,String(L))}
function recHtml(R){if(!R.terms.length)return null;if(R.terms.length>14)return null;
  return 'a<sub>n</sub> = '+R.terms.map(([j,v],i)=>{const a=v<0n?-v:v;return (i?(v<0n?' − ':' + '):(v<0n?'−':''))+(a===1n?'':a)+`a<sub>n − ${j}</sub>`}).join('')}
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
  const C=closed(S),a1=byProduct(S,N),a2=byClosed(C,N),sum=sumHtml(C),bin=binomHtml(C),R=recurrence(C),rec=recHtml(R),Fm=formula(C),sser=sumSeries(C);
  /* the recurrence and the formula are checked against the coefficients as well */
  let recOk=true,recN=0;if(rec)for(let n=R.from;n<=N;n++){let t=0n;for(const [j,v] of R.terms)t+=v*a1[n-j];recN++;if(t!==a1[n])recOk=false}
  let fmOk=true,fmN=0;if(Fm.cls)for(let n=Fm.n0;n<=N;n++){const c=Fm.cls.length===1?Fm.cls[0]:Fm.cls[n%Fm.M],v=evalPoly(c.cf,n);fmN++;if(v.d!==1n||v.n!==a1[n])fmOk=false}
  const startVals=rec?Array.from({length:Math.min(R.from,N+1)},(_,n)=>`a<sub>${n}</sub> = ${a1[n]}`).join(',  '):'';
  const fmHtml=!Fm.cls?null:Fm.cls.length===1?`a<sub>n</sub> = ${polyHtml(Fm.cls[0].cf)}`:`<span class="gcs">${Fm.cls.map(c=>`<span><span>a<sub>n</sub> = ${polyHtml(c.cf)}</span><span class="gcd">n ≡ ${c.r} (mod ${Fm.M})</span></span>`).join('')}</span>`;
  const early=Fm.cls&&Fm.n0>0?Array.from({length:Fm.n0},(_,n)=>`a<sub>${n}</sub> = ${a1[n]}`).join(',  '):'';
  /* verification: the ways must agree on every coefficient shown */
  let agree=true,counted=0,cntOk=true,binOk=true,binN=0;for(let n=0;n<=N;n++){if(a1[n]!==a2[n])agree=false;const b=byBinomial(C,n);if(b!==null){binN++;if(b!==a1[n])binOk=false}
    if(n<=Math.min(N,24)){const c=byCount(S,n,300000);if(c!==null){counted++;if(BigInt(c)!==a1[n])cntOk=false}}}
  const blk=(t,sub,body)=>`<section class="gfb"><h3>${t}</h3>${sub?`<p class="hint">${sub}</p>`:''}<div class="gfm fx">${body}</div></section>`;
  document.getElementById('main').innerHTML=`<div class="gfwrap">
    <div class="gfeq fx">${eq}</div>
    ${blk('הצורה הפתוחה','לכל משתנה סוגריים, ובהם חזקה אחת לכל ערך שהוא יכול לתרום לסכום.',`F(x) = ${S.map(openForm).join(' · ')}`)}
    ${blk('הצורה הסגורה, גורם לכל משתנה','כל סוגריים הם טור הנדסי.',`F(x) = ${S.map(factorClosed).join(' · ')}`)}
    ${blk('הצורה הסגורה המפושטת, כמכפלה','',`F(x) = ${closedHtml(C)}`)}
    ${blk('כמכפלת טורים','אותם סוגריים בכתיב סיגמא.',`F(x) = ${S.map(s=>`<span class="gbr">(</span>${sigmaForm(s)}<span class="gbr">)</span>`).join(' · ')}`)}
    ${sum?blk('אותה פונקציה, כסכום','המונה נפתח לסכום של חזקות.',`F(x) = ${sum}`):''}
    ${sser?blk('כסכום של טורים',sser.hint,`F(x) = ${sser.html}`):''}
    ${bin?blk('המקדם של x<sup>n</sup>, כנוסחה','בינום שהמספר העליון שלו שלילי שווה אפס.',`a<sub>n</sub> = ${bin}`):''}
    ${rec?blk('נוסחת נסיגה לסדרה',`מתקבלת מהכפלת שני האגפים במכנה והשוואת מקדמים. תקפה מ־<bdi dir="ltr" class="fx">n = ${R.from}</bdi> והלאה, עם תנאי ההתחלה שמתחתיה.`,`${rec}<div class="gin">${startVals}</div>`):''}
    ${fmHtml?blk('הסדרה בנוסחה מפורשת',(Fm.cls.length===1?'פולינום אחד':`פולינום לכל שארית של n בחלוקה ב־${Fm.M}`)+(Fm.n0>0?`, תקף מ־<bdi dir="ltr" class="fx">n = ${Fm.n0}</bdi> והלאה. האיברים שלפני כן רשומים מתחת.`:', תקף לכל n.'),`${fmHtml}${early?`<div class="gin">${early}</div>`:''}`):Fm.skip?`<section class="gfb"><h3>הסדרה בנוסחה מפורשת</h3><p class="hint">לא מוצגת כאן: הנוסחה מתפצלת ליותר מדי מקרים לפי השארית של n.</p></section>`:''}
    ${blk('כטור אחד','המקדם של כל חזקה הוא מספר הפתרונות.',`F(x) = <span class="gsg"><span>∞</span><span class="S">Σ</span><span>n = 0</span></span>a<sub>n</sub>x<sup>n</sup> = ${seriesForm(a1,N)}`)}
    ${fmHtml?blk('כטור אחד, עם הנוסחה המפורשת',Fm.n0>0?'האיברים הראשונים רשומים בנפרד, ומהם והלאה המקדם הוא הנוסחה.':'המקדם של כל חזקה הוא הנוסחה המפורשת.',`F(x) = ${explicitSeries(Fm,a1)}`):''}
  </div>`;
  const row=(lab,st,txt)=>`<div class="gfv ${st}"><b>${st==='ok'?'✓':st==='bad'?'✗':'·'}</b><span>${lab}</span><span class="lab">${txt}</span></div>`;
  document.getElementById('card').innerHTML=`<div class="gfcard"><div class="cardhead"><h2>מספר הפתרונות</h2></div>
    <label class="cell gft">n =<input type="number" min="0" max="200" class="rn" dir="ltr" id="gfn" value="${TARGET}"></label>
    <div class="gfans fx">a<sub>${TARGET}</sub> = <b>${a1[TARGET]}</b></div>
    <h3>אימות</h3>
    ${row('מכפלת הטורים מול הצורה הסגורה',agree?'ok':'bad',`n = 0 … ${N}`)}
    ${binN?row('הנוסחה עם הבינומים',binOk?'ok':'bad',`n = 0 … ${N}`):row('הנוסחה עם הבינומים','na','לא קיימת כאן: במכנה יש גורם שאינו (1 − x)')}
    ${counted?row('ספירת הפתרונות אחד אחד',cntOk?'ok':'bad',`n = 0 … ${counted-1}`):row('ספירת הפתרונות אחד אחד','na','יותר מדי פתרונות')}
    ${rec?row('נוסחת הנסיגה',recOk?'ok':'bad',`n = ${R.from} … ${N}`):''}
    ${Fm.cls?row('הנוסחה המפורשת',fmOk?'ok':'bad',`n = ${Fm.n0} … ${N}`):''}
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
  const R=recurrence(C),Fm=formula(C);
  return{rec:a.map((_,n)=>{if(n<R.from)return null;let t=0n;for(const [j,v] of R.terms)t+=v*a[n-j];return String(t)}),formula:a.map((_,n)=>{if(!Fm.cls||n<Fm.n0)return null;const c=Fm.cls.length===1?Fm.cls[0]:Fm.cls[n%Fm.M],v=evalPoly(c.cf,n);return v.d===1n?String(v.n):'frac'}),fm:Fm.cls?Fm.cls.length:0,product:a.map(String),closed:b.map(String),binomial:a.map((_,n)=>{const x=byBinomial(C,n);return x===null?null:String(x)}),count:a.map((_,n)=>n<=18?byCount(S,n,400000):null),C}},
render(){
  document.getElementById('conds').innerHTML=`<div class="qb gf"><div class="colhead"><h2>המשתנים</h2><span class="lab">תנאי לכל משתנה</span></div><div id="gfobjs" class="qlist"></div>
    <div class="qbox"><div class="addrow"><button class="addb" data-add="1">+ משתנה</button></div><p class="hint">המשתנים הם מספרים טבעיים, כולל אפס. מקדם בסכום גדול מאחת אומר שהמשתנה נספר כמה פעמים, כמו מטבע בשווי המקדם.</p></div></div>`;
  renderAll()}};
})();
