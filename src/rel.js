/* ---------- the relations playground: a relation on a small set, as a directed graph, a matrix and a set of pairs ---------- */
const REL=(()=>{
const MAXN=12,esc=s=>String(s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
/* a relation on n elements: one bit row per element, bit j of row i says (i, j) is in the relation */
const empty=n=>new Array(n).fill(0),full=n=>new Array(n).fill((1<<n)-1),ident=n=>empty(n).map((_,i)=>1<<i);
const has=(M,i,j)=>M[i]>>j&1,union=(P,Q)=>P.map((r,i)=>r|Q[i]),inter=(P,Q)=>P.map((r,i)=>r&Q[i]),diff=(P,Q)=>P.map((r,i)=>r&~Q[i]);
const compl=M=>{const n=M.length;return M.map(r=>~r&((1<<n)-1))};
const inverse=M=>{const n=M.length,R=empty(n);for(let i=0;i<n;i++)for(let j=0;j<n;j++)if(has(M,i,j))R[j]|=1<<i;return R};
/* PQ: (a, c) is in it when some b has (a, b) in P and (b, c) in Q */
const compose=(P,Q)=>{const n=P.length;return P.map(r=>{let o=0;for(let b=0;b<n;b++)if(r>>b&1)o|=Q[b];return o})};
const tclose=M=>{const n=M.length,T=M.slice();for(let k=0;k<n;k++)for(let i=0;i<n;i++)if(T[i]>>k&1)T[i]|=T[k];return T};
const same=(P,Q)=>P.every((r,i)=>r===Q[i]),subset=(P,Q)=>P.every((r,i)=>(r&~Q[i])===0);
const size=M=>M.reduce((t,r)=>{while(r){t++;r&=r-1}return t},0);
const pairs=M=>{const o=[];for(let i=0;i<M.length;i++)for(let j=0;j<M.length;j++)if(has(M,i,j))o.push([i,j]);return o};
/* the five properties, each with a witness when it fails: pairs that are in the relation (inn) and pairs that are missing (out) */
function analyze(M){const n=M.length,P={};
  const set=(k,ok,inn,out)=>{P[k]={ok,inn:inn||[],out:out||[]}};
  { let w=-1;for(let a=0;a<n&&w<0;a++)if(!has(M,a,a))w=a;set('refl',w<0,[],w<0?[]:[[w,w]])}
  { let w=-1;for(let a=0;a<n&&w<0;a++)if(has(M,a,a))w=a;set('irr',w<0,w<0?[]:[[w,w]])}
  { let w=null;for(let a=0;a<n&&!w;a++)for(let b=0;b<n&&!w;b++)if(has(M,a,b)&&!has(M,b,a))w=[a,b];set('sym',!w,w?[w]:[],w?[[w[1],w[0]]]:[])}
  { let w=null;for(let a=0;a<n&&!w;a++)for(let b=a+1;b<n&&!w;b++)if(has(M,a,b)&&has(M,b,a))w=[a,b];set('anti',!w,w?[w,[w[1],w[0]]]:[])}
  { let w=null;for(let a=0;a<n&&!w;a++)for(let b=0;b<n&&!w;b++)if(has(M,a,b))for(let c=0;c<n&&!w;c++)if(has(M,b,c)&&!has(M,a,c))w=[a,b,c];set('trans',!w,w?[[w[0],w[1]],[w[1],w[2]]]:[],w?[[w[0],w[2]]]:[])}
  { let w=null;for(let a=0;a<n&&!w;a++)for(let b=a+1;b<n&&!w;b++)if(!has(M,a,b)&&!has(M,b,a))w=[a,b];set('comp',!w,[],w?[w,[w[1],w[0]]]:[])}
  P.equiv=P.refl.ok&&P.sym.ok&&P.trans.ok;P.weak=P.refl.ok&&P.anti.ok&&P.trans.ok;P.strict=P.irr.ok&&P.trans.ok;P.total=(P.weak||P.strict)&&P.comp.ok;return P}
/* the classes of an equivalence relation, in order of their first element */
function classes(M){const n=M.length,seen=new Array(n).fill(false),C=[];for(let a=0;a<n;a++)if(!seen[a]){const c=[];for(let b=0;b<n;b++)if(has(M,a,b)){c.push(b);seen[b]=true}C.push(c)}return C}
/* an order, weak or strict: its covering pairs, levels and special elements. (a, b) in the relation reads "a is below b" */
function order(M){const n=M.length,T=M.map((r,i)=>r&~(1<<i)),cover=[];
  for(let a=0;a<n;a++)for(let b=0;b<n;b++)if(has(T,a,b)){let mid=false;for(let c=0;c<n&&!mid;c++)if(has(T,a,c)&&has(T,c,b))mid=true;if(!mid)cover.push([a,b])}
  const lev=new Array(n).fill(-1),below=a=>{const o=[];for(let b=0;b<n;b++)if(has(T,b,a))o.push(b);return o};
  const L=a=>{if(lev[a]>=0)return lev[a];let m=0;for(const b of below(a))m=Math.max(m,L(b)+1);return lev[a]=m};for(let a=0;a<n;a++)L(a);
  const all=(1<<n)-1,min=[],max=[];let least=-1,greatest=-1;
  for(let a=0;a<n;a++){if(!below(a).length)min.push(a);if(!T[a])max.push(a);if((T[a]|1<<a)===all)least=a;if(below(a).length===n-1)greatest=a}
  /* a longest chain: walk down from a highest element through covering pairs */
  const chain=[];{let a=lev.indexOf(Math.max(...lev));chain.push(a);while(lev[a]>0){a=below(a).find(b=>lev[b]===lev[a]-1);chain.push(a)}chain.reverse()}
  /* a largest set of pairwise incomparable elements, by trying every subset */
  let anti=[];for(let s=1;s<=all;s++){let ok=true,k=0;for(let a=0;a<n&&ok;a++)if(s>>a&1){k++;if(T[a]&s)ok=false}if(ok&&k>anti.length){anti=[];for(let a=0;a<n;a++)if(s>>a&1)anti.push(a)}}
  const inc=[];for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)if(!has(T,a,b)&&!has(T,b,a))inc.push([a,b]);
  return{cover,lev,min,max,least,greatest,chain,anti,inc}}

/* ---------- state ---------- */
let KIND='div',PARAM={range:5,div:12,pow:3,custom:'a, b, c, d'},A=[],R=[],S=null,VIEW='R',HL=null,SEL=null;
const divisors=N=>{const o=[];for(let d=1;d<=N;d++)if(N%d===0)o.push(d);return o};
function buildSet(){let els=[];
  if(KIND==='range'){const n=Math.max(1,Math.min(MAXN,Math.floor(Number(PARAM.range))||1));els=Array.from({length:n},(_,i)=>({l:String(i+1),num:i+1}))}
  else if(KIND==='div'){const N=Math.max(1,Math.min(100000,Math.floor(Number(PARAM.div))||1));els=divisors(N).slice(0,MAXN).map(d=>({l:String(d),num:d}))}
  else if(KIND==='pow'){const k=Math.max(1,Math.min(3,Math.floor(Number(PARAM.pow))||1));for(let m=0;m<1<<k;m++){const e=[];for(let i=0;i<k;i++)if(m>>i&1)e.push(i+1);els.push({l:e.length?`{${e.join(',')}}`:'∅',mask:m,sz:e.length})}
    els.sort((x,y)=>x.sz-y.sz||x.mask-y.mask)}
  else{const seen=new Set();for(const t of String(PARAM.custom).split(/[,;\s]+/).filter(Boolean)){if(seen.has(t)||els.length>=MAXN)continue;seen.add(t);els.push({l:t.slice(0,6),num:/^-?\d+$/.test(t)?Number(t):undefined})}if(!els.length)els=[{l:'a'}]}
  return els}
const numeric=()=>A.every(e=>e.num!==undefined),sets=()=>A.every(e=>e.mask!==undefined);
/* ready-made relations; each needs elements of a suitable kind */
const PRE={empty:['היחס הריק',()=>true,()=>false],full:['היחס המלא, A × A',()=>true,()=>true],eq:['שוויון, a = b',()=>true,(a,b,i,j)=>i===j],
  div:['חלוקה, a מחלק את b',numeric,(a,b)=>a.num!==0&&b.num%a.num===0],le:['קטן או שווה, a ≤ b',numeric,(a,b)=>a.num<=b.num],lt:['קטן ממש, a < b',numeric,(a,b)=>a.num<b.num],
  mod2:['אותה שארית בחלוקה בשתיים',numeric,(a,b)=>(a.num-b.num)%2===0],mod3:['אותה שארית בחלוקה בשלוש',numeric,(a,b)=>(a.num-b.num)%3===0],
  cop:['זרים, המחלק המשותף הגדול הוא אחת',numeric,(a,b)=>{let x=Math.abs(a.num),y=Math.abs(b.num);while(y)[x,y]=[y,x%y];return x===1}],
  sub:['הכלה, a ⊆ b',sets,(a,b)=>(a.mask&~b.mask)===0],psub:['הכלה ממש, a ⊂ b',sets,(a,b)=>(a.mask&~b.mask)===0&&a.mask!==b.mask],dis:['זרות, a ∩ b = ∅',sets,(a,b)=>(a.mask&b.mask)===0],card:['אותו מספר איברים',sets,(a,b)=>a.sz===b.sz]};
const fill=k=>{const f=PRE[k][2],n=A.length,M=empty(n);for(let i=0;i<n;i++)for(let j=0;j<n;j++)if(f(A[i],A[j],i,j))M[i]|=1<<j;return M};
function resetSet(keep){const old=A.length;A=buildSet();const n=A.length;
  if(keep&&R.length){const m=(1<<n)-1,fit=M=>Array.from({length:n},(_,i)=>i<old?M[i]&m:0);R=fit(R);if(S)S=fit(S)}else{R=empty(n);if(S)S=empty(n)}HL=null;SEL=null}
A=buildSet();R=fill('div');

/* ---------- the views: the relation itself and what is built from it ---------- */
const VIEWS={R:{l:'היחס R',s:'R',f:()=>R},S:{l:'היחס S',s:'S',two:true,f:()=>S},
  inv:{l:'היחס ההפוך',s:'R⁻¹',def:'R⁻¹ = { (b, a) | (a, b) ∈ R }',f:()=>inverse(R)},
  cmp:{l:'המשלים',s:'R′',def:'R′ = (A × A) ∖ R',f:()=>compl(R)},
  sq:{l:'ההרכבה של R עם עצמו',s:'R²',def:'R² = RR = { (a, c) | ∃b: (a, b) ∈ R, (b, c) ∈ R }',f:()=>compose(R,R)},
  rc:{l:'הסגור הרפלקסיבי',s:'R ∪ I',def:'R ∪ I,   I = { (a, a) | a ∈ A }',add:true,f:()=>union(R,ident(R.length))},
  sc:{l:'הסגור הסימטרי',s:'R ∪ R⁻¹',def:'R ∪ R⁻¹',add:true,f:()=>union(R,inverse(R))},
  tc:{l:'הסגור הטרנזיטיבי',s:'R⁺',def:'R⁺ = R ∪ R² ∪ R³ ∪ …',add:true,f:()=>tclose(R)},
  ec:{l:'סגור השקילות',s:'E',def:'E = (R ∪ R⁻¹ ∪ I)⁺,   the smallest equivalence relation containing R',add:true,f:()=>tclose(union(union(R,inverse(R)),ident(R.length)))},
  uni:{l:'איחוד',s:'R ∪ S',two:true,def:'R ∪ S',f:()=>union(R,S)},int:{l:'חיתוך',s:'R ∩ S',two:true,def:'R ∩ S',f:()=>inter(R,S)},dif:{l:'הפרש',s:'R ∖ S',two:true,def:'R ∖ S',f:()=>diff(R,S)},
  rs:{l:'הרכבה RS',s:'RS',two:true,def:'RS = { (a, c) | ∃b: (a, b) ∈ R, (b, c) ∈ S }',f:()=>compose(R,S)},sr:{l:'הרכבה SR',s:'SR',two:true,def:'SR = { (a, c) | ∃b: (a, b) ∈ S, (b, c) ∈ R }',f:()=>compose(S,R)}};
const cur=()=>{if(!VIEWS[VIEW]||(VIEWS[VIEW].two&&!S))VIEW='R';return VIEWS[VIEW]};
const editable=()=>VIEW==='R'||VIEW==='S',target=()=>VIEW==='S'?S:R;

/* ---------- drawing ---------- */
const fx=t=>`<bdi dir="ltr" class="fx">${t}</bdi>`,pr=([i,j])=>`(${esc(A[i].l)}, ${esc(A[j].l)})`;
const rad=e=>Math.max(15,Math.min(27,4*e.l.length+10));
const DEFS=`<defs>${['a','h','b'].map(c=>`<marker id="rl${c}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="10" markerHeight="10" markerUnits="userSpaceOnUse" orient="auto-start-reverse"><path class="mk ${c}" d="M0,0 L10,5 L0,10 z"/></marker>`).join('')}</defs>`;
/* the directed graph: elements on a circle, an arrow for every pair, a small ring for a pair (a, a) */
function graphSvg(M,added,w){const n=A.length,W=440,cx=W/2,cy=W/2,RR=n===1?0:Math.min(170,60+n*14),pos=A.map((_,i)=>{const t=-Math.PI/2+2*Math.PI*i/n;return[cx+RR*Math.cos(t),cy+RR*Math.sin(t)]});
  const key=(i,j)=>i+','+j,winn=new Set((w?w.inn:[]).map(p=>key(...p))),wout=(w?w.out:[]);
  const cls=(i,j)=>winn.has(key(i,j))?'b':added&&has(added,i,j)?'h':'a';
  const arrow=(i,j,c,dash)=>{if(i===j){const [x,y]=pos[i],dx=n===1?0:(x-cx)/RR,dy=n===1?-1:(y-cy)/RR,r=rad(A[i]),lx=x+dx*(r+9),ly=y+dy*(r+9);return `<circle class="lp ${c}${dash?' ds':''}" cx="${lx.toFixed(1)}" cy="${ly.toFixed(1)}" r="11"/>`}
    const [x1,y1]=pos[i],[x2,y2]=pos[j],dx=x2-x1,dy=y2-y1,d=Math.hypot(dx,dy),ux=dx/d,uy=dy/d,both=has(M,j,i)&&has(M,i,j),off=both?13:0;
    const sx=x1+ux*rad(A[i]),sy=y1+uy*rad(A[i]),ex=x2-ux*(rad(A[j])+2),ey=y2-uy*(rad(A[j])+2),mx=(sx+ex)/2-uy*off*1.6,my=(sy+ey)/2+ux*off*1.6;
    return `<path class="ar ${c}${dash?' ds':''}" d="M${sx.toFixed(1)},${sy.toFixed(1)} Q${mx.toFixed(1)},${my.toFixed(1)} ${ex.toFixed(1)},${ey.toFixed(1)}" marker-end="url(#rl${c})"/>`};
  const E=pairs(M).sort((p,q)=>(cls(...p)==='a'?0:1)-(cls(...q)==='a'?0:1)).map(([i,j])=>arrow(i,j,cls(i,j),false)).join('')+wout.map(([i,j])=>arrow(i,j,'b',true)).join('');
  const N=A.map((e,i)=>`<g class="nd${SEL===i?' sel':''}" data-rn="${i}" tabindex="0" role="button" aria-label="${esc(e.l)}"><circle cx="${pos[i][0].toFixed(1)}" cy="${pos[i][1].toFixed(1)}" r="${rad(e)}"/><text x="${pos[i][0].toFixed(1)}" y="${pos[i][1].toFixed(1)}" style="font-size:${e.l.length>4?10:e.l.length>2?12:15}px">${esc(e.l)}</text></g>`).join('');
  return `<svg class="rlsvg" viewBox="0 0 ${W} ${W}" role="img" aria-label="הגרף המכוון של היחס">${DEFS}${E}${N}</svg>`}
function matrixHtml(M,added,w,name,small){const n=A.length,key=(i,j)=>i+','+j,wi=new Set((w?w.inn:[]).map(p=>key(...p))),wo=new Set((w?w.out:[]).map(p=>key(...p)));
  return `<div class="rlmw"><table class="rlmx${small?' sm':''}" dir="ltr"><thead><tr><th></th>${A.map(e=>`<th scope="col">${esc(e.l)}</th>`).join('')}</tr></thead><tbody>${A.map((e,i)=>`<tr><th scope="row">${esc(e.l)}</th>${A.map((f,j)=>{const on=has(M,i,j),c=[on?'on':'',on&&added&&has(added,i,j)?'h':'',wi.has(key(i,j))?'wi':'',wo.has(key(i,j))?'wo':'',i===j?'dg':''].filter(Boolean).join(' ');
    return `<td class="${c}">${name?`<button data-rc="${name}|${i}|${j}" aria-label="(${esc(e.l)}, ${esc(f.l)})" aria-pressed="${!!on}">${on?'●':''}</button>`:on?'●':''}</td>`}).join('')}</tr>`).join('')}</tbody></table></div>`}
/* the Hasse diagram: one level for every step of the longest chain below an element, lines for covering pairs only */
function hasseSvg(O){const n=A.length,H=Math.max(...O.lev)+1,by=Array.from({length:H},()=>[]);for(let a=0;a<n;a++)by[O.lev[a]].push(a);
  const W=440,gap=H>1?Math.min(86,340/(H-1)):0,hgt=Math.max(120,(H-1)*gap+80),x=new Array(n).fill(0);
  for(let l=0;l<H;l++){if(l>0){const bc=a=>{const lo=O.cover.filter(c=>c[1]===a).map(c=>x[c[0]]);return lo.length?lo.reduce((t,v)=>t+v,0)/lo.length:W/2};by[l].sort((p,q)=>bc(p)-bc(q))}
    by[l].forEach((a,i)=>{x[a]=W*(i+1)/(by[l].length+1)})}
  const y=a=>hgt-40-O.lev[a]*gap;
  return `<svg class="rlsvg hs" viewBox="0 0 ${W} ${hgt}" role="img" aria-label="דיאגרמת הסה">${O.cover.map(([a,b])=>`<line class="hl" x1="${x[a].toFixed(1)}" y1="${y(a).toFixed(1)}" x2="${x[b].toFixed(1)}" y2="${y(b).toFixed(1)}"/>`).join('')}${A.map((e,a)=>`<g class="nd"><circle cx="${x[a].toFixed(1)}" cy="${y(a).toFixed(1)}" r="${rad(e)}"/><text x="${x[a].toFixed(1)}" y="${y(a).toFixed(1)}" style="font-size:${e.l.length>4?10:e.l.length>2?12:15}px">${esc(e.l)}</text></g>`).join('')}</svg>`}

/* ---------- text ---------- */
const PROPS=[['refl','רפלקסיבי','∀a ∈ A:  (a, a) ∈ X','I ⊆ X'],['irr','אנטי-רפלקסיבי','∀a ∈ A:  (a, a) ∉ X','X ∩ I = ∅'],['sym','סימטרי','(a, b) ∈ X  ⇒  (b, a) ∈ X','X⁻¹ = X'],
  ['anti','אנטי-סימטרי','(a, b) ∈ X,  (b, a) ∈ X  ⇒  a = b','X ∩ X⁻¹ ⊆ I'],['trans','טרנזיטיבי','(a, b) ∈ X,  (b, c) ∈ X  ⇒  (a, c) ∈ X','X² ⊆ X'],['comp','כל שני איברים שונים ניתנים להשוואה','a ≠ b  ⇒  (a, b) ∈ X  or  (b, a) ∈ X','X ∪ X⁻¹ ∪ I = A × A']];
const witness=(k,p,s)=>p.ok?'':[...p.inn.map(q=>`${pr(q)} ∈ ${s}`),...p.out.map(q=>`${pr(q)} ∉ ${s}`)].join(',   ');
const setOf=a=>`{${a.map(i=>esc(A[i].l)).join(', ')}}`;
function renderSide(){const two=!!S,ok=Object.entries(PRE).filter(([k,v])=>v[1]());
  const preset=t=>`<select data-rp="${t}" aria-label="יחס מוכן"><option value="">יחס מוכן…</option>${ok.map(([k,v])=>`<option value="${k}">${v[0]}</option>`).join('')}</select>`;
  const par=KIND==='custom'?`<input type="text" dir="ltr" class="rlt" data-rk="custom" value="${esc(PARAM.custom)}" aria-label="האיברים, מופרדים בפסיקים">`:`<label class="cell">${KIND==='range'?'עד':KIND==='div'?'המחלקים של':'קבוצת החזקה של {1,…,k}, k ='}<input type="number" min="1" max="${KIND==='range'?MAXN:KIND==='pow'?3:100000}" class="rn" dir="ltr" data-rk="${KIND}" value="${esc(PARAM[KIND])}"></label>`;
  document.getElementById('rlobjs').innerHTML=`<div class="qbox"><div class="qrow"><span class="name">A</span><select data-rk="kind" aria-label="סוג הקבוצה">${[['range','המספרים מאחת עד'],['div','המחלקים של מספר'],['pow','קבוצת חזקה'],['custom','איברים שאני כותב']].map(([v,l])=>`<option value="${v}" ${v===KIND?'selected':''}>${l}</option>`).join('')}</select></div>
      <div class="qrow">${par}</div><div class="gfset fx">A = ${setOf(A.map((_,i)=>i))},   |A| = ${A.length}</div></div>
    <div class="qbox"><div class="qrow"><span class="name v">R</span>${preset('R')}</div>${matrixHtml(R,null,null,'R',true)}<p class="hint">לחיצה על תא מוסיפה או מסירה זוג. השורה היא האיבר הראשון בזוג.</p></div>
    ${two?`<div class="qbox"><div class="qrow"><span class="name v">S</span>${preset('S')}<button class="x" data-rs="0" aria-label="הסר את היחס השני">×</button></div>${matrixHtml(S,null,null,'S',true)}</div>`:`<div class="qbox"><div class="addrow"><button class="addb" data-rs="1">+ יחס שני, S</button></div><p class="hint">יחס שני מאפשר איחוד, חיתוך, הפרש והרכבה.</p></div>`}`}
function renderMain(){const v=cur(),M=v.f(),P=analyze(M),s=v.s,w=HL&&P[HL]&&!P[HL].ok?P[HL]:null,added=v.add?diff(M,R):null,nAdd=added?size(added):0,ps=pairs(M);
  const opts=Object.entries(VIEWS).filter(([k,x])=>!x.two||S).map(([k,x])=>`<option value="${k}" ${k===VIEW?'selected':''}>${x.l}${k==='R'||k==='S'?'':'  —  '+x.s}</option>`).join('');
  let extra='';
  if(P.equiv){const C=classes(M);extra+=`<section class="gfb"><h3>יחס שקילות: מחלקות השקילות</h3><p class="hint">המחלקות מחלקות את A לקבוצות זרות. מספר המחלקות: ${C.length}.</p><div class="rlcl">${C.map(c=>`<span class="rlc">${fx(`[${esc(A[c[0]].l)}] = ${setOf(c)}`)}</span>`).join('')}</div><div class="rlset">${fx(`A / ${s} = { ${C.map(setOf).join(', ')} }`)}</div></section>`}
  if(P.weak||P.strict){const O=order(M),li=(t,x)=>`<div class="rlf"><span>${t}</span>${fx(x)}</div>`;
    extra+=`<section class="gfb"><h3>${P.total?'סדר מלא':'סדר חלקי'}${P.strict?' (אנטי-רפלקסיבי)':' (רפלקסיבי)'}: דיאגרמת הסה</h3><p class="hint">קו עולה מאיבר לאיבר שמעליו רק כשאין איבר ביניהם. שאר הזוגות נובעים מטרנזיטיביות${P.weak?' ומרפלקסיביות':''}.</p>
      <div class="rlrow"><div class="rlg">${hasseSvg(O)}</div><div class="rlfacts">${li('איברים מינימליים',setOf(O.min))}${li('איברים מקסימליים',setOf(O.max))}${li('איבר קטן ביותר',O.least>=0?esc(A[O.least].l):'אין')}${li('איבר גדול ביותר',O.greatest>=0?esc(A[O.greatest].l):'אין')}
        ${li('שרשרת ארוכה ביותר',O.chain.map(i=>esc(A[i].l)).join(P.strict?'  ,  ':'  ,  ')+`   (${O.chain.length})`)}${li('אנטי-שרשרת גדולה ביותר',setOf(O.anti)+`   (${O.anti.length})`)}
        ${li('זוגות כיסוי, הקווים בדיאגרמה',String(O.cover.length))}${li('זוגות שאינם ניתנים להשוואה',O.inc.length?(O.inc.length<=8?O.inc.map(([a,b])=>`{${esc(A[a].l)}, ${esc(A[b].l)}}`).join(', '):String(O.inc.length)):'אין')}</div></div></section>`}
  document.getElementById('main').innerHTML=`<div class="gfwrap rl">
    <section class="gfb rlhead"><div class="rlbar"><label class="cell">מה מוצג<select data-rv="1">${opts}</select></label>${editable()?'':`<button class="btn sm" data-rset="1">קבע את התוצאה כ־R</button>`}</div>
      ${v.def?`<div class="rldef">${fx(v.def)}</div>`:''}${v.add?`<p class="hint">${nAdd?`זוגות שנוספו ל־R מסומנים בצבע. מספרם: ${nAdd}.`:'לא נוסף אף זוג: R כבר מקיים את התכונה.'}</p>`:''}</section>
    <div class="rlrow"><section class="gfb rlg"><h3>הגרף המכוון</h3>${graphSvg(M,added,w)}<p class="hint">${editable()?(SEL===null?'לחיצה על איבר ואחריה על איבר שני מוסיפה או מסירה חץ. לחיצה שנייה על אותו איבר: הזוג של האיבר עם עצמו.':`נבחר ${fx(esc(A[SEL].l))}. לחץ על האיבר שאליו החץ.`):'התצוגה הזאת מחושבת מ־R ואינה ניתנת לעריכה.'}</p></section>
      <section class="gfb rlm"><h3>המטריצה</h3>${matrixHtml(M,added,w,editable()?VIEW:null,false)}<p class="hint">נקודה בשורה של a ובעמודה של b: הזוג ${fx('(a, b)')} ביחס.</p></section></div>
    <section class="gfb"><h3>היחס כקבוצת זוגות</h3><div class="rlset">${fx(`${s} = ${ps.length?`{ ${ps.map(pr).join(', ')} }`:'∅'}`)}</div><div class="rlset sm">${fx(`|${s}| = ${ps.length},   |A × A| = ${A.length*A.length}`)}</div></section>
    ${extra}</div>`;
  /* the card: the properties, each with its definition and a counterexample when it fails */
  const X=t=>/ /.test(s)?t.replace(/X/g,`(${s})`):t.replace(/X(?=⁻¹|²)/g,s.length>1?`(${s})`:s).replace(/X/g,s);
  const kind=P.equiv&&P.weak?'גם יחס שקילות וגם סדר חלקי: זה יחס השוויון':P.equiv?'יחס שקילות':P.total?(P.strict?'סדר מלא (אנטי-רפלקסיבי)':'סדר מלא (רפלקסיבי)'):P.weak?'סדר חלקי (רפלקסיבי)':P.strict?'סדר חלקי (אנטי-רפלקסיבי)':'לא יחס שקילות ולא יחס סדר';
  const miss=(need,name)=>{const m=need.filter(k=>!P[k].ok).map(k=>PROPS.find(p=>p[0]===k)[1]);return m.length?`<div class="rlmiss"><b>${name}:</b> חסר ${m.join(', ')}</div>`:''};
  document.getElementById('card').innerHTML=`<div class="gfcard rl"><div class="cardhead"><h2>תכונות היחס</h2></div><div class="rlkind">${fx(esc(s))} <span>${kind}</span></div>
    ${PROPS.map(([k,name,df,alg])=>{const p=P[k],on=HL===k&&!p.ok;return `<div class="rlp ${p.ok?'ok':'no'}${on?' cur':''}"><div class="rlph"><b>${p.ok?'✓':'✗'}</b><span>${name}</span>${p.ok?'':`<button class="qexb" data-rh="${k}" aria-pressed="${on}">${on?'הסתר':'הראה'}</button>`}</div>
      <div class="rlpd">${fx(X(df))}</div><div class="rlpd alg">${fx(X(alg))}</div>${p.ok?'':`<div class="rlpw"><span>דוגמה נגדית</span>${fx(witness(k,p,esc(s)))}</div>`}</div>`}).join('')}
    ${!P.equiv?miss(['refl','sym','trans'],'יחס שקילות'):''}${!P.weak&&!P.strict?miss(['refl','anti','trans'],'סדר חלקי רפלקסיבי')+miss(['irr','trans'],'סדר חלקי אנטי-רפלקסיבי'):''}
    <p class="hint">${fx('I')} הוא יחס הזהות על A. בדוגמה נגדית, ״הראה״ מסמן את הזוגות בגרף ובמטריצה: קו מלא לזוג שביחס, קו מקווקו לזוג שחסר.</p></div>`}
function renderAll(){renderSide();renderMain()}
const toggle=(M,i,j)=>{M[i]^=1<<j};
document.addEventListener('click',ev=>{const t=ev.target;if(!t.closest||!t.closest('.rl'))return;
  const c=t.closest('[data-rc]'),nd=t.closest('[data-rn]'),h=t.closest('[data-rh]'),rs=t.closest('[data-rs]'),st=t.closest('[data-rset]');
  if(c){const [nm,i,j]=c.dataset.rc.split('|');toggle(nm==='S'?S:R,Number(i),Number(j));SEL=null;renderAll()}
  else if(nd&&editable()){const i=Number(nd.dataset.rn);if(SEL===null){SEL=i;renderMain()}else{toggle(target(),SEL,i);SEL=null;renderAll()}}
  else if(h){HL=HL===h.dataset.rh?null:h.dataset.rh;renderMain()}
  else if(rs){if(rs.dataset.rs==='1'){S=empty(A.length)}else{S=null}renderAll()}
  else if(st){R=cur().f().slice();VIEW='R';HL=null;renderAll()}});
document.addEventListener('keydown',ev=>{const nd=ev.target.closest&&ev.target.closest('.rl [data-rn]');if(nd&&(ev.key==='Enter'||ev.key===' ')){ev.preventDefault();nd.dispatchEvent(new MouseEvent('click',{bubbles:true}))}});
document.addEventListener('change',ev=>{const t=ev.target;if(!t.closest||!t.closest('.rl'))return;
  if(t.dataset.rv){VIEW=t.value;HL=null;SEL=null;renderMain()}
  else if(t.dataset.rp){if(t.value){const M=fill(t.value);if(t.dataset.rp==='S')S=M;else R=M;HL=null;renderAll()}}
  else if(t.dataset.rk==='kind'){KIND=t.value;resetSet(false);R=fill(KIND==='div'?'div':KIND==='pow'?'sub':KIND==='range'?'le':'empty');renderAll()}
  else if(t.dataset.rk){PARAM[t.dataset.rk]=t.value;const was=KIND;resetSet(was==='range');if(was==='div')R=fill('div');else if(was==='pow')R=fill('sub');renderAll()}});
return{
/* for tests */
lib:{empty,full,ident,union,inter,diff,compl,inverse,compose,tclose,analyze,classes,order,pairs,size,same,subset},
render(){
  document.getElementById('conds').innerHTML=`<div class="qb rl"><div class="colhead"><h2>הקבוצה והיחס</h2><span class="lab">יחס מעל קבוצה סופית</span></div><div id="rlobjs" class="qlist"></div></div>`;
  renderAll()}};
})();
