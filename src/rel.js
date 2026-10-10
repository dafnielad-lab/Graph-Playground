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
  /* antisymmetric as in the course: (a, b) in the relation rules out (b, a), so no pair (a, a) either. The wide sense allows a = b */
  { let w=null;for(let a=0;a<n&&!w;a++)for(let b=a;b<n&&!w;b++)if(has(M,a,b)&&has(M,b,a))w=[a,b];set('anti',!w,w?(w[0]===w[1]?[w]:[w,[w[1],w[0]]]):[])}
  { let w=null;for(let a=0;a<n&&!w;a++)for(let b=a+1;b<n&&!w;b++)if(has(M,a,b)&&has(M,b,a))w=[a,b];set('wanti',!w,w?[w,[w[1],w[0]]]:[])}
  { let w=null;for(let a=0;a<n&&!w;a++)for(let b=0;b<n&&!w;b++)if(has(M,a,b))for(let c=0;c<n&&!w;c++)if(has(M,b,c)&&!has(M,a,c))w=[a,b,c];set('trans',!w,w?[[w[0],w[1]],[w[1],w[2]]]:[],w?[[w[0],w[2]]]:[])}
  { let w=null;for(let a=0;a<n&&!w;a++)for(let b=a+1;b<n&&!w;b++)if(!has(M,a,b)&&!has(M,b,a))w=[a,b];set('comp',!w,[],w?[w,[w[1],w[0]]]:[])}
  P.equiv=P.refl.ok&&P.sym.ok&&P.trans.ok;P.weak=P.refl.ok&&P.wanti.ok&&P.trans.ok;P.strict=P.irr.ok&&P.trans.ok;P.total=(P.weak||P.strict)&&P.comp.ok;return P}
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
let KIND='div',PARAM={range:5,div:12,pow:3,custom:'a, b, c, d'},A=[],RELS=[],CUR=0,HL=null,SEL=null;
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
/* the relations: a free one holds its own pairs (M); a derived one names an operation and the relations it is built from */
const NAMES='RSTUVWQPNMLK',SUP='⁰¹²³⁴⁵⁶⁷⁸⁹',pwr=(P,k)=>{let o=ident(P.length);for(let i=0;i<k;i++)o=compose(o,P);return o};
const OPS={tc:{l:'סגור טרנזיטיבי',add:true,sym:a=>`${a}⁺`,def:a=>`${a} ∪ ${a}² ∪ ${a}³ ∪ …`,f:P=>tclose(P)},
  rc:{l:'סגור רפלקסיבי',add:true,sym:a=>`${a} ∪ I`,def:a=>`${a} ∪ I,   I = { (x, x) | x ∈ A }`,f:P=>union(P,ident(P.length))},
  sc:{l:'סגור סימטרי',add:true,sym:a=>`${a} ∪ ${a}⁻¹`,def:a=>`${a} ∪ ${a}⁻¹`,f:P=>union(P,inverse(P))},
  ec:{l:'סגור שקילות',add:true,sym:a=>`(${a} ∪ ${a}⁻¹ ∪ I)⁺`,def:a=>`(${a} ∪ ${a}⁻¹ ∪ I)⁺,   the smallest equivalence relation containing ${a}`,f:P=>tclose(union(union(P,inverse(P)),ident(P.length)))},
  pow:{l:'חזקה',k:true,sym:(a,b,k)=>a+String(k).split('').map(d=>SUP[d]).join(''),def:(a,b,k)=>k===0?'I,   the identity relation on A':k===1?a:`${a.repeat(Math.min(k,6))}${k>6?'…':''},   ${a} composed with itself ${k} times`,f:(P,Q,k)=>pwr(P,k)},
  inv:{l:'היחס ההפוך',sym:a=>`${a}⁻¹`,def:a=>`{ (y, x) | (x, y) ∈ ${a} }`,f:P=>inverse(P)},
  cmp:{l:'המשלים',sym:a=>`(A × A) ∖ ${a}`,def:a=>`(A × A) ∖ ${a}`,f:P=>compl(P)},
  comp:{l:'הרכבה של שני יחסים',two:true,sym:(a,b)=>a+b,def:(a,b)=>`{ (x, z) | ∃y: (x, y) ∈ ${a}, (y, z) ∈ ${b} }`,f:(P,Q)=>compose(P,Q)},
  uni:{l:'איחוד',two:true,sym:(a,b)=>`${a} ∪ ${b}`,def:(a,b)=>`${a} ∪ ${b}`,f:(P,Q)=>union(P,Q)},
  int:{l:'חיתוך',two:true,sym:(a,b)=>`${a} ∩ ${b}`,def:(a,b)=>`${a} ∩ ${b}`,f:(P,Q)=>inter(P,Q)},
  dif:{l:'הפרש',two:true,sym:(a,b)=>`${a} ∖ ${b}`,def:(a,b)=>`${a} ∖ ${b}`,f:(P,Q)=>diff(P,Q)}};
const kOf=r=>Math.max(0,Math.min(9,Math.floor(Number(r.k))||0));
/* every relation as a matrix, in order: a derived relation may only use relations listed before it, so there are no loops */
function evalAll(){const n=A.length,V=[];RELS.forEach((r,i)=>{if(!r.op){V.push(r.M);return}const ix=nm=>{const j=RELS.findIndex(x=>x.name===nm);return j>=0&&j<i?V[j]:empty(n)};V.push(OPS[r.op].f(ix(r.a),ix(r.b),kOf(r)))});return V}
const symOf=r=>r.op?OPS[r.op].sym(r.a,r.b,kOf(r)):r.name;
function resetSet(keep){const old=A.length;A=buildSet();const n=A.length,m=(1<<n)-1;
  for(const r of RELS)if(!r.op)r.M=keep?Array.from({length:n},(_,i)=>i<old?r.M[i]&m:0):empty(n);HL=null;SEL=null}
A=buildSet();RELS=[{name:'R',M:fill('div')}];
const editable=()=>!RELS[CUR].op;

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
    return `<td class="${c}">${name!==null&&name!==undefined?`<button data-rc="${name}|${i}|${j}" aria-label="(${esc(e.l)}, ${esc(f.l)})" aria-pressed="${!!on}">${on?'●':''}</button>`:on?'●':''}</td>`}).join('')}</tr>`).join('')}</tbody></table></div>`}
/* the Hasse diagram: one level for every step of the longest chain below an element, lines for covering pairs only */
function hasseSvg(O){const n=A.length,H=Math.max(...O.lev)+1,by=Array.from({length:H},()=>[]);for(let a=0;a<n;a++)by[O.lev[a]].push(a);
  const W=440,gap=H>1?Math.min(86,340/(H-1)):0,hgt=Math.max(120,(H-1)*gap+80),x=new Array(n).fill(0);
  for(let l=0;l<H;l++){if(l>0){const bc=a=>{const lo=O.cover.filter(c=>c[1]===a).map(c=>x[c[0]]);return lo.length?lo.reduce((t,v)=>t+v,0)/lo.length:W/2};by[l].sort((p,q)=>bc(p)-bc(q))}
    by[l].forEach((a,i)=>{x[a]=W*(i+1)/(by[l].length+1)})}
  const y=a=>hgt-40-O.lev[a]*gap;
  return `<svg class="rlsvg hs" viewBox="0 0 ${W} ${hgt}" role="img" aria-label="דיאגרמת הסה">${O.cover.map(([a,b])=>`<line class="hl" x1="${x[a].toFixed(1)}" y1="${y(a).toFixed(1)}" x2="${x[b].toFixed(1)}" y2="${y(b).toFixed(1)}"/>`).join('')}${A.map((e,a)=>`<g class="nd"><circle cx="${x[a].toFixed(1)}" cy="${y(a).toFixed(1)}" r="${rad(e)}"/><text x="${x[a].toFixed(1)}" y="${y(a).toFixed(1)}" style="font-size:${e.l.length>4?10:e.l.length>2?12:15}px">${esc(e.l)}</text></g>`).join('')}</svg>`}

/* ---------- text ---------- */
const PROPS=[['refl','רפלקסיבי','∀a ∈ A:  (a, a) ∈ X','I ⊆ X'],['irr','אנטי-רפלקסיבי','∀a ∈ A:  (a, a) ∉ X','X ∩ I = ∅'],['sym','סימטרי','(a, b) ∈ X  ⇒  (b, a) ∈ X','X⁻¹ = X'],
  ['anti','אנטי-סימטרי','(a, b) ∈ X  ⇒  (b, a) ∉ X','X ∩ X⁻¹ = ∅'],['wanti','אנטי-סימטרי במובן הרחב','(a, b) ∈ X,  (b, a) ∈ X  ⇒  a = b','X ∩ X⁻¹ ⊆ I'],['trans','טרנזיטיבי','(a, b) ∈ X,  (b, c) ∈ X  ⇒  (a, c) ∈ X','X² ⊆ X'],['comp','כל שני איברים שונים ניתנים להשוואה','a ≠ b  ⇒  (a, b) ∈ X  or  (b, a) ∈ X','X ∪ X⁻¹ ∪ I = A × A']];
const witness=(k,p,s)=>p.ok?'':[...p.inn.map(q=>`${pr(q)} ∈ ${s}`),...p.out.map(q=>`${pr(q)} ∉ ${s}`)].join(',   ');
const setOf=a=>`{${a.map(i=>esc(A[i].l)).join(', ')}}`;
function renderSide(){const ok=Object.entries(PRE).filter(([k,v])=>v[1]()),V=evalAll();
  const opt=(list,c)=>list.map(([v,l])=>`<option value="${v}" ${v===c?'selected':''}>${l}</option>`).join('');
  const box=(r,i)=>{const head=`<button class="name v rlnm" data-rsel="${i}" aria-pressed="${i===CUR}" aria-label="הצג את ${r.name}">${r.name}</button>`,del=RELS.length>1?`<button class="x" data-rdel="${i}" aria-label="הסר את ${r.name}">×</button>`:'';
    if(!r.op)return `<div class="qbox${i===CUR?' rlcur':''}"><div class="qrow">${head}<select data-rp="${i}" aria-label="יחס מוכן"><option value="">יחס מוכן…</option>${ok.map(([k,v])=>`<option value="${k}">${v[0]}</option>`).join('')}</select>${del}</div>${matrixHtml(r.M,null,null,i,true)}</div>`;
    const o=OPS[r.op],before=RELS.slice(0,i).map(x=>[x.name,x.name]);
    return `<div class="qbox${i===CUR?' rlcur':''}"><div class="qrow">${head}<select data-ro="${i}" data-f="op" aria-label="פעולה">${opt(Object.entries(OPS).filter(([k,x])=>!x.two||i>=1).map(([k,x])=>[k,x.l]),r.op)}</select>${del}</div>
      <div class="qrow"><label class="cell">${o.two?'ראשון':'של'}<select data-ro="${i}" data-f="a">${opt(before,r.a)}</select></label>${o.two?`<label class="cell">שני<select data-ro="${i}" data-f="b">${opt(before,r.b)}</select></label>`:''}${o.k?`<label class="cell">מעריך<input type="number" min="0" max="9" class="rn" dir="ltr" data-ro="${i}" data-f="k" value="${kOf(r)}"></label>`:''}</div>
      <div class="gfset fx">${r.name} = ${esc(symOf(r))},   |${r.name}| = ${size(V[i])}</div></div>`};
  const par=KIND==='custom'?`<input type="text" dir="ltr" class="rlt" data-rk="custom" value="${esc(PARAM.custom)}" aria-label="האיברים, מופרדים בפסיקים">`:`<label class="cell">${KIND==='range'?'עד':KIND==='div'?'המחלקים של':'קבוצת החזקה של {1,…,k}, k ='}<input type="number" min="1" max="${KIND==='range'?MAXN:KIND==='pow'?3:100000}" class="rn" dir="ltr" data-rk="${KIND}" value="${esc(PARAM[KIND])}"></label>`;
  const room=RELS.length<NAMES.length;
  document.getElementById('rlobjs').innerHTML=`<div class="qbox"><div class="qrow"><span class="name">A</span><select data-rk="kind" aria-label="סוג הקבוצה">${opt([['range','המספרים מאחת עד'],['div','המחלקים של מספר'],['pow','קבוצת חזקה'],['custom','איברים שאני כותב']],KIND)}</select></div>
      <div class="qrow">${par}</div><div class="gfset fx">A = ${setOf(A.map((_,i)=>i))},   |A| = ${A.length}</div></div>
    ${RELS.map(box).join('')}
    <div class="qbox"><div class="lab">הוסף יחס</div><div class="addrow"><button class="addb" data-radd="free" ${room?'':'disabled'}>+ יחס חופשי</button><button class="addb" data-radd="op" ${room?'':'disabled'}>+ יחס מפעולה</button></div>
      <p class="hint">יחס חופשי: לחיצה על תא במטריצה מוסיפה או מסירה זוג, והשורה היא האיבר הראשון בזוג. יחס מפעולה נבנה מיחסים שמעליו ומתעדכן איתם: סגור, חזקה, הפוך, משלים, הרכבה, איחוד, חיתוך והפרש. לחיצה על שם היחס מציגה אותו.</p></div>`}
function renderMain(){if(CUR>=RELS.length)CUR=RELS.length-1;const V=evalAll(),r=RELS[CUR],M=V[CUR],P=analyze(M),s=r.name,o=r.op?OPS[r.op]:null,w=HL&&P[HL]&&!P[HL].ok?P[HL]:null,si=o?RELS.findIndex(x=>x.name===r.a):-1,added=o&&o.add&&si>=0?diff(M,V[si]):null,nAdd=added?size(added):0,ps=pairs(M);
  const opts=RELS.map((x,k)=>`<option value="${k}" ${k===CUR?'selected':''}>${x.name}${x.op?'  =  '+esc(symOf(x))+'   —   '+OPS[x.op].l:''}</option>`).join('');
  let extra='';
  if(P.equiv){const C=classes(M);extra+=`<section class="gfb"><h3>יחס שקילות: מחלקות השקילות</h3><p class="hint">המחלקות מחלקות את A לקבוצות זרות. מספר המחלקות: ${C.length}.</p><div class="rlcl">${C.map(c=>`<span class="rlc">${fx(`[${esc(A[c[0]].l)}] = ${setOf(c)}`)}</span>`).join('')}</div><div class="rlset">${fx(`A / ${s} = { ${C.map(setOf).join(', ')} }`)}</div></section>`}
  if(P.weak||P.strict){const O=order(M),li=(t,x)=>`<div class="rlf"><span>${t}</span>${fx(x)}</div>`;
    extra+=`<section class="gfb"><h3>${P.total?'סדר מלא':'סדר חלקי'}${P.strict?' (אנטי-רפלקסיבי)':' (רפלקסיבי)'}: דיאגרמת הסה</h3><p class="hint">קו עולה מאיבר לאיבר שמעליו רק כשאין איבר ביניהם. שאר הזוגות נובעים מטרנזיטיביות${P.weak?' ומרפלקסיביות':''}.</p>
      <div class="rlrow"><div class="rlg">${hasseSvg(O)}</div><div class="rlfacts">${li('איברים מינימליים',setOf(O.min))}${li('איברים מקסימליים',setOf(O.max))}${li('איבר קטן ביותר',O.least>=0?esc(A[O.least].l):'אין')}${li('איבר גדול ביותר',O.greatest>=0?esc(A[O.greatest].l):'אין')}
        ${li('שרשרת ארוכה ביותר',O.chain.map(i=>esc(A[i].l)).join(P.strict?'  ,  ':'  ,  ')+`   (${O.chain.length})`)}${li('אנטי-שרשרת גדולה ביותר',setOf(O.anti)+`   (${O.anti.length})`)}
        ${li('זוגות כיסוי, הקווים בדיאגרמה',String(O.cover.length))}${li('זוגות שאינם ניתנים להשוואה',O.inc.length?(O.inc.length<=8?O.inc.map(([a,b])=>`{${esc(A[a].l)}, ${esc(A[b].l)}}`).join(', '):String(O.inc.length)):'אין')}</div></div></section>`}
  document.getElementById('main').innerHTML=`<div class="gfwrap rl">
    <section class="gfb rlhead"><div class="rlbar"><label class="cell">מה מוצג<select data-rv="1">${opts}</select></label>${editable()?'':`<button class="btn sm" data-rfz="1">הפוך ליחס חופשי לעריכה</button>`}</div>
      ${o?`<div class="rldef">${fx(`${s} = ${esc(symOf(r))}${o.def(r.a,r.b,kOf(r))===symOf(r)?'':' = '+esc(o.def(r.a,r.b,kOf(r)))}`)}</div>`:''}${o&&o.add?`<p class="hint">${nAdd?`זוגות שנוספו ל־${r.a} מסומנים בצבע. מספרם: ${nAdd}.`:`לא נוסף אף זוג: ${r.a} כבר מקיים את התכונה.`}</p>`:''}</section>
    <div class="rlrow"><section class="gfb rlg"><h3>הגרף המכוון</h3>${graphSvg(M,added,w)}<p class="hint">${editable()?(SEL===null?'לחיצה על איבר ואחריה על איבר שני מוסיפה או מסירה חץ. לחיצה שנייה על אותו איבר: הזוג של האיבר עם עצמו.':`נבחר ${fx(esc(A[SEL].l))}. לחץ על האיבר שאליו החץ.`):'היחס הזה מחושב מיחסים אחרים ומתעדכן איתם, ולכן אינו נערך ישירות.'}</p></section>
      <section class="gfb rlm"><h3>המטריצה</h3>${matrixHtml(M,added,w,editable()?CUR:null,false)}<p class="hint">נקודה בשורה של a ובעמודה של b: הזוג ${fx('(a, b)')} ביחס.</p></section></div>
    <section class="gfb"><h3>היחס כקבוצת זוגות</h3><div class="rlset">${fx(`${s} = ${ps.length?`{ ${ps.map(pr).join(', ')} }`:'∅'}`)}</div><div class="rlset sm">${fx(`|${s}| = ${ps.length},   |A × A| = ${A.length*A.length}`)}</div></section>
    ${extra}</div>`;
  /* the card: the properties, each with its definition and a counterexample when it fails */
  const X=t=>t.replace(/X/g,s);
  const kind=P.equiv&&P.weak?'גם יחס שקילות וגם סדר חלקי: זה יחס השוויון':P.equiv?'יחס שקילות':P.total?(P.strict?'סדר מלא (אנטי-רפלקסיבי)':'סדר מלא (רפלקסיבי)'):P.weak?'סדר חלקי (רפלקסיבי)':P.strict?'סדר חלקי (אנטי-רפלקסיבי)':'לא יחס שקילות ולא יחס סדר';
  const miss=(need,name)=>{const m=need.filter(k=>!P[k].ok).map(k=>PROPS.find(p=>p[0]===k)[1]);return m.length?`<div class="rlmiss"><b>${name}:</b> חסר ${m.join(', ')}</div>`:''};
  document.getElementById('card').innerHTML=`<div class="gfcard rl"><div class="cardhead"><h2>תכונות היחס</h2></div><div class="rlkind">${fx(esc(s))} <span>${kind}</span></div>
    ${PROPS.map(([k,name,df,alg])=>{const p=P[k],on=HL===k&&!p.ok;return `<div class="rlp ${p.ok?'ok':'no'}${on?' cur':''}"><div class="rlph"><b>${p.ok?'✓':'✗'}</b><span>${name}</span>${p.ok?'':`<button class="qexb" data-rh="${k}" aria-pressed="${on}">${on?'הסתר':'הראה'}</button>`}</div>
      <div class="rlpd">${fx(X(df))}</div><div class="rlpd alg">${fx(X(alg))}</div>${p.ok?'':`<div class="rlpw"><span>דוגמה נגדית</span>${fx(witness(k,p,esc(s)))}</div>`}</div>`}).join('')}
    ${!P.equiv?miss(['refl','sym','trans'],'יחס שקילות'):''}${!P.weak&&!P.strict?miss(['refl','wanti','trans'],'סדר חלקי רפלקסיבי')+miss(['irr','trans'],'סדר חלקי אנטי-רפלקסיבי'):''}
    <p class="hint">${fx('I')} הוא יחס הזהות על A. בדוגמה נגדית, ״הראה״ מסמן את הזוגות בגרף ובמטריצה: קו מלא לזוג שביחס, קו מקווקו לזוג שחסר.</p></div>`}
function renderAll(){renderSide();renderMain()}
const toggle=(M,i,j)=>{M[i]^=1<<j};
/* removing or freezing: a relation built from the removed one keeps its current pairs as a free relation */
const freeze=(i,V)=>{RELS[i]={name:RELS[i].name,M:V[i].slice()}};
document.addEventListener('click',ev=>{const t=ev.target;if(!t.closest||!t.closest('.rl'))return;
  const md=t.closest('[data-rmode]');if(md){MODE=md.dataset.rmode;REL.render();return}if(MODE==='abs'){absClick(t);return}
  const c=t.closest('[data-rc]'),nd=t.closest('[data-rn]'),h=t.closest('[data-rh]'),sel=t.closest('[data-rsel]'),del=t.closest('[data-rdel]'),add=t.closest('[data-radd]'),fz=t.closest('[data-rfz]');
  if(c){const [k,i,j]=c.dataset.rc.split('|').map(Number);if(RELS[k]&&!RELS[k].op){toggle(RELS[k].M,i,j);SEL=null;renderAll()}}
  else if(nd&&editable()){const i=Number(nd.dataset.rn);if(SEL===null){SEL=i;renderMain()}else{toggle(RELS[CUR].M,SEL,i);SEL=null;renderAll()}}
  else if(h){HL=HL===h.dataset.rh?null:h.dataset.rh;renderMain()}
  else if(sel){CUR=Number(sel.dataset.rsel);HL=null;SEL=null;renderAll()}
  else if(fz){freeze(CUR,evalAll());renderAll()}
  else if(del&&RELS.length>1){const i=Number(del.dataset.rdel),V=evalAll(),nm=RELS[i].name;RELS.forEach((r,k)=>{if(r.op&&(r.a===nm||(OPS[r.op].two&&r.b===nm)))freeze(k,V)});RELS.splice(i,1);if(CUR>=i&&CUR>0)CUR--;HL=null;SEL=null;renderAll()}
  else if(add){const name=[...NAMES].find(x=>!RELS.some(r=>r.name===x));if(!name)return;const src=RELS[CUR].name;
    RELS.push(add.dataset.radd==='op'?{name,op:'tc',a:src,b:src,k:2}:{name,M:empty(A.length)});CUR=RELS.length-1;HL=null;SEL=null;renderAll()}});
document.addEventListener('keydown',ev=>{const nd=ev.target.closest&&ev.target.closest('.rl [data-rn]');if(nd&&(ev.key==='Enter'||ev.key===' ')){ev.preventDefault();nd.dispatchEvent(new MouseEvent('click',{bubbles:true}))}});
document.addEventListener('change',ev=>{const t=ev.target;if(!t.closest||!t.closest('.rl'))return;
  if(MODE==='abs'){if(t.dataset.ro!==undefined){const r=ABS[Number(t.dataset.ro)];if(r&&r.op){r[t.dataset.f]=t.value;renderAbs()}}return}
  if(t.dataset.rv){CUR=Number(t.value);HL=null;SEL=null;renderAll()}
  else if(t.dataset.rp!==undefined){const r=RELS[Number(t.dataset.rp)];if(t.value&&r&&!r.op){r.M=fill(t.value);HL=null;renderAll()}}
  else if(t.dataset.ro!==undefined){const r=RELS[Number(t.dataset.ro)];if(r&&r.op){r[t.dataset.f]=t.value;HL=null;renderAll()}}
  else if(t.dataset.rk==='kind'){KIND=t.value;resetSet(false);const f=RELS.find(r=>!r.op);if(f)f.M=fill(KIND==='div'?'div':KIND==='pow'?'sub':KIND==='range'?'le':'empty');renderAll()}
  else if(t.dataset.rk){PARAM[t.dataset.rk]=t.value;const was=KIND;resetSet(was==='range');const f=RELS.find(r=>!r.op);if(f&&was==='div')f.M=fill('div');else if(f&&was==='pow')f.M=fill('sub');renderAll()}});
/* ---------- the abstract layer: relations known only by their properties ----------
   Two independent tools answer "does this property follow":
   1. rules: theorems as clauses, chained by unit propagation; whatever they reach comes with a derivation.
   2. models: every choice of relations over small sets that satisfies the data; one model where a property fails
      settles that it does not follow. */
let MODE='conc',ABS=[{name:'R',giv:{sym:'y',trans:'y'}},{name:'S',op:'rc',a:'R',b:'R',k:2,giv:{}},{name:'T',op:'inv',a:'S',b:'S',k:2,giv:{}}],PICK=null;
const PK=['refl','irr','sym','anti','wanti','trans','comp'],PN={refl:'רפלקסיבי',irr:'אנטי-רפלקסיבי',sym:'סימטרי',anti:'אנטי-סימטרי',wanti:'אנטי-סימטרי במובן הרחב',trans:'טרנזיטיבי',comp:'השוואה מלאה'};
const PF={refl:'I ⊆ X',irr:'X ∩ I = ∅',sym:'X⁻¹ = X',anti:'X ∩ X⁻¹ = ∅',wanti:'X ∩ X⁻¹ ⊆ I',trans:'X² ⊆ X',comp:'X ∪ X⁻¹ ∪ I = A × A'};
/* the seven properties of a matrix at once, without witnesses */
function flags(M){const n=M.length;let loop=false,gap=false,both=false,one=false,inc=false,tr=true;
  for(let i=0;i<n;i++){const r=M[i];if(r>>i&1)loop=true;else gap=true;
    for(let j=0;j<n;j++){if(r>>j&1){if(tr&&(M[j]&~r))tr=false;if(j!==i){if(M[j]>>i&1)both=true;else one=true}}else if(j>i&&!(M[j]>>i&1))inc=true}}
  return{refl:!gap,irr:!loop,sym:!one,anti:!both&&!loop,wanti:!both,trans:tr,comp:!inc}}
const evalList=(list,base,n)=>{const V=[];list.forEach((r,i)=>{if(!r.op){V.push(base[i]);return}const ix=nm=>{const j=list.findIndex(x=>x.name===nm);return j>=0&&j<i?V[j]:empty(n)};V.push(OPS[r.op].f(ix(r.a),ix(r.b),kOf(r)))});return V};
/* the theorems, as clauses over the statements "X has property p". A clause is a list of literals of which at least one holds */
function clauses(list){const C=[],lit=(x,p,v)=>({x,p,v:v!==false}),neg=l=>({x:l.x,p:l.p,v:!l.v});
  const imp=(prem,concl,why)=>C.push({lits:[...prem.map(neg),concl],why}),iff=(a,b,why)=>{imp([a],b,why);imp([b],a,why)},fact=(l,why)=>C.push({lits:[l],why});
  const DOWN=['irr','anti','wanti'],UP=['refl','comp'];
  /* P is contained in X: what X has passes down to P for the properties that survive removing pairs, and up for those that survive adding */
  const inside=(P,X,pre,why)=>{for(const h of DOWN)imp([...pre,lit(X,h)],lit(P,h),`${why}, ותכונה זו נשמרת כשמסירים זוגות`);for(const h of UP)imp([...pre,lit(P,h)],lit(X,h),`${why}, ותכונה זו נשמרת כשמוסיפים זוגות`)};
  list.forEach((r,i)=>{const X=r.name;
    imp([lit(X,'anti')],lit(X,'irr'),'זוג של איבר עם עצמו שווה להפוך שלו');imp([lit(X,'anti')],lit(X,'wanti'),'אם אין שני זוגות הפוכים, התנאי מתקיים באופן ריק');
    imp([lit(X,'irr'),lit(X,'wanti')],lit(X,'anti'),'זוגות הפוכים אפשריים רק על האלכסון, והאלכסון ריק');
    imp([lit(X,'irr'),lit(X,'trans')],lit(X,'anti'),'שני זוגות הפוכים היו נותנים, בטרנזיטיביות, זוג של איבר עם עצמו');
    imp([lit(X,'refl')],lit(X,'irr',false),'A אינה ריקה, ולכן יש זוג של איבר עם עצמו');
    imp([lit(X,'sym'),lit(X,'wanti')],lit(X,'trans'),'כל זוג הוא של איבר עם עצמו, כלומר היחס מוכל בזהות');
    if(!r.op)return;const o=r.op,P=r.a,Q=r.b,k=kOf(r),ok=nm=>{const j=list.findIndex(x=>x.name===nm);return j>=0&&j<i};if(!ok(P)||(OPS[o].two&&!ok(Q)))return;
    const S=`${X} = ${OPS[o].sym(P,Q,k)}`;
    if(o==='inv'||(o==='pow'&&k===1))for(const p of PK)iff(lit(P,p),lit(X,p),o==='inv'?`${S}: היפוך כל הזוגות שומר על התכונה`:`${S}: אותו יחס`);
    if(o==='cmp'){iff(lit(P,'irr'),lit(X,'refl'),`${S}: האלכסון במשלים מלא בדיוק כשהוא ריק במקור`);iff(lit(P,'refl'),lit(X,'irr'),`${S}: האלכסון במשלים ריק בדיוק כשהוא מלא במקור`);iff(lit(P,'sym'),lit(X,'sym'),`${S}: זוג והפוכו נמצאים יחד או חסרים יחד`);
      iff(lit(P,'wanti'),lit(X,'comp'),`${S}: שני זוגות הפוכים חסרים במשלים בדיוק כששניהם במקור`);iff(lit(P,'comp'),lit(X,'wanti'),`${S}: שני זוגות הפוכים במשלים בדיוק כששניהם חסרים במקור`);
      imp([lit(X,'anti')],lit(P,'refl'),`${S}: האלכסון של המשלים ריק`);imp([lit(X,'anti')],lit(P,'comp'),`${S}: אין במשלים שני זוגות הפוכים`);imp([lit(P,'refl'),lit(P,'comp')],lit(X,'anti'),`${S}: במשלים אין אלכסון ואין שני זוגות הפוכים`)}
    if(o==='rc'){fact(lit(X,'refl'),`${S}: הזהות נוספה`);iff(lit(P,'sym'),lit(X,'sym'),`${S}: הזוגות שנוספו סימטריים`);iff(lit(P,'wanti'),lit(X,'wanti'),`${S}: מחוץ לאלכסון היחסים זהים`);iff(lit(P,'comp'),lit(X,'comp'),`${S}: מחוץ לאלכסון היחסים זהים`);
      imp([lit(P,'trans')],lit(X,'trans'),`${S}: הרכבה עם זוג מהזהות מחזירה את אותו זוג`)}
    if(o==='sc'){fact(lit(X,'sym'),`${S}: לכל זוג נוסף ההפוך שלו`);iff(lit(P,'refl'),lit(X,'refl'),`${S}: האלכסון לא השתנה`);iff(lit(P,'irr'),lit(X,'irr'),`${S}: האלכסון לא השתנה`);iff(lit(P,'comp'),lit(X,'comp'),`${S}: זוג או הפוכו במקור, בדיוק כשאחד מהם בסגור`);inside(P,X,[],`${P} ⊆ ${X}`)}
    if(o==='tc'){fact(lit(X,'trans'),`${S}: סגור טרנזיטיבי`);imp([lit(P,'sym')],lit(X,'sym'),`${S}: מסלול הפוך עובר בזוגות ההפוכים`);inside(P,X,[],`${P} ⊆ ${X}`);
      for(const h of DOWN)imp([lit(P,'trans'),lit(P,h)],lit(X,h),`${S}: יחס טרנזיטיבי שווה לסגור שלו`)}
    if(o==='ec'){for(const p of ['refl','sym','trans'])fact(lit(X,p),`${S}: סגור שקילות`);inside(P,X,[],`${P} ⊆ ${X}`)}
    if(o==='pow'&&k===0){for(const p of ['refl','sym','wanti','trans'])fact(lit(X,p),`${S}: יחס הזהות`)}
    if(o==='pow'&&k>=2){imp([lit(P,'refl')],lit(X,'refl'),`${S}: זוג של איבר עם עצמו, מורכב עם עצמו`);imp([lit(P,'sym')],lit(X,'sym'),`${S}: ההפוך של חזקה הוא החזקה של ההפוך`);imp([lit(P,'trans')],lit(X,'trans'),`${S}: מ־${P}² ⊆ ${P} נובע שכל חזקה מוכלת בקודמת`);
      inside(X,P,[lit(P,'trans')],`${P} טרנזיטיבי, ולכן ${X} ⊆ ${P}`);inside(P,X,[lit(P,'refl')],`${P} רפלקסיבי, ולכן ${P} ⊆ ${X}`)}
    if(o==='comp'){imp([lit(P,'refl'),lit(Q,'refl')],lit(X,'refl'),`${S}: שני זוגות של איבר עם עצמו`);inside(Q,X,[lit(P,'refl')],`${P} רפלקסיבי, ולכן ${Q} ⊆ ${X}`);inside(P,X,[lit(Q,'refl')],`${Q} רפלקסיבי, ולכן ${P} ⊆ ${X}`)}
    if(o==='uni'){inside(P,X,[],`${P} ⊆ ${X}`);inside(Q,X,[],`${Q} ⊆ ${X}`);imp([lit(P,'irr'),lit(Q,'irr')],lit(X,'irr'),`${S}: האלכסון ריק בשניהם`);imp([lit(P,'sym'),lit(Q,'sym')],lit(X,'sym'),`${S}: ההפוך של כל זוג נמצא באותו יחס`)}
    if(o==='int'){inside(X,P,[],`${X} ⊆ ${P}`);inside(X,Q,[],`${X} ⊆ ${Q}`);imp([lit(P,'refl'),lit(Q,'refl')],lit(X,'refl'),`${S}: האלכסון מלא בשניהם`);imp([lit(P,'sym'),lit(Q,'sym')],lit(X,'sym'),`${S}: ההפוך של כל זוג נמצא בשניהם`);imp([lit(P,'trans'),lit(Q,'trans')],lit(X,'trans'),`${S}: הזוג המורכב נמצא בשניהם`)}
    if(o==='dif'){inside(X,P,[],`${X} ⊆ ${P}`);imp([lit(Q,'refl')],lit(X,'irr'),`${S}: כל האלכסון הוסר`);imp([lit(X,'refl')],lit(Q,'irr'),`${S}: שום זוג מהאלכסון לא הוסר`);imp([lit(P,'sym'),lit(Q,'sym')],lit(X,'sym'),`${S}: זוג והפוכו נשארים יחד או מוסרים יחד`)}});
  return C}
/* unit propagation: when all literals of a clause but one are known to fail, the last one holds */
function propagate(list){const C=clauses(list),K=new Map(),key=l=>l.x+'|'+l.p;let conflict=null;
  for(const r of list)for(const p of PK)if(r.giv&&r.giv[p])K.set(r.name+'|'+p,{v:r.giv[p]==='y',given:true,from:[]});
  let ch=true;while(ch&&!conflict){ch=false;for(const c of C){let open=null,n=0,sat=false;for(const l of c.lits){const k=K.get(key(l));if(!k){open=l;n++}else if(k.v===l.v){sat=true;break}}
    if(sat)continue;if(n===0){conflict=c;break}if(n===1){K.set(key(open),{v:open.v,why:c.why,from:c.lits.filter(l=>l!==open).map(key)});ch=true}}}
  return{K,conflict,C}}
/* models: all relations over sets of one to four elements that satisfy the data, as far as the budget allows */
let CACHE={key:'',val:null};
function models(list){const LIMIT=300000,B=list.map((r,i)=>r.op?-1:i).filter(i=>i>=0),seen={},exh={};let found=0,tried=0;
  for(const r of list){seen[r.name]={};for(const p of PK)seen[r.name][p]={T:null,F:null}}
  const fits=(r,f)=>{for(const p of PK){const g=r.giv&&r.giv[p];if(g&&(g==='y')!==f[p])return false}return true};
  let seed=987654321;const rnd=()=>(seed=(seed*1103515245+12345)&0x7fffffff)/0x7fffffff;
  for(let n=1;n<=4;n++){const bits=n*n,mask=(1<<n)-1,cand=[];if(bits*B.length>26&&n>2){exh[n]=false}
    /* each unknown relation is first cut down to the matrices that fit its own data */
    let prod=1,ok=true;for(const b of B){const L=[];if(n<=4){for(let code=0;code<1<<bits;code++){const M=[];for(let i=0;i<n;i++)M.push(code>>i*n&mask);if(fits(list[b],flags(M)))L.push(M)}}cand.push(L);prod*=L.length;if(!L.length)ok=false}
    if(!ok){exh[n]=true;continue}
    const full=prod<=LIMIT,runs=full?prod:LIMIT>>2;exh[n]=full;
    for(let t=0;t<runs;t++){const base=[];let q=t;B.forEach((b,j)=>{const L=cand[j];base[b]=full?L[q%L.length]:L[Math.floor(rnd()*L.length)];q=Math.floor(q/L.length)});
      const V=evalList(list,base,n),F=V.map(flags);tried++;let good=true;for(let i=0;i<list.length&&good;i++)if(list[i].op&&!fits(list[i],F[i]))good=false;if(!good)continue;found++;
      for(let i=0;i<list.length;i++){const s=seen[list[i].name];for(const p of PK){const slot=F[i][p]?'T':'F';if(!s[p][slot])s[p][slot]={n,base:B.map(b=>base[b].slice())}}}}}
  return{seen,exh,found,tried,B}}
const FREE_OPS=new Set(['inv','cmp','rc','sc','uni','int','dif']);
/* everything together: for every relation and property, what is known and why */
function solveAbs(list){const key=JSON.stringify(list);if(CACHE.key===key)return CACHE.val;const pr=propagate(list),mo=models(list);
  /* when the data are only "has the property" and no operation hides an existence claim, three elements decide the matter:
     a counterexample cut down to the elements of its witness is still a counterexample */
  const exact=list.every(r=>(!r.op||FREE_OPS.has(r.op))&&PK.every(p=>!r.giv||r.giv[p]!=='n'))&&mo.exh[1]&&mo.exh[2]&&mo.exh[3];
  const st={};for(const r of list){st[r.name]={};for(const p of PK){const k=pr.K.get(r.name+'|'+p),s=mo.seen[r.name][p];
    st[r.name][p]=k?{kind:k.given?'given':'proved',v:k.v,clash:!!(k.v?s.F&&!s.T&&false:false)}:s.T&&s.F?{kind:'open'}:!mo.found?{kind:'none'}:exact?{kind:'exact',v:!!s.T}:{kind:'seen',v:!!s.T};
    /* a rule may never say what a model contradicts */
    if(k&&!k.given&&mo.found&&((k.v&&!s.T)||(!k.v&&!s.F)))st[r.name][p].clash=true}}
  const val={pr,mo,st,exact};CACHE={key,val};return val}
const holds=x=>x&&(x.kind==='given'||x.kind==='proved'||x.kind==='exact')&&x.v===true;
/* a derivation: every statement after the statements it rests on */
function proofHtml(pr,k0,list){const order=[],seen=new Set(),go=k=>{if(seen.has(k))return;seen.add(k);const e=pr.K.get(k);if(!e)return;for(const f of e.from)go(f);order.push(k)};go(k0);
  const txt=(k,v)=>{const [x,p]=k.split('|'),f=PF[p].replace(/X/g,x);return v?f:`not ( ${f} )`},nm=(k,v)=>{const [x,p]=k.split('|');return `${fx(esc(x))} ${v?'':'אינו '}${PN[p]}`};
  return `<div class="qpf">${order.map((k,i)=>{const e=pr.K.get(k),refs=e.from.map(f=>order.indexOf(f)+1).filter(x=>x>0);
    return `<div class="ps"><div class="pf"><span class="pn">${i+1}</span>${fx(esc(txt(k,e.v)))}</div><div class="pj">${nm(k,e.v)}: ${e.given?'נתון':esc(e.why)+(refs.length?`. לפי ${refs.length>1?'שורות':'שורה'} ${refs.join(', ')}`:'')}</div></div>`}).join('')}</div>`}
const CELL={given:x=>[x.v?'✓':'✗','gv '+(x.v?'y':'n'),'נתון'],proved:x=>[x.v?'✓':'✗',x.v?'y':'n',x.v?'נובע':'לא ייתכן'],exact:x=>[x.v?'✓':'✗',x.v?'y':'n',x.v?'נובע':'לא ייתכן'],open:()=>['תלוי','op','לא נובע'],seen:x=>[x.v?'✓ ?':'✗ ?','un','לא הוכרע'],none:()=>['?','un','לא הוכרע']};
function renderAbsSide(){const opt=(l,c)=>l.map(([v,t])=>`<option value="${v}" ${v===c?'selected':''}>${t}</option>`).join('');
  const box=(r,i)=>{const o=r.op?OPS[r.op]:null,before=ABS.slice(0,i).map(x=>[x.name,x.name]),del=ABS.length>1?`<button class="x" data-rdel="${i}" aria-label="הסר את ${r.name}">×</button>`:'';
    return `<div class="qbox"><div class="qrow"><span class="name v">${r.name}</span>${o?`<select data-ro="${i}" data-f="op" aria-label="פעולה">${opt(Object.entries(OPS).map(([k,x])=>[k,x.l]),r.op)}</select>`:'<span class="lab">יחס לא ידוע מעל A</span>'}${del}</div>
      ${o?`<div class="qrow"><label class="cell">${o.two?'ראשון':'של'}<select data-ro="${i}" data-f="a">${opt(before,r.a)}</select></label>${o.two?`<label class="cell">שני<select data-ro="${i}" data-f="b">${opt(before,r.b)}</select></label>`:''}${o.k?`<label class="cell">מעריך<input type="number" min="0" max="9" class="rn" dir="ltr" data-ro="${i}" data-f="k" value="${kOf(r)}"></label>`:''}</div><div class="gfset fx">${r.name} = ${esc(symOf(r))}</div>`:''}
      <div class="rlchips">${PK.map(p=>{const g=r.giv[p]||'';return `<button class="rlchip ${g}" data-rg="${i}|${p}" aria-label="${PN[p]}: ${g==='y'?'נתון שמתקיים':g==='n'?'נתון שלא מתקיים':'לא נתון'}"><b>${g==='y'?'✓':g==='n'?'✗':'·'}</b>${PN[p]}</button>`}).join('')}</div></div>`};
  const room=ABS.length<NAMES.length;
  document.getElementById('rlobjs').innerHTML=`${ABS.map(box).join('')}<div class="qbox"><div class="lab">הוסף יחס</div><div class="addrow"><button class="addb" data-radd="free" ${room?'':'disabled'}>+ יחס לא ידוע</button><button class="addb" data-radd="op" ${room?'':'disabled'}>+ יחס מפעולה</button></div>
    <p class="hint">לחיצה על תכונה מחליפה בין שלושה מצבים: לא נתון, נתון שמתקיים, נתון שלא מתקיים. אפשר לתת נתונים גם על יחס מפעולה.</p></div>`}
function renderAbsMain(){const R=solveAbs(ABS),{pr,mo,st}=R,sizes=[1,2,3,4].filter(n=>mo.exh[n]),clash=ABS.some(r=>PK.some(p=>st[r.name][p].clash));
  const kind=r=>{const s=st[r.name],eq=holds(s.refl)&&holds(s.sym)&&holds(s.trans),wk=holds(s.refl)&&holds(s.wanti)&&holds(s.trans),sr=holds(s.irr)&&holds(s.trans),tot=holds(s.comp);
    return eq&&wk?'יחס השוויון':eq?'יחס שקילות':wk?(tot?'סדר מלא (רפלקסיבי)':'סדר חלקי (רפלקסיבי)'):sr?(tot?'סדר מלא (אנטי-רפלקסיבי)':'סדר חלקי (אנטי-רפלקסיבי)'):''};
  let top='';
  if(pr.conflict){const c=pr.conflict;top=`<div class="qwarn"><b>הנתונים סותרים זה את זה.</b> ${esc(c.why)}.<div class="rlex">${c.lits.map(l=>proofHtml(pr,l.x+'|'+l.p,ABS)).join('')}</div></div>`}
  else if(!mo.found)top=`<div class="qwarn">לא נמצא אף יחס שמקיים את כל הנתונים מעל קבוצות של עד ארבעה איברים. ייתכן שהנתונים סותרים, אבל הכללים לא הוכיחו זאת.</div>`;
  if(clash)top+=`<div class="qwarn">שגיאה פנימית: כלל הסיק מסקנה שדוגמה סותרת. אל תסמוך על התוצאה הזאת, ודווח עליה.</div>`;
  let ex='';
  if(PICK&&!pr.conflict){const [x,p]=PICK.split('|'),r=ABS.find(q=>q.name===x),s=r&&st[x][p];if(s){const head=`<div class="qph"><span>${fx(esc(x))} ${PN[p]}</span>${fx(esc(PF[p].replace(/X/g,x)))}</div>`,se=mo.seen[x][p];
    const open=(slot,t)=>se[slot]?`<button class="btn sm" data-rex="${x}|${p}|${slot}">${t}</button>`:'';let body='';
    if(s.kind==='given')body=`<p class="hint">נתון.</p>`;
    else if(s.kind==='proved')body=`<p class="hint">${s.v?'נובע מהנתונים.':'לא ייתכן לפי הנתונים.'} ההוכחה, שורה אחר שורה:</p>${proofHtml(pr,PICK,ABS)}`;
    else if(s.kind==='exact')body=`<p class="hint">${s.v?'נובע מהנתונים':'לא ייתכן לפי הנתונים'}, אבל לא לפי כלל מהרשימה אלא בבדיקה ממצה: נבדקו כל היחסים המתאימים מעל קבוצות של אחד, שניים ושלושה איברים. כאן זה מספיק, כי כל הנתונים והתכונה הם טענות ״לכל״ על שלושה איברים לכל היותר: דוגמה נגדית, אילו הייתה, הייתה נשארת דוגמה נגדית גם אחרי שמצמצמים את הקבוצה לאיברים שמופיעים בה.</p>`;
    else if(s.kind==='open')body=`<p class="hint">לא נובע מהנתונים: יש יחסים שמקיימים את כל הנתונים והתכונה מתקיימת בהם, ויש כאלה שבהם היא לא מתקיימת. זו הכרעה סופית, כי כל דוגמה היא יחס ממשי.</p><div class="rlbar">${open('T','פתח דוגמה שבה התכונה מתקיימת')}${open('F','פתח דוגמה נגדית')}</div>`;
    else if(s.kind==='seen')body=`<p class="hint">לא הוכרע. ${s.v?'התכונה התקיימה בכל הדוגמאות שנבדקו':'התכונה לא התקיימה באף דוגמה שנבדקה'}, אבל אין כלל שמוכיח זאת, והבדיקה מכסה רק קבוצות קטנות. ייתכן שזה משפט נכון, וייתכן שיש דוגמה ${s.v?'נגדית':'מקיימת'} גדולה יותר.</p><div class="rlbar">${open(s.v?'T':'F','פתח דוגמה')}</div>`;
    else body=`<p class="hint">לא הוכרע: לא נמצאה אף דוגמה שמקיימת את הנתונים.</p>`;
    ex=`<section class="gfb"><div class="qpb">${head}${body}</div></section>`}}
  document.getElementById('main').innerHTML=`<div class="gfwrap rl">${top}
    <section class="gfb"><h3>מה נובע מהנתונים</h3><p class="hint">שורה לכל יחס ועמודה לכל תכונה. לחיצה על תא פותחת את ההסבר: הוכחה, או דוגמאות.</p>
      <div class="rlmw"><table class="rlab"><thead><tr><th></th>${PK.map(p=>`<th scope="col">${PN[p]}<span class="fx">${PF[p]}</span></th>`).join('')}<th scope="col">סיווג</th></tr></thead><tbody>
      ${ABS.map(r=>`<tr><th scope="row">${fx(`${r.name}${r.op?' = '+esc(symOf(r)):''}`)}</th>${PK.map(p=>{const s=st[r.name][p],[sym,cl,lab]=CELL[s.kind](s),k=r.name+'|'+p;return `<td class="${cl}${PICK===k?' cur':''}"><button data-rpk="${k}" aria-pressed="${PICK===k}" aria-label="${r.name} ${PN[p]}: ${lab}"><b>${sym}</b><span>${lab}</span></button></td>`}).join('')}<td class="kd">${kind(r)}</td></tr>`).join('')}
      </tbody></table></div></section>${ex}</div>`;
  document.getElementById('card').innerHTML=`<div class="gfcard rl"><div class="cardhead"><h2>איך לקרוא</h2></div>
    <div class="rlleg"><span class="rlk gv y">✓</span><span>נתון</span><span class="rlk y">✓</span><span>נובע מהנתונים, עם הוכחה</span><span class="rlk n">✗</span><span>לא ייתכן לפי הנתונים, עם הוכחה</span><span class="rlk op">תלוי</span><span>לא נובע: יש דוגמה לכאן ודוגמה לכאן</span><span class="rlk un">✓ ?</span><span>לא הוכרע: כך בכל הדוגמאות הקטנות, בלי הוכחה</span></div>
    <p class="qnote" role="note"><b>מה מובטח, ומה לא.</b> ״נובע״ ו״לא ייתכן״ מגיעים משרשרת של משפטים, והיא מוצגת בהסבר. ״לא נובע״ מגיע מדוגמאות ממשיות, ולכן הוא סופי. ״לא הוכרע״ אומר שהכלים כאן לא הספיקו, ולא שהטענה נכונה או שגויה.</p>
    <p class="hint">הדוגמאות: ${mo.found} יחסים שמקיימים את הנתונים, מתוך ${mo.tried} שנבדקו. הבדיקה מלאה לקבוצות בגודל ${sizes.length?sizes.join(', '):'—'}, ובגדלים האחרים עד ארבע היא מדגמית. ההנחה בכל מקום: A אינה ריקה.</p></div>`}
function renderAbs(){renderAbsSide();renderAbsMain()}
function absClick(t){const g=t.closest('[data-rg]'),pk=t.closest('[data-rpk]'),del=t.closest('[data-rdel]'),add=t.closest('[data-radd]'),exb=t.closest('[data-rex]');
  if(g){const [i,p]=g.dataset.rg.split('|'),r=ABS[Number(i)],c=r.giv[p];if(!c)r.giv[p]='y';else if(c==='y')r.giv[p]='n';else delete r.giv[p];renderAbs()}
  else if(pk){PICK=PICK===pk.dataset.rpk?null:pk.dataset.rpk;renderAbsMain()}
  else if(del&&ABS.length>1){const i=Number(del.dataset.rdel),nm=ABS[i].name;ABS.forEach(r=>{if(r.op&&(r.a===nm||(OPS[r.op].two&&r.b===nm))){delete r.op}});ABS.splice(i,1);PICK=null;renderAbs()}
  else if(add){const name=[...NAMES].find(x=>!ABS.some(r=>r.name===x));if(!name)return;const src=ABS[ABS.length-1].name;ABS.push(add.dataset.radd==='op'?{name,op:'tc',a:src,b:src,k:2,giv:{}}:{name,giv:{}});renderAbs()}
  else if(exb){const [x,p,slot]=exb.dataset.rex.split('|'),R=solveAbs(ABS),m=R.mo.seen[x][p][slot];if(!m)return;
    /* the example becomes a concrete relation: the same list, with the unknown relations filled in */
    KIND='custom';PARAM.custom='abcd'.slice(0,m.n).split('').join(', ');A=buildSet();RELS=ABS.map((r,i)=>{const j=R.mo.B.indexOf(i);return r.op?{name:r.name,op:r.op,a:r.a,b:r.b,k:r.k}:{name:r.name,M:m.base[j].slice()}});
    CUR=Math.max(0,ABS.findIndex(r=>r.name===x));HL=slot==='F'?p:null;SEL=null;MODE='conc';REL.render()}}
return{
/* for tests */
lib:{empty,full,ident,union,inter,diff,compl,inverse,compose,tclose,analyze,classes,order,pairs,size,same,subset,flags,clauses,propagate,models,solveAbs,evalList,OPS,PK},
render(){const seg=`<div class="seg rlmode" role="group" aria-label="סוג העבודה">${[['conc','יחס מסוים'],['abs','תכונות בלבד']].map(([v,l])=>`<button data-rmode="${v}" aria-pressed="${MODE===v}">${l}</button>`).join('')}</div>`;
  document.getElementById('conds').innerHTML=`<div class="qb rl"><div class="colhead"><h2>${MODE==='abs'?'היחסים והנתונים':'הקבוצה והיחס'}</h2><span class="lab">${MODE==='abs'?'יחסים שידועות רק התכונות שלהם':'יחס מעל קבוצה סופית'}</span></div>${seg}<div id="rlobjs" class="qlist"></div></div>`;
  if(MODE==='abs')renderAbs();else renderAll()}};
})();
