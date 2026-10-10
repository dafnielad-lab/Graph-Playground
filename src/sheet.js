/* ---------- formula-sheet mode: objects, operations, live substitution ---------- */
const SHEET=(()=>{
const V=x=>`<span class="qv">${x}</span>`;
/* objects of the question, in order; a derived graph may only use objects defined above it.
   graph properties are tri-state: 'y' given true, 'n' given false, 'u' unknown */
const newG=(name,o)=>Object.assign({t:'g',name,n:null,m:null,c:null,D:null,dl:null,f:null,chi:null,al:null,nu:null,be:null,rho:null,lv:null,om:null,pl:'u',tr:'u',bp:'u',fo:'u',tf:'u',sc:'u',eu:'u',ha:'u',pm:'u',more:false},o);
let O=[newG('G',{n:10,c:1,pl:'y'}),
       {t:'v',name:'v',in:'G',q:'one',d:3,cut:false},
       newG('H',{op:'delv',src:'G',arg:'v',c:2})];
const NAMES={v:['v','u','w','x','y','z'],e:['e','e₂','e₃','e₄'],s:['S','T','A','B'],g:['H','K','L','M','N']};
const OPS={delv:['הסרת הצומת','v'],dele:['הסרת הקשת','e'],delS:['הסרת קבוצת הצמתים','s'],adde:['הוספת קשת',null],contr:['כיווץ הקשת','e'],subd:['העדנת הקשת','e'],compl:['המשלים',null],ind:['תת-גרף מושרה על','s'],comp:['רכיב קשירות',null],span:['תת-גרף פורש',null],join:['חיבור הרכיבים במספר קשתות מינימלי',null]};
const SYM={n:'n',m:'m',c:'c',D:'Δ',dl:'δ',f:'f',chi:'χ',al:'α',nu:'ν',be:'β',rho:'ρ',om:'ω',lv:'ℓ'};
const DEF={n:'מספר הצמתים',m:'מספר הקשתות',c:'מספר רכיבי הקשירות',D:'הדרגה המקסימלית',dl:'הדרגה המינימלית',f:'מספר הפאות בשיכון מישורי',chi:'מספר הצביעה',al:'גודל קבוצה בלתי תלויה מקסימלית',nu:'גודל זיווג מקסימום',be:'גודל מינימלי של כיסוי בצמתים',rho:'גודל מינימלי של כיסוי בקשתות',om:'גודל קליקה מקסימלית',lv:'מספר העלים'};
const PROPS={pl:'מישורי',tr:'עץ',bp:'דו-צדדי',conn:'קשיר',fo:'יער',tf:'בלי משולשים',sc:'איזומורפי למשלים',eu:'אוילרי',ha:'המילטוני',pm:'יש זיווג מושלם'};
const COL=new Set(['Σ']);
const by=n=>O.find(o=>o.name===n),graphs=()=>O.filter(o=>o.t==='g');
const fresh=t=>NAMES[t].find(n=>!by(n))||NAMES[t][0]+O.length;
function ensureArg(g){const need=OPS[g.op][1];if(!need){g.arg=null;return}
  const cur=by(g.arg);if(cur&&cur.t===need&&cur.in===g.src&&O.indexOf(cur)<O.indexOf(g))return;
  let a=O.find(o=>o.t===need&&o.in===g.src&&O.indexOf(o)<O.indexOf(g));
  if(!a){a=need==='v'?{t:'v',name:fresh('v'),in:g.src,q:'one',d:null,cut:false}:need==='e'?{t:'e',name:fresh('e'),in:g.src,bridge:false}:{t:'s',name:fresh('s'),in:g.src,k:null,prop:''};O.splice(O.indexOf(g),0,a)}
  g.arg=a.name}
/* a complement is named after its source with a bar above, not with a new letter */
const barName=n=>(n+'\u0304').normalize('NFC'),isBar=n=>n.normalize('NFD').includes('\u0304');
function rename(o,nw){const old=o.name;for(const x of O){if(x.in===old)x.in=nw;if(x.src===old)x.src=nw;if(x.arg===old)x.arg=nw}o.name=nw}
function fixNames(){for(const g of O)if(g.t==='g'&&g.op){
  if(g.op==='compl'){const w=barName(g.src);if(g.name!==w&&!by(w))rename(g,w)}
  else if(isBar(g.name))rename(g,fresh('g'))}}
function removeObj(name){const dep=O.filter(o=>o.in===name||o.src===name||o.arg===name).map(o=>o.name);O=O.filter(o=>o.name!==name);dep.forEach(removeObj)}
const opt=(list,cur)=>list.map(([v,l])=>`<option value="${v}" ${v===cur?'selected':''}>${l}</option>`).join('');
/* every numeric cell takes a number or a range: "3", "2-5", "3-" (at least), "-5" (at most) */
function parseNum(t){t=String(t).trim().replace(/\s+/g,'');let m;
  if(t==='')return{v:null,r:null};
  if(/^\d+$/.test(t))return{v:Number(t),r:null};
  if((m=/^(\d*)[-–…:](\d*)$/.exec(t))&&(m[1]||m[2])||(m=/^(?:>=|≥)(\d+)()$/.exec(t))||(m=/^()(?:<=|≤)(\d+)$/.exec(t))||(m=/^(\d+)\+()$/.exec(t))){const lo=m[1]===''?null:Number(m[1]),hi=m[2]===''?null:Number(m[2]);
    if(lo!==null&&hi!==null&&lo>hi)return{v:null,r:null,bad:true};return lo!==null&&lo===hi?{v:lo,r:null}:{v:null,r:[lo,hi]}}
  return{v:null,r:null,bad:true}}
const rgOf=(o,k)=>(o.rg&&o.rg[k])||null;
const num=(i,k,val,lab)=>{const o=O[i],tx=o.tx&&o.tx[k]!==undefined?o.tx[k]:(val===null||val===undefined?'':val);return `<label class="cell">${lab}<input type="text" inputmode="numeric" class="rn" dir="ltr" data-i="${i}" data-k="${k}" data-r="1" value="${String(tx).replace(/"/g,'')}" placeholder="?" id="f${i}${k}" autocomplete="off"></label>`};
const tri=(i,k,val,lab)=>`<label class="cell">${lab}<select data-i="${i}" data-k="${k}" id="f${i}${k}">${opt([['u','לא ידוע'],['y','כן'],['n','לא']],val)}</select></label>`;
const chk=(i,k,val,lab)=>`<label class="cell">${lab}<input type="checkbox" data-i="${i}" data-k="${k}" id="f${i}${k}" ${val?'checked':''}></label>`;
function renderObjs(){
  document.getElementById('qobjs').innerHTML=O.map((o,i)=>{const gs=opt(graphs().filter(g=>o.t!=='g'||O.indexOf(g)<i).map(g=>[g.name,g.name]),o.t==='g'?o.src:o.in),x=o.name==='G'?'':`<button class="x" data-del="${o.name}" aria-label="הסר את ${o.name}">×</button>`;
    if(o.t==='g')return `<div class="qbox"><div class="qrow"><span class="name">${o.name}</span>${o.op?`<span>=</span><select data-i="${i}" data-k="op" id="f${i}op" aria-label="פעולה">${opt(Object.entries(OPS).map(([k,v])=>[k,v[0]]),o.op)}</select>${o.arg?`<select data-i="${i}" data-k="arg" id="f${i}arg" aria-label="על מה">${opt(O.filter(a=>a.t===OPS[o.op][1]&&a.in===o.src&&O.indexOf(a)<i).map(a=>[a.name,a.name]),o.arg)}</select>`:''}<span>${o.op==='compl'||o.op==='comp'||o.op==='span'?'של':'מתוך'}</span><select data-i="${i}" data-k="src" id="f${i}src" aria-label="גרף מקור">${gs}</select>`:'<span>הגרף הנתון</span>'}${x}</div>
      <div class="qrow">${num(i,'n',o.n,'צמתים')}${num(i,'m',o.m,'קשתות')}${num(i,'c',o.c,'רכיבים')}</div>
      <div class="qrow">${tri(i,'pl',o.pl,'מישורי')}<label class="cell">עץ<select data-i="${i}" data-k="tr" id="f${i}tr">${opt([['u','לא ידוע'],['y','עץ'],['f','יער'],['n','לא']],o.tr)}</select></label>${tri(i,'bp',o.bp,'דו-צדדי')}</div>
      ${o.more?`<div class="qrow">${['D','dl','f','chi','om','al','nu','be','rho','lv'].map(k=>num(i,k,o[k],`<span class="fx">${SYM[k]}</span>`)).join('')}</div><div class="qrow">${tri(i,'tf',o.tf,'בלי משולשים')}${tri(i,'sc',o.sc,'איזומורפי למשלים')}${tri(i,'eu',o.eu,'אוילרי')}${tri(i,'ha',o.ha,'המילטוני')}${tri(i,'pm',o.pm,'זיווג מושלם')}</div>`:''}
      <button class="link" data-more="${i}">${o.more?'הסתר גדלים ותכונות נוספים':'גדלים ותכונות נוספים'}</button></div>`;
    if(o.t==='v')return `<div class="qbox"><div class="qrow"><span class="name v">${o.name}</span><select data-i="${i}" data-k="q" id="f${i}q" aria-label="כמת">${opt([['one','צומת מסוים'],['all','כל צומת'],['ex','קיים צומת']],o.q)}</select><span>ב־</span><select data-i="${i}" data-k="in" id="f${i}in" aria-label="בגרף">${gs}</select>${x}</div>${o.q==='one'?`<div class="qrow"><span class="cell">איזה צומת</span><select data-i="${i}" data-k="w" id="f${i}w" aria-label="איזה צומת">${opt([['','צומת כלשהו שנבחר'],['max','בעל הדרגה הגבוהה ביותר'],['min','בעל הדרגה הנמוכה ביותר']],o.w||'')}</select></div>`:''}<div class="qrow">${num(i,'d',o.d,'דרגה')}${chk(i,'cut',o.cut,'צומת מפריד')}</div></div>`;
    if(o.t==='e')return `<div class="qbox"><div class="qrow"><span class="name v">${o.name}</span><span>קשת ב־</span><select data-i="${i}" data-k="in" id="f${i}in" aria-label="בגרף">${gs}</select>${x}</div><div class="qrow">${chk(i,'bridge',o.bridge,'גשר (הסרתה מנתקת)')}</div></div>`;
    return `<div class="qbox"><div class="qrow"><span class="name v">${o.name}</span><span>קבוצת צמתים ב־</span><select data-i="${i}" data-k="in" id="f${i}in" aria-label="בגרף">${gs}</select>${x}</div><div class="qrow">${num(i,'k',o.k,'גודל')}<select data-i="${i}" data-k="prop" id="f${i}prop" aria-label="תכונה">${opt([['','בלי תכונה נוספת'],['indep','בלתי תלויה'],['clique','קליקה'],['cover','כיסוי בצמתים'],['side','צד בגרף דו-צדדי']],o.prop)}</select></div></div>`}).join('')}
/* symbol of a graph quantity: the given value in colour, otherwise the symbol (with the graph's name unless it is G) */
/* with several graphs on the sheet every symbol carries the name of its graph */
const sub=g=>!g.virt&&O.filter(o=>o.t==='g'&&!o.virt).length<2?'':`<sub>${g.name}</sub>`;
const MK=/(?<![A-Za-z])(?:deg|[nmcf])(?![A-Za-z])|[ΔδχανβρωℓΓ]/g;
const mk=(x,g)=>{const s=sub(g);if(!s||!x)return x;return x.split(/(<[^>]*>)/).map((p,i,A)=>i%2?p:p.replace(MK,(a,o)=>o+a.length===p.length&&A[i+1]==='<sub>'?a:a+s)).join('')};
/* operation formulas name the graph in brackets: n(H) becomes n with the name beneath */
const fnSub=x=>{for(const h of O.filter(o=>o.t==='g'))x=x.split(`(${h.name})`).join(`<sub>${h.name}</sub>`);return x};
const COLG=new Set();
/* a vertex degree is exact, or a range with either end optional */
const dLo=v=>v.dm==='rng'?(v.d1??null):v.d,dHi=v=>v.dm==='rng'?(v.d2??null):v.d,dEx=v=>dLo(v)!==null&&dLo(v)===dHi(v)?dLo(v):null;
const allV=g=>O.find(o=>o.t==='v'&&o.in===g.name&&o.q==='all'&&(dLo(o)!==null||dHi(o)!==null));
const allDeg=g=>{const v=allV(g);return v?dEx(v):null};
const rngTxt=(lo,mid,hi)=>`${lo!==null?V(lo)+' ≤ ':''}${mid}${hi!==null?' ≤ '+V(hi):''}`;
/* a chosen vertex can be the one of highest or lowest degree; its exact degree then fixes Δ or δ */
const ext=(g,w)=>O.find(o=>o.t==='v'&&o.in===g.name&&o.q==='one'&&o.w===w);
const val=(g,k)=>{if(g[k]!==null&&g[k]!==undefined)return g[k];if(k!=='D'&&k!=='dl')return null;const a=allDeg(g);if(a!==null)return a;const v=ext(g,k==='D'?'max':'min');return v?dEx(v):null};
const sy=(g,k)=>{const v=val(g,k);return v!==null?V(v):SYM[k]+sub(g)};
const degOf=v=>dEx(v)!==null?V(dEx(v)):v.q==='one'&&v.w?(x=>x.includes('class="q')?x:`<span class="qs">${x}</span>`)(sx(by(v.in),v.w==='max'?'D':'dl')):`deg${sub(by(v.in))}(${v.name})`;
/* what is known about a quantity: its own value, or what the operation that built the graph makes of the source graph's quantities.
   num: a number; otherwise html is an expression in the remaining symbols */
const NUM=v=>({num:v,html:V(v),atom:true}),EXP=h=>({num:null,html:h,atom:false}),OPD=e=>e.atom?e.html:`(${e.html})`;
const plus=(e,c)=>c===0?e:e.num!==null?NUM(e.num+c):EXP(`${OPD(e)} ${c<0?'−':'+'} ${V(Math.abs(c))}`);
/* the components defined for a graph; when their number equals c they are all of its components, each a different one */
const compsOf=P=>O.filter(o=>o.t==='g'&&o.op==='comp'&&o.src===P.name);
const fullComps=P=>{const c=ex(P,'c').num,L=compsOf(P);return c!==null&&L.length===c?L:null};
const ownB=(o,k)=>val(o,k)!==null?[val(o,k),val(o,k)]:rgOf(o,k);
function ex(g,k,depth){
  const own=val(g,k);if(own!==null)return NUM(own);
  const me={num:null,html:SYM[k]+sub(g),atom:true,self:true};
  /* a tree or a forest fixes the number of edges from the vertices and components */
  if(k==='m'&&(depth||0)<=12){const t=prop(g,'tr');if(t==='y'||prop(g,'fo')==='y'){const N={...ex(g,'n',(depth||0)+1),self:false};if(t==='y')return plus(N,-1);
    const C=ex(g,'c',(depth||0)+1);return N.num!==null&&C.num!==null?NUM(N.num-C.num):C.num!==null?plus(N,-C.num):EXP(`${OPD(N)} − ${C.html}`)}}
  if(!g.op||(depth||0)>12)return me;
  const src=by(g.src),a=by(g.arg),E=x=>({...ex(src,x,(depth||0)+1),self:false}),op=g.op;
  if(k==='n'){if(op==='delv'||op==='contr')return plus(E('n'),-1);if(op==='subd')return plus(E('n'),1);if(['dele','adde','compl','span','join'].includes(op))return E('n');
    if(op==='delS')return a.k!==null?plus(E('n'),-a.k):EXP(`${OPD(E('n'))} − |${a.name}|`);if(op==='ind')return a.k!==null?NUM(a.k):{num:null,html:`|${a.name}|`,atom:true}}
  if(k==='m'){if(op==='delv'){const d=dEx(a);return d!==null?plus(E('m'),-d):EXP(`${OPD(E('m'))} − ${degOf(a)}`)}
    if(op==='dele')return plus(E('m'),-1);if(op==='adde'||op==='subd')return plus(E('m'),1);
    if(op==='join'){const M=E('m'),C=E('c');return C.num!==null?plus(M,C.num-1):EXP(`${OPD(M)} + ${C.html} − 1`)}
    if(op==='compl'){const N=E('n'),M=E('m');return N.num!==null&&M.num!==null?NUM(N.num*(N.num-1)/2-M.num):EXP(`${OPD(N)}·(${N.html} − 1) / 2 − ${OPD(M)}`)}
    if(op==='ind'){if(a.prop==='indep')return NUM(0);if(a.prop==='clique'&&a.k!==null)return NUM(a.k*(a.k-1)/2)}}
  if(op==='comp'&&(k==='n'||k==='m')){const L=fullComps(src);if(L){const others=L.filter(x=>x!==g);if(others.every(x=>val(x,k)!==null))return plus(E(k),-others.reduce((t,x)=>t+val(x,k),0))}}
  if(k==='c'){if(op==='dele'&&a.bridge)return plus(E('c'),1);if(op==='contr'||op==='subd')return E('c');if(op==='comp'||op==='join')return NUM(1)}
  if((k==='D'||k==='dl')&&op==='compl'){const N=E('n'),d=E(k==='D'?'dl':'D');return N.num!==null&&d.num!==null?NUM(N.num-1-d.num):EXP(`${OPD(N)} − 1 − ${OPD(d)}`)}
  return me}
/* a range for a quantity: given directly, or carried over from the source graph by the operation */
const bounds=(g,k,d)=>{const e=ex(g,k,d);return e.num!==null?[e.num,e.num]:interval(g,k,d)};
const shift=(b,c)=>b&&[b[0]===null?null:b[0]+c,b[1]===null?null:b[1]+c];
const span2=(b,lo,hi)=>b&&[b[0]===null||hi===null?null:b[0]-hi,b[1]===null||lo===null?null:b[1]-lo];
function interval(g,k,depth){
  const own=rgOf(g,k);if(own)return own;
  if(!g.op||(depth||0)>12)return null;
  const src=by(g.src),a=by(g.arg),E=x=>bounds(src,x,(depth||0)+1),op=g.op;let r=null;
  if(k==='n'){if(op==='delv'||op==='contr')r=shift(E('n'),-1);else if(op==='subd')r=shift(E('n'),1);else if(['dele','adde','compl','span','join'].includes(op))r=E('n');
    else if(op==='delS')r=span2(E('n'),a.k!==null?a.k:(rgOf(a,'k')||[null,null])[0],a.k!==null?a.k:(rgOf(a,'k')||[null,null])[1]);else if(op==='ind')r=rgOf(a,'k')}
  if(k==='m'){if(op==='delv')r=span2(E('m'),dLo(a),dHi(a));else if(op==='dele')r=shift(E('m'),-1);else if(op==='adde'||op==='subd')r=shift(E('m'),1);else if(op==='join'){const M=E('m'),C=E('c');r=M&&C&&[M[0]===null||C[0]===null?null:M[0]+C[0]-1,M[1]===null||C[1]===null?null:M[1]+C[1]-1]}}
  if(k==='c'){const C=E('c');if(op==='dele')r=a.bridge?shift(C,1):C&&[C[0],C[1]===null?null:C[1]+1];else if(op==='adde')r=C&&[C[0]===null?null:Math.max(1,C[0]-1),C[1]];else if(op==='contr'||op==='subd')r=C}
  if(op==='comp'&&(k==='n'||k==='m')){const L=fullComps(src),Pb=E(k),fl=k==='n'?1:0;
    if(L&&Pb){const ob=L.filter(x=>x!==g).map(x=>ownB(x,k));
      if(ob.every(Boolean)){const sLo=ob.reduce((t,b)=>t+(b[0]??fl),0),sHi=ob.some(b=>b[1]===null)?null:ob.reduce((t,b)=>t+b[1],0);
        r=[Pb[0]===null||sHi===null?fl:Math.max(fl,Pb[0]-sHi),Pb[1]===null?null:Pb[1]-sLo]}
    }
    /* not all components are known: the others still take at least what is known about them, and a vertex each */
    if(!r&&Pb&&Pb[1]!==null){const sib=compsOf(src).filter(x=>x!==g),c=ex(src,'c').num,hidden=c!==null?Math.max(0,c-sib.length-1):0;
      const take=sib.reduce((t,x)=>t+((ownB(x,k)||[null])[0]??fl),0)+(k==='n'?hidden:0);if(take>0)r=[fl,Pb[1]-take]}}
  return r&&(r[0]!==null||r[1]!==null)&&r[0]!==r[1]?r:null}
const sx=(g,k)=>{const e=ex(g,k);return e.num!==null?V(e.num):e.self?e.html:`<span class="qs">${OPD(e)}</span>`};
const cMany=g=>(g.c!==null&&g.c>1)||!!(rgOf(g,'c')&&rgOf(g,'c')[0]>1);
/* the tree field also offers "forest": a forest is a tree exactly when it has one component */
/* properties pass from a graph to what an operation makes of it: a subgraph of a forest is a forest, of a planar graph is planar, and so on */
const SUBG=['delv','dele','delS','ind','comp','span'],KEEP={fo:[...SUBG,'contr','subd','join'],pl:[...SUBG,'contr','subd','join'],bp:[...SUBG,'join'],tf:[...SUBG,'join']};
const from=(g,k,d)=>!!(g.op&&KEEP[k].includes(g.op)&&(d||0)<12&&by(g.src)&&prop(by(g.src),k,(d||0)+1)==='y');
const forestish=(g,d)=>g.tr==='y'||g.tr==='f'||from(g,'fo',d);
const connOf=g=>g.c===1||g.tr==='y'||g.op==='comp'||g.op==='join'||g.eu==='y'||g.ha==='y'?'y':cMany(g)?'n':'u';
/* a forest is a tree exactly when it is connected; a component of a forest is therefore a tree */
const isTree=(g,d)=>g.tr==='y'?'y':g.tr==='n'?'n':forestish(g,d)?connOf(g):'u';
function prop(g,k,d){
  if(k==='tr')return isTree(g,d);if(k==='conn')return connOf(g);if(k==='fo')return forestish(g,d)?'y':'u';
  if(k==='pl'||k==='bp'){if(g[k]!=='u')return g[k];if(forestish(g,d)||from(g,k,d))return 'y';
    /* a graph with a non-planar (non-bipartite) subgraph is itself non-planar (non-bipartite); subdivision keeps planarity both ways */
    if(O.some(h=>h.t==='g'&&h.op&&h.src===g.name&&h[k]==='n'&&(SUBG.includes(h.op)||(k==='pl'&&h.op==='subd'))))return 'n';
    if(k==='pl'&&g.op==='subd'&&by(g.src)&&by(g.src).pl==='n')return 'n';
    if((g.op==='join'||g.op==='adde')&&by(g.src)&&by(g.src)[k]==='n')return 'n';return 'u'}
  if(k==='tf')return g.tf!=='u'?g.tf:forestish(g,d)||prop(g,'bp',d)==='y'||from(g,'tf',d)?'y':'u';
  return g[k]}
/* combinations of data that no graph satisfies; each entry is one sentence shown in red above the graph's formulas */
function issues(g){
  const R=[],b=k=>bounds(g,k)||[null,null],lo=k=>b(k)[0],hi=k=>b(k)[1],F=x=>`<span class="fx">${x}</span>`,X=g.name;
  const gt=(x,y)=>x!==null&&y!==null&&x>y;
  const nL=lo('n'),nH=hi('n'),mL=lo('m'),mH=hi('m'),cL=lo('c'),cH=hi('c'),DL=lo('D'),DH=hi('D'),dL=lo('dl'),dH=hi('dl');
  if(g.eu==='y'&&cMany(g))R.push('גרף אוילרי הוא קשיר, ולכן יש לו רכיב קשירות אחד.');
  if(g.ha==='y'&&cMany(g))R.push('גרף המילטוני הוא קשיר, ולכן יש לו רכיב קשירות אחד.');
  if(g.ha==='y'&&forestish(g))R.push('בעץ וביער אין מעגלים, ולכן הם אינם המילטוניים.');
  if(g.tr==='y'&&cMany(g))R.push('עץ הוא גרף קשיר, ולכן יש לו רכיב קשירות אחד בלבד.');
  if(forestish(g)&&g.pl==='n')R.push('עץ ויער הם תמיד מישוריים.');
  if(forestish(g)&&g.bp==='n')R.push('בעץ וביער אין מעגלים, ולכן הם דו-צדדיים.');
  if((forestish(g)||g.bp==='y')&&g.tf==='n')R.push(forestish(g)?'בעץ וביער אין מעגלים, ולכן אין משולשים.':'משולש הוא מעגל באורך אי-זוגי, ובגרף דו-צדדי אין כזה.');
  if(gt(cL,nH))R.push('מספר רכיבי הקשירות גדול ממספר הצמתים.');
  if(nH!==null&&gt(mL,nH*(nH-1)/2))R.push(`יותר קשתות ממה שיש בגרף פשוט: ${F('m ≤ n(n − 1) / 2')}.`);
  if(nL!==null&&cH!==null&&mH!==null&&mH<nL-cH)R.push(`פחות מדי קשתות למספר הרכיבים הזה: ${F('m ≥ n − c')}.`);
  if(nH!==null&&gt(DL,nH-1))R.push(`הדרגה המקסימלית גדולה מדי: ${F('Δ ≤ n − 1')}.`);
  if(gt(dL,DH))R.push('הדרגה המינימלית גדולה מהמקסימלית.');
  if(dL!==null&&nL!==null&&mH!==null&&dL*nL>2*mH)R.push(`הדרגה המינימלית גדולה מהדרגה הממוצעת: ${F('δ ≤ 2m / n')}.`);
  if(DH!==null&&nH!==null&&mL!==null&&DH*nH<2*mL)R.push(`הדרגה המקסימלית קטנה מהדרגה הממוצעת: ${F('Δ ≥ 2m / n')}.`);
  const ad=allDeg(g);if(ad!==null&&nL!==null&&nL===nH&&(ad*nL)%2)R.push('סכום הדרגות יוצא אי-זוגי, והוא חייב להיות פעמיים מספר הקשתות.');
  if(ad!==null&&nL!==null&&nL===nH&&mL!==null&&mL===mH&&g.m!==null&&ad*nL!==2*mL)R.push(`סכום הדרגות לא שווה לפעמיים מספר הקשתות: ${F(ad+'·'+nL+' ≠ 2·'+mL)}.`);
  if(g.tr==='y'&&g.m!==null&&nL!==null&&nL===nH&&g.m!==nL-1)R.push(`בעץ מספר הקשתות הוא ${F('n − 1')}.`);
  if(g.tr==='f'&&g.m!==null&&nL!==null&&nL===nH&&cL!==null&&cL===cH&&g.m!==nL-cL)R.push(`ביער מספר הקשתות הוא ${F('n − c')}.`);
  if(prop(g,'tr')==='y'&&nL!==null&&nL>=2&&gt(dL,1))R.push('בעץ עם שני צמתים לפחות יש עלה, ולכן הדרגה המינימלית היא אחת.');
  if(g.pl==='y'&&nH!==null&&nH>=3&&gt(mL,3*nH-6))R.push(`יותר מדי קשתות לגרף מישורי: ${F('m ≤ 3n − 6')}.`);
  if(g.pl==='y'&&prop(g,'tf')==='y'&&nH!==null&&nH>=3&&gt(mL,2*nH-4))R.push(`יותר מדי קשתות לגרף מישורי בלי משולשים: ${F('m ≤ 2n − 4')}.`);
  if(g.pl==='y'&&gt(dL,5))R.push('בגרף מישורי יש צומת מדרגה חמש לכל היותר.');
  if(g.pl==='y'&&gt(lo('chi'),4))R.push('גרף מישורי נצבע בארבעה צבעים לכל היותר.');
  if(g.pl==='n'&&((nH!==null&&nH<5)||(mH!==null&&mH<9)))R.push('גרף לא מישורי מכיל העדנה של K₅ או של K₃,₃, ולכן יש בו חמישה צמתים ותשע קשתות לפחות.');
  if(prop(g,'bp')==='y'&&gt(lo('chi'),2))R.push('גרף דו-צדדי נצבע בשני צבעים לכל היותר.');
  if(DH!==null&&gt(lo('chi'),DH+1))R.push(`מספר הצביעה גדול מדי: ${F('χ ≤ Δ + 1')}.`);
  if(gt(lo('om'),hi('chi')))R.push(`מספר הצביעה קטן מגודל הקליקה המקסימלית: ${F('χ ≥ ω')}.`);
  for(const [k,w] of [['chi','מספר הצביעה'],['al','הקבוצה הבלתי תלויה המקסימלית'],['om','הקליקה המקסימלית'],['be','הכיסוי בצמתים']])if(gt(lo(k),nH))R.push(`${w} גדול ממספר הצמתים.`);
  if(nH!==null&&lo('nu')!==null&&2*lo('nu')>nH)R.push(`הזיווג גדול מדי: ${F('ν ≤ n / 2')}.`);
  if(gt(lo('nu'),hi('be')))R.push(`כיסוי בצמתים קטן מהזיווג: ${F('β ≥ ν')}.`);
  if(g.al!==null&&g.be!==null&&nL!==null&&nL===nH&&g.al+g.be!==nL)R.push(`צריך להתקיים ${F('α + β = n')}.`);
  if(g.sc==='y'&&nL!==null&&nL===nH&&nL%4>1)R.push('בגרף שאיזומורפי למשלים שלו, מספר הצמתים נותן שארית אפס או אחת בחלוקה לארבע.');
  for(const o of O){if(o.in!==X)continue;
    if(o.t==='v'&&nH!==null&&gt(dLo(o),nH-1))R.push(`הדרגה של ${F(o.name)} גדולה מדי: לכל היותר ${F('n − 1')}.`);
    if(o.t==='v'&&gt(dLo(o),DH)&&g.D!==null)R.push(`הדרגה של ${F(o.name)} גדולה מהדרגה המקסימלית שנתונה.`);
    if(o.t==='v'&&gt(dL,dHi(o))&&g.dl!==null)R.push(`הדרגה של ${F(o.name)} קטנה מהדרגה המינימלית שנתונה.`);
    if(o.t==='s'){const k=ownB(o,'k');if(k&&gt(k[0],nH))R.push(`הקבוצה ${F(o.name)} גדולה ממספר הצמתים.`);
      if(k&&o.prop==='indep'&&g.al!==null&&gt(k[0],g.al))R.push(`הקבוצה הבלתי תלויה ${F(o.name)} גדולה מהמקסימלית שנתונה.`);
      if(k&&o.prop==='clique'&&g.om!==null&&gt(k[0],g.om))R.push(`הקליקה ${F(o.name)} גדולה מהמקסימלית שנתונה.`)}}
  const cn=ex(g,'c').num,CL=compsOf(g);if(cn!==null&&CL.length>cn)R.push('הוגדרו יותר רכיבי קשירות ממה שיש בגרף.');
  if(g.op==='comp'&&cMany(g))R.push('רכיב קשירות הוא קשיר, ולכן יש לו רכיב אחד.');
  return R}
function sheetFor(g){
  const s=sub(g),q=k=>sx(g,k),n=q('n'),m=q('m'),c=q('c'),D=q('D'),dl=q('dl'),ad=allDeg(g),F=[],X=g.name;
  const cb=s?`χ<sub>${isBar(X)&&g.src?g.src:barName(X)}</sub>`:'χ(complement)';let tp='קשרים מהפעולה';const add=(t,r,gen,st,need,cs)=>F.push({t,r,g:mk(gen,g),s:mk(st,g),need,tp,cs});
  const src=g.op?by(g.src):null;
  if(src){const n=sy(g,'n'),m=sy(g,'m'),c=sy(g,'c'),D=sy(g,'D'),Q=k=>sx(src,k),N=Q('n'),M=Q('m'),C=Q('c'),a=by(g.arg),P=src.name,rel=(t,gn,st)=>F.push({t,r:'מהפעולה',g:mk(fnSub(gn),src),s:mk(st,src),rel:1,tp});
    if(g.op==='delv'){rel('צמתים אחרי הסרת צומת',`n(${X}) = n(${P}) − 1`,`${n} = ${N} − 1`);rel('קשתות אחרי הסרת צומת',`m(${X}) = m(${P}) − deg(${a.name})`,`${m} = ${M} − ${degOf(a)}`);
      rel('רכיבי קשירות אחרי הסרת צומת',`c(${X}) ≤ c(${P}) + deg(${a.name}) − 1`,`${c} ≤ ${C} + ${degOf(a)} − 1`);if(dEx(a)===null&&(dLo(a)!==null||dHi(a)!==null))rel('קשתות אחרי הסרת צומת, לפי טווח הדרגה',`m(${P}) − max deg ≤ m(${X}) ≤ m(${P}) − min deg`,`${dHi(a)!==null?M+' − '+V(dHi(a))+' ≤ ':''}${m}${dLo(a)!==null?' ≤ '+M+' − '+V(dLo(a)):''}`);
      if(a.cut)rel(`${a.name} צומת מפריד`,`c(${X}) ≥ c(${P}) + 1`,`${c} ≥ ${C} + 1`)}
    if(g.op==='dele'){rel('צמתים אחרי הסרת קשת',`n(${X}) = n(${P})`,`${n} = ${N}`);rel('קשתות אחרי הסרת קשת',`m(${X}) = m(${P}) − 1`,`${m} = ${M} − 1`);
      if(a.bridge)rel(`${a.name} גשר`,`c(${X}) = c(${P}) + 1`,`${c} = ${C} + 1`);else rel('רכיבי קשירות אחרי הסרת קשת',`c(${P}) ≤ c(${X}) ≤ c(${P}) + 1`,`${C} ≤ ${c} ≤ ${C} + 1`)}
    if(g.op==='delS'){const k=a.k!==null?V(a.k):`|${a.name}|`;rel('צמתים אחרי הסרת קבוצה',`n(${X}) = n(${P}) − |${a.name}|`,`${n} = ${N} − ${k}`);rel('קשתות אחרי הסרת קבוצה',`m(${X}) ≥ m(${P}) − |${a.name}|·Δ(${P})`,`${m} ≥ ${M} − ${k}·${Q('D')}`);
      if(a.prop==='indep')rel('הקבוצה בלתי תלויה: כל קשת שנוגעת בה נספרת פעם אחת',`m(${X}) = m(${P}) − Σ deg(u), u ∈ ${a.name}`,`${m} = ${M} − Σ deg(u), u ∈ ${a.name}`)}
    if(g.op==='adde'){rel('צמתים אחרי הוספת קשת',`n(${X}) = n(${P})`,`${n} = ${N}`);rel('קשתות אחרי הוספת קשת',`m(${X}) = m(${P}) + 1`,`${m} = ${M} + 1`);rel('רכיבי קשירות אחרי הוספת קשת',`c(${P}) − 1 ≤ c(${X}) ≤ c(${P})`,`${C} − 1 ≤ ${c} ≤ ${C}`)}
    if(g.op==='contr'){rel('צמתים אחרי כיווץ קשת',`n(${X}) = n(${P}) − 1`,`${n} = ${N} − 1`);rel('קשתות אחרי כיווץ קשת (שכנים משותפים מתאחדים)',`m(${X}) ≤ m(${P}) − 1`,`${m} ≤ ${M} − 1`);rel('רכיבי קשירות אחרי כיווץ',`c(${X}) = c(${P})`,`${c} = ${C}`)}
    if(g.op==='subd'){rel('צמתים אחרי העדנת קשת',`n(${X}) = n(${P}) + 1`,`${n} = ${N} + 1`);rel('קשתות אחרי העדנת קשת',`m(${X}) = m(${P}) + 1`,`${m} = ${M} + 1`);rel('רכיבי קשירות אחרי העדנה',`c(${X}) = c(${P})`,`${c} = ${C}`);F.push({tp,t:'העדנה שומרת על מישוריות',r:'טענה 5.7',g:`${X} planar ⇔ ${P} planar`,s:'',rel:1,text:1})}
    if(g.op==='compl'){rel('צמתים במשלים',`n(${X}) = n(${P})`,`${n} = ${N}`);rel('קשתות בגרף ובמשלים',`m(${P}) + m(${X}) = n(n − 1) / 2`,`${M} + ${m} = ${N}·(${N} − 1) / 2`);const xd=allDeg(src);rel('דרגה במשלים',`deg${s}(u) = n − 1 − deg(u)`,`deg${s}(u) = ${N} − 1 − ${xd!==null?V(xd):'deg(u)'}`);
      rel('דרגה מקסימלית במשלים',`Δ(${X}) = n − 1 − δ(${P})`,`${D} = ${N} − 1 − ${Q('dl')}`);rel('קליקה במשלים היא קבוצה בלתי תלויה בגרף',`ω(${X}) = α(${P})`,`ω${s} = ${Q('al')}`)}
    if(g.op==='ind'){const k=a.k!==null?V(a.k):`|${a.name}|`;rel('צמתים בתת-גרף מושרה',`n(${X}) = |${a.name}|`,`${n} = ${k}`);rel('קשתות בתת-גרף מושרה',`m(${X}) ≤ m(${P})`,`${m} ≤ ${M}`);rel('צביעה של תת-גרף',`χ(${X}) ≤ χ(${P})`,`${q('chi')} ≤ ${Q('chi')}`);
      if(a.prop==='indep')rel('מושרה על קבוצה בלתי תלויה',`m(${X}) = 0`,`${m} = ${V(0)}`);if(a.prop==='clique')rel('מושרה על קליקה',`m(${X}) = |${a.name}|(|${a.name}| − 1) / 2`,`${m} = ${k}·(${k} − 1) / 2`)}
    if(g.op==='comp'){rel('רכיב קשירות הוא קשיר',`c(${X}) = 1`,`${c} = ${V(1)}`);rel('צמתים ברכיב',`n(${X}) ≤ n(${P})`,`${n} ≤ ${N}`);rel('קשתות ברכיב',`m(${X}) ≤ m(${P})`,`${m} ≤ ${M}`)}
    if(g.op==='join'){rel('אותם צמתים',`n(${X}) = n(${P})`,`${n} = ${N}`);rel('קשת אחת לכל רכיב נוסף',`m(${X}) = m(${P}) + c(${P}) − 1`,`${m} = ${M} + ${C} − 1`);rel('הגרף שמתקבל קשיר',`c(${X}) = 1`,`${c} = ${V(1)}`);
      rel('קשת בין רכיבים היא גשר: לא נסגר מעגל',`χ(${X}) = max(χ(${P}), 2),  ω(${X}) = max(ω(${P}), 2)`,`${q('chi')} = max(${Q('chi')}, 2)`);rel('דרגה מקסימלית אחרי החיבור',`Δ(${P}) ≤ Δ(${X}) ≤ Δ(${P}) + c(${P}) − 1`,`${Q('D')} ≤ ${D} ≤ ${Q('D')} + ${C} − 1`)}
    if(g.op==='span'){rel('תת-גרף פורש: אותם צמתים',`n(${X}) = n(${P})`,`${n} = ${N}`);rel('קשתות בתת-גרף פורש',`m(${X}) ≤ m(${P})`,`${m} ≤ ${M}`);rel('רכיבי קשירות בתת-גרף פורש',`c(${X}) ≥ c(${P})`,`${c} ≥ ${C}`);F.push({tp,t:'כל גרף קשיר מכיל עץ פורש',r:'טענה 2.6',g:`${P} connected ⇒ exists spanning tree`,s:'',rel:1,text:1})}}
  /* degrees */
  const CL=compsOf(g);
  if(CL.length){tp='רכיבי הקשירות';const full=fullComps(g),cn=ex(g,'c').num;
    for(const k of ['n','m']){const w=k==='n'?'הצמתים':'הקשתות',gen=CL.map(h=>`${k}(${h.name})`).join(' + '),st=CL.map(h=>sx(h,k)).join(' + ');
      if(full)add(`${w} של הגרף הם סכום ${w} ברכיבים`,'מההגדרה',`${k} = ${gen}`,`${q(k)} = ${st}`);
      else add(`סכום ${w} ברכיבים שהוגדרו`,'מההגדרה',`${gen} ≤ ${k}`,`${st} ≤ ${q(k)}`)}
    if(cn!==null&&CL.length>cn)add('הוגדרו יותר רכיבים ממספר רכיבי הקשירות','בדיקה','defined components ≤ c',`${V(CL.length)} ≤ ${V(cn)}`)}
  tp='נתונים בטווח';
  for(const k in SYM){const iv=ex(g,k).num===null?interval(g,k):null;if(iv)add(DEF[k]+(rgOf(g,k)?'':' (מהפעולה)'),'נתון',`min ≤ ${SYM[k]} ≤ max`,rngTxt(iv[0],SYM[k]+s,iv[1]))}
  for(const S of O.filter(o=>o.t==='s'&&o.in===X&&rgOf(o,'k')))add(`מספר הצמתים בקבוצה ${S.name}`,'נתון',`min ≤ |${S.name}| ≤ max`,rngTxt(rgOf(S,'k')[0],`|${S.name}|`,rgOf(S,'k')[1]));
  tp='דרגות';
  const av=allV(g),aLo=av?dLo(av):null,aHi=av?dHi(av):null;
  add('סכום הדרגות','טענה 1.3','Σ deg(u) = 2m',`${ad!==null?V(ad)+'·'+n:'Σ deg(u)'} = 2·${m}`);
  if(av&&ad===null){add('סכום הדרגות כשכל הדרגות בטווח','טענה 1.3','n·min deg ≤ 2m ≤ n·max deg',`${aLo!==null?n+'·'+V(aLo)+' ≤ ':''}2·${m}${aHi!==null?' ≤ '+n+'·'+V(aHi):''}`);
    add('כל הדרגות בטווח','מההגדרה','min deg ≤ δ ≤ Δ ≤ max deg',rngTxt(aLo,`${dl} ≤ ${D}`,aHi))}
  add('דרגה מינימלית, ממוצעת ומקסימלית','מההגדרה','δ ≤ 2m / n ≤ Δ',`${dl} ≤ 2·${m} / ${n} ≤ ${D}`);
  add('דרגה מקסימלית בגרף פשוט','מההגדרה','Δ ≤ n − 1',`${D} ≤ ${n} − 1`,null,['גרף פשוט']);
  for(const v of O.filter(o=>o.t==='v'&&o.in===X&&o.q==='one'&&o.w)){const mx=v.w==='max',E=mx?D:dl,S0=mx?'Δ':'δ';
    add(`${v.name} בעל הדרגה ${mx?'הגבוהה':'הנמוכה'} ביותר`,'מההגדרה',`deg(${v.name}) = ${S0}`,`deg(${v.name}) = ${E}`);
    if(dEx(v)===null&&(dLo(v)!==null||dHi(v)!==null))add(`טווח הדרגה של ${v.name}`,'נתון',`min ≤ ${S0} ≤ max`,rngTxt(dLo(v),S0+s,dHi(v)))}
  for(const v of O.filter(o=>o.t==='v'&&o.in===X&&o.q!=='all'&&!(o.q==='one'&&o.w))){add(v.q==='ex'?'קיים צומת בדרגה נתונה':`הדרגה של ${v.name}`,'מההגדרה',`δ ≤ deg(${v.name}) ≤ Δ`,dEx(v)!==null||(dLo(v)===null&&dHi(v)===null)?`${dl} ≤ ${degOf(v)} ≤ ${D}`:[dHi(v)!==null?`${dl} ≤ ${V(dHi(v))}`:'',dLo(v)!==null?`${V(dLo(v))} ≤ ${D}`:''].filter(Boolean).join(',   '));
    if(dEx(v)===null&&(dLo(v)!==null||dHi(v)!==null))add(`טווח הדרגה של ${v.name}`,'נתון',`min ≤ deg(${v.name}) ≤ max`,rngTxt(dLo(v),`deg(${v.name})`,dHi(v)))}
  add('מספר הצמתים מדרגה אי-זוגית הוא זוגי','מסקנה מ־1.3','#{u : deg(u) odd} is even',ad!==null&&ad%2?`${V(ad)} odd ⇒ ${n} even`:'');
  add('יש שני צמתים מאותה דרגה (שני צמתים לפחות)','מסקנה','deg(u) = deg(w) for some u ≠ w','',null,['גרף פשוט',['n',2]]);
  add('דרגה מינימלית גדולה מבטיחה קשירות','מסקנה','δ ≥ (n − 1) / 2 ⇒ connected',`${dl} ≥ (${n} − 1) / 2`);
  add('מסלול ומעגל ארוכים לפי הדרגה המינימלית','פרק 1, שאלה 3','simple path of length ≥ δ,  simple cycle on ≥ δ + 1 vertices (δ ≥ 2)',`path ≥ ${dl},  cycle ≥ ${dl} + 1`);
  /* edges, components, trees */
  tp='קשתות, קשירות ועצים';
  add('מספר הקשתות המרבי בגרף פשוט','מההגדרה','m ≤ n(n − 1) / 2',`${m} ≤ ${n}·(${n} − 1) / 2`,null,['גרף פשוט']);
  add('מספר הקשתות המזערי לפי רכיבי הקשירות','פרק 2','m ≥ n − c',`${m} ≥ ${n} − ${c}`);
  add('עץ: מספר הקשתות','משפט 2.5','m = n − 1',`${sy(g,'m')} = ${n} − 1`,[['tr','y']]);
  add('עץ עם שני צמתים לפחות: יש עלה','טענה 2.3','δ = 1',`${dl} = ${V(1)}`,[['tr','y']],[['n',2]]);
  add('מספר העצים המתויגים על אותם צמתים','משפט 2.9 (קיילי)','nⁿ⁻²',`${n} ^ (${n} − 2)`,[['tr','y']]);
  add('יער: מספר הקשתות','מסקנה מ־2.5','m = n − c',`${sy(g,'m')} = ${n} − ${c}`,[['fo','y']]);
  add('עץ: שני עלים לפחות, ולפחות כדרגה המקסימלית','מסקנה מ־2.3','ℓ ≥ 2,  ℓ ≥ Δ',`${q('lv')} ≥ ${V(2)},  ${q('lv')} ≥ ${D}`,[['tr','y']],[['n',2]]);
  add('עץ: מספר העלים לפי הדרגות','מסקנה מ־1.3 ומ־2.5','ℓ = 2 + Σ (deg(u) − 2), deg(u) ≥ 3',q('lv').includes('class=')?`${q('lv')} = 2 + Σ (deg(u) − 2), deg(u) ≥ 3`:'',[['tr','y']]);
  add('סדרת פרופר: מספר ההופעות של צומת','פרק 2','appearances of u = deg(u) − 1','',[['tr','y']]);
  add('קשיר, ומספר הקשתות כמספר הצמתים: מעגל יחיד','מסקנה מ־2.5','connected, m = n ⇒ exactly one cycle',`${m} = ${n}`,[['conn','y']]);
  add('הרבה קשתות מבטיחות קשירות','מסקנה','m > (n − 1)(n − 2) / 2 ⇒ connected',`${m} > (${n} − 1)·(${n} − 2) / 2`);
  add('הגרף או המשלים שלו קשיר','מסקנה',`${X} or its complement is connected`,'');
  /* bipartite */
  tp='דו-צדדי';
  add('דו-צדדי: אין מעגל באורך אי-זוגי','משפט 1.6','no odd cycle','',[['bp','y']]);
  add('דו-צדדי: שני צבעים מספיקים','משפט 1.6','χ ≤ 2',`${q('chi')} ≤ ${V(2)}`,[['bp','y']]);
  add('דו-צדדי: חסם על מספר הקשתות','מסקנה','m ≤ n² / 4',`${m} ≤ ${n}² / 4`,[['bp','y']]);
  add('דו-צדדי: סכום הדרגות בכל צד','מההגדרה','Σ deg(a), a ∈ A  =  Σ deg(b), b ∈ B  =  m',`Σ deg(a) = Σ deg(b) = ${m}`,[['bp','y']]);
  if(ad!==null&&ad>=1)add('דו-צדדי רגולרי: צדדים שווים וזיווג מושלם','מסקנה מ־4.7','k-regular, k ≥ 1 ⇒ |A| = |B| = n / 2,  ν = n / 2',`|A| = |B| = ${n} / 2,  ${q('nu')} = ${n} / 2`,[['bp','y']]);
  /* Euler, Hamilton */
  tp='אוילר והמילטון';
  add('מסלול אוילר שאינו מעגל','פרק 3','Euler path ⇔ exactly 2 vertices of odd degree','',[['conn','y']]);
  add('אוילרי, אם ורק אם כל הדרגות זוגיות','משפט 3.1','Eulerian ⇔ deg(u) even for all u',ad!==null?`Eulerian ⇔ ${V(ad)} even`:'',[['conn','y']]);
  add('אוילרי: קשיר, וכל הדרגות זוגיות','משפט 3.1','c = 1,  deg(u) even for all u',`${c} = ${V(1)}`,[['eu','y']]);
  add('אוילרי: הקשתות מתפרקות למעגלים','מסקנה מ־3.1','δ ≥ 2,  m ≥ n',`${dl} ≥ ${V(2)},  ${m} ≥ ${n}`,[['eu','y']]);
  add('המילטוני: קשיר, וכל דרגה שתיים לפחות','מההגדרה','c = 1,  δ ≥ 2,  m ≥ n',`${c} = ${V(1)},  ${dl} ≥ ${V(2)},  ${m} ≥ ${n}`,[['ha','y']]);
  add('המילטוני: זיווג וקבוצה בלתי תלויה מתוך המעגל','מסקנה','ν = ⌊n / 2⌋,  α ≤ n / 2',`${q('nu')} = ⌊${n} / 2⌋,  ${q('al')} ≤ ${n} / 2`,[['ha','y']]);
  add('המילטוני: הסרת קבוצת צמתים S','מסקנה','c(G − S) ≤ |S|','',[['ha','y']]);
  add('זיווג מושלם','מההגדרה','ν = n / 2,  n even,  δ ≥ 1',`${q('nu')} = ${n} / 2`,[['pm','y']]);
  add('תנאי אור, לכל שני צמתים לא שכנים','משפט 3.2','deg(u) + deg(w) ≥ n ⇒ Hamiltonian',`${ad!==null?V(ad)+' + '+V(ad):'deg(u) + deg(w)'} ≥ ${n}`);
  add('תנאי דירק להמילטוניות','משפט 3.3','δ ≥ n / 2 ⇒ Hamiltonian',`${dl} ≥ ${n} / 2`);
  /* matchings and covers */
  tp='זיווגים וכיסויים';
  add('משפט ברג׳: זיווג מקסימום ומסלול שיפור','משפט 4.6','M is maximum ⇔ no augmenting path','');
  add('זיווג מכסה שני צמתים לכל קשת','מההגדרה','ν ≤ n / 2',`${q('nu')} ≤ ${n} / 2`);
  add('כיסוי בקשתות וזיווג (בלי צמתים מבודדים)','משפט 4.10','ρ = n − ν',`${q('rho')} = ${n} − ${q('nu')}`,null,[['dl',1]]);
  add('קבוצה בלתי תלויה וכיסוי בצמתים','טענה 4.14','α + β = n',`${q('al')} + ${q('be')} = ${n}`);
  add('כיסוי בצמתים מול זיווג','טענה 4.15','β ≥ ν',`${q('be')} ≥ ${q('nu')}`);
  add('דו-צדדי: כיסוי בצמתים שווה לזיווג','משפט 4.16 (קניג)','β = ν',`${q('be')} = ${q('nu')}`,[['bp','y']]);
  for(const S of O.filter(o=>o.t==='s'&&o.in===X&&o.prop)){const k=S.k!==null?V(S.k):`|${S.name}|`,A=S.name;
    if(S.prop==='indep')add('קבוצה בלתי תלויה נתונה','מההגדרה',`α ≥ |${A}|`,`${q('al')} ≥ ${k}`);
    if(S.prop==='clique')add('קליקה נתונה','מההגדרה',`χ ≥ ω ≥ |${A}|`,`${q('chi')} ≥ ω${s} ≥ ${k}`);
    if(S.prop==='cover')add('כיסוי בצמתים נתון','מההגדרה',`β ≤ |${A}|`,`${q('be')} ≤ ${k}`);
    if(S.prop==='side'){add(`כל קשת נוגעת בצומת אחד של ${A}`,'מההגדרה',`Σ deg(u) = m, u ∈ ${A}`,`Σ deg(u) = ${m}, u ∈ ${A}`,[['bp','y']]);
      add(`תנאי הול לזיווג שמכסה את ${A}`,'משפט 4.7 (הול)',`|Γ(X)| ≥ |X| for all X ⊆ ${A}  ⇔  ν = |${A}|`,`|Γ(X)| ≥ |X| for all X ⊆ ${A}  ⇔  ${q('nu')} = ${k}`,[['bp','y']]);
      add('זיווג מושלם בגרף דו-צדדי','מסקנה 4.8',`perfect matching ⇔ |${A}| = n − |${A}| and Hall`,`${k} = ${n} − ${k}`,[['bp','y']])}}
  add('כיסוי בצמתים לכל היותר פעמיים הזיווג','מסקנה','β ≤ 2ν',`${q('be')} ≤ 2·${q('nu')}`);
  add('קבוצה בלתי תלויה לפי הדרגה המקסימלית','מסקנה','α ≥ n / (Δ + 1)',`${q('al')} ≥ ${n} / (${D} + 1)`);
  /* planarity */
  tp='מישוריות';
  add('נוסחת אוילר','משפט 5.3','f = m − n + 2',`${q('f')} = ${m} − ${n} + 2`,[['pl','y'],['conn','y']]);
  add('נוסחת אוילר לגרף מישורי כלשהו','הכללה של 5.3','f = m − n + c + 1',`${q('f')} = ${m} − ${n} + ${c} + 1`,[['pl','y']]);
  add('חסם הקשתות בגרף מישורי (שלושה צמתים לפחות)','מסקנה 5.4','m ≤ 3n − 6',`${m} ≤ 3·${n} − 6`,[['pl','y']],[['n',3]]);
  add('כל פאה תחומה בשלוש קשתות לפחות','פרק 5','3f ≤ 2m',`3·${q('f')} ≤ 2·${m}`,[['pl','y']]);
  add('סכום אורכי הפאות','פרק 5','Σ len(face) = 2m',`Σ len(face) = 2·${m}`,[['pl','y']]);
  add('בגרף מישורי יש צומת מדרגה קטנה','מסקנה 5.5','δ ≤ 5',`${dl} ≤ ${V(5)}`,[['pl','y']]);
  add('משפט ארבעת הצבעים','משפט 6.3','χ ≤ 4',`${q('chi')} ≤ ${V(4)}`,[['pl','y']]);
  add('לא מישורי: מכיל העדנה של K₅ או של K₃,₃','משפט 5.8 (קורטובסקי)','contains a subdivision of K₅ or K₃,₃','',[['pl','n']]);
  add('לא מישורי: גדלים מזעריים','משפט 5.8','n ≥ 5,  m ≥ 9',`${n} ≥ 5,  ${m} ≥ 9`,[['pl','n']]);
  add('מישורי בלי משולשים (שלושה צמתים לפחות)','מסקנה מ־5.3','m ≤ 2n − 4',`${m} ≤ 2·${n} − 4`,[['pl','y'],['tf','y']],[['n',3]]);
  add('משפט חמשת הצבעים','משפט 6.4','χ ≤ 5',`${q('chi')} ≤ ${V(5)}`,[['pl','y']]);
  /* colouring */
  tp='צביעה ומשלים';
  add('חסם על מספר הצביעה','פרק 6, שאלה 1','χ ≤ Δ + 1',`${q('chi')} ≤ ${D} + 1`);
  add('משפט ברוקס (פרט לרכיב שהוא גרף מלא או מעגל אי-זוגי)','משפט 6.2','χ ≤ Δ',`${q('chi')} ≤ ${D}`);
  add('כל צבע הוא קבוצה בלתי תלויה','מההגדרה','n ≤ χ·α',`${n} ≤ ${q('chi')}·${q('al')}`);
  add('מספר הצביעה לפחות הקליקה המקסימלית','מההגדרה','χ ≥ ω',`${q('chi')} ≥ ${q('om')}`);
  add('צביעה של הגרף ושל המשלים','מסקנה',`χ·${cb} ≥ n`,`${q('chi')}·${cb} ≥ ${n}`);
  add('איזומורפי למשלים','מסקנה','n mod 4 ∈ {0, 1},  m = n(n − 1) / 4',`${m} = ${n}·(${n} − 1) / 4`,[['sc','y']]);
  /* status of each formula: applies, hidden (a needed property is given as the opposite), or conditional (unknown) */
  const st=f=>{if(!f.need)return 'on';let u=false;for(const [k,w] of f.need){const p=prop(g,k);if(p==='u')u=true;else if(p!==w)return 'hide'}return u?'hide':'on'};
  const cond=f=>f.need.filter(([k])=>prop(g,k)==='u').map(([k,w])=>(w==='n'?'לא ':'')+PROPS[k]).join(' ו');
  /* a condition of a formula, with the known value substituted: holds, fails, or cannot be decided from the data */
  const chk=c=>{if(typeof c==='string')return `<span class="qc0">${c}</span>`;const [k,v]=c,b=bounds(g,k)||[null,null],e=ex(g,k).num,r=b[0]!==null&&b[0]>=v?'y':b[1]!==null&&b[1]<v?'n':'u';
    return `<span class="qc0 ${r}" title="${r==='y'?'התנאי מתקיים':r==='n'?'התנאי לא מתקיים':'לא ידוע אם התנאי מתקיים'}"><span class="fx">${mk(SYM[k],g)||SYM[k]} ≥ ${v}</span>${e!==null?`<span class="fx qsub">${V(e)} ≥ ${v}</span>`:r!=='u'?`<span class="fx qsub">${b[0]!==null?V(b[0])+' ≤ ':''}${SYM[k]+s}${b[1]!==null?' ≤ '+V(b[1]):''}</span>`:''}<b>${r==='y'?'✓':r==='n'?'✗':'?'}</b></span>`};
  const bad0=f=>f.cs&&f.cs.some(c=>typeof c!=='string'&&(b=>b&&b[1]!==null&&b[1]<c[1])(bounds(g,c[0])));
  const card=f=>{const sb=f.s&&/class="q[vs]"/.test(f.s)?f.s:'';return `<div class="qi${f.rel?' rel':''}${bad0(f)?' off':''}"><div class="qn">${f.t} <span class="ref">${f.r}</span></div><div class="qf"><span class="fx gen">${f.g}</span>${sb?`<span class="fx qsub">${sb}</span>`:''}</div>${f.cs?`<div class="qc"><span class="qcl">בתנאי</span>${f.cs.map(chk).join('')}</div>`:''}</div>`};
  const title=titleOf(g);
  const vis=F.filter(f=>st(f)!=='hide');
  const tps=[...new Set(vis.map(f=>f.tp))];
  const bad=issues(g);
  const shut=COLG.has(X);
  return `<section class="qt"><h3 class="qcap"><button class="qmin" data-min="${X}" aria-expanded="${!shut}" title="${shut?'הצג את כל הסעיפים':'מזער את כל הסעיפים'}">${shut?'◂':'▾'}</button><span class="name">${X}</span> ${title}${shut?` <span class="lab">${vis.length} נוסחאות מוסתרות</span>`:''}</h3>${shut?'':(bad.length?`<div class="qwarn" role="alert"><b>הנתונים של ${X} לא מתיישבים:</b><ul>${bad.map(x=>`<li>${x}</li>`).join('')}</ul></div>`:'')+tps.map(t=>{const rows=vis.filter(f=>f.tp===t),open=!COL.has(t);return `<div class="qtp"><button data-tp="${t}" aria-expanded="${open}">${open?'▾':'◂'} ${t} <span class="lab">${rows.length}</span></button>${open?`<div class="qitems">${rows.map(card).join('')}</div>`:''}</div>`}).join('')}</section>`}
/* the digest: every formula of the sheet is used as a constraint on the ranges of the quantities, again and again until nothing
   tightens any more. Each bound remembers the formula that gave it. */
const D0={n:1,m:0,c:1,D:0,dl:0,f:1,chi:1,al:1,nu:0,be:0,rho:0,om:1,lv:0};
function digest(g,memo){
  let St=memo.get(g);const fresh=!St;if(fresh){St={B:{},W:{},U:{},N:[],bad:false};memo.set(g,St)}
  const B=St.B,W=St.W,U=St.U,X=g.name;let ch=true,bad=St.bad,moved=false;if(bad)return false;
  if(fresh)for(const k in SYM){B[k]=[D0[k],Infinity];W[k]=[null,null];U[k]=[[],[]];const b=bounds(g,k),own=val(g,k)!==null||rgOf(g,k),r=own?'נתון':g.op?'מהפעולה':forestish(g)&&k==='m'?'עץ או יער: m = n − c':'מהנתונים';
    if(b){if(b[0]!==null&&b[0]>B[k][0]){B[k][0]=b[0];W[k][0]=r}if(b[1]!==null){B[k][1]=b[1];W[k][1]=r}}}
  /* every bound that a rule reads is noted, so that each conclusion can say what it was made of */
  const rd=[],stk=[],K=()=>{stk.push(rd.slice())},E=()=>{stk.pop()},note=(name,Wx,k,i,v)=>{if(Wx[k][i])rd.push({g:name,k,i,v,r:Wx[k][i]})},Z=()=>{rd.length=0};
  const take=()=>{const seen=new Set(),u=[...stk.flat(),...rd].filter(x=>{const q=x.g+'|'+x.k+x.i;if(seen.has(q))return false;seen.add(q);return true});rd.length=0;return u};
  const L=k=>{note(X,W,k,0,B[k][0]);return B[k][0]},H=k=>{note(X,W,k,1,B[k][1]);return B[k][1]};
  const put=(k,i,v,r,u)=>{B[k][i]=v;W[k][i]=r;U[k][i]=u.filter(x=>!(x.g===X&&x.k===k&&x.i===i));ch=moved=true};
  const ge=(k,v,r,u0)=>{const u=u0||take();if(Number.isFinite(v)&&v>B[k][0])put(k,0,v,r,u)},le=(k,v,r,u0)=>{const u=u0||take();if(Number.isFinite(v)&&v<B[k][1])put(k,1,v,r,u)};
  const eq=(k,v,r)=>{const u=take();ge(k,v,r,u);le(k,v,r,u)},up=Math.ceil,dn=Math.floor;
  /* a = b + c, as a constraint on all three */
  const sum=(a,b,c,r)=>{ge(a,L(b)+L(c),r);le(a,H(b)+H(c),r);ge(b,L(a)-H(c),r);le(b,H(a)-L(c),r);ge(c,L(a)-H(b),r);le(c,H(a)-L(b),r)};
  /* what the operation carries over from everything already concluded about the source graph */
  const src=g.op?by(g.src):null,S=src?memo.get(src):null;
  Z();if(S&&!S.bad){K();const sl=k=>{note(src.name,S.W,k,0,S.B[k][0]);return S.B[k][0]},sh=k=>{note(src.name,S.W,k,1,S.B[k][1]);return S.B[k][1]},op=g.op,a=by(g.arg),r=`מ־${src.name}`,sub1=SUBG.includes(op);
    const same=(k,c)=>{ge(k,sl(k)+c,r);le(k,sh(k)+c,r)};
    Z();if(sub1){K();for(const k of ['n','m','D','chi','om','nu'])le(k,sh(k),r);Z();if(op!=='span'&&op!=='dele')le('al',sh('al'),r);E();}
    Z();if(op==='delv'){K();same('n',-1);ge('chi',sl('chi')-1,r);ge('al',sl('al')-1,r);ge('nu',sl('nu')-1,r);ge('dl',sl('dl')-1,r);ge('om',sl('om')-1,r);ge('m',sl('m')-(dHi(a)??sh('D')),r);le('m',sh('m')-(dLo(a)??sl('dl')),r);le('c',sh('c')+(dHi(a)??sh('D'))-1,r);E();}
    Z();if(op==='dele'){K();same('n',0);same('m',-1);ge('chi',sl('chi')-1,r);ge('nu',sl('nu')-1,r);ge('dl',sl('dl')-1,r);le('dl',sh('dl'),r);ge('D',sl('D')-1,r);ge('al',sl('al'),r);le('al',sh('al')+1,r);ge('c',sl('c'),r);le('c',sh('c')+1,r);ge('om',sl('om')-1,r);E();}
    Z();if(op==='adde'){K();same('n',0);same('m',1);ge('chi',sl('chi'),r);le('chi',sh('chi')+1,r);ge('D',sl('D'),r);le('D',sh('D')+1,r);ge('dl',sl('dl'),r);le('dl',sh('dl')+1,r);ge('nu',sl('nu'),r);le('nu',sh('nu')+1,r);le('al',sh('al'),r);ge('al',sl('al')-1,r);le('c',sh('c'),r);ge('c',sl('c')-1,r);ge('om',sl('om'),r);E();}
    Z();if(op==='join'){K();const two=sl('c')>=2,w=`חיבור הרכיבים של ${src.name}`;same('n',0);ge('m',sl('m')+sl('c')-1,w);le('m',sh('m')+sh('c')-1,w);
      ge('chi',sl('chi'),w);le('chi',Math.max(sh('chi'),2),w);ge('om',sl('om'),w);le('om',Math.max(sh('om'),2),w);Z();if(two){ge('chi',2,w);ge('om',2,w);ge('dl',1,w)}
      ge('dl',sl('dl'),w);le('dl',sh('dl')+sh('c')-1,w);ge('D',sl('D'),w);le('D',sh('D')+sh('c')-1,w);ge('nu',sl('nu'),w);le('nu',sh('nu')+sh('c')-1,w);le('al',sh('al'),w);ge('al',sl('al')-(sh('c')-1),w);E();}
    Z();if(op==='span'){K();same('n',0);ge('al',sl('al'),r);ge('c',sl('c'),r);le('dl',sh('dl'),r);E();}
    Z();if(op==='comp'){K();ge('dl',sl('dl'),r);Z();if(S.B.c[0]===1&&S.B.c[1]===1)for(const k in SYM){ge(k,sl(k),r);le(k,sh(k),r)};E();}
    Z();if(op==='ind'||op==='delS'){K();const b=ownB(a,'k')||[null,null];Z();if(op==='delS'){K();Z();if(b[1]!==null)ge('n',sl('n')-b[1],r);Z();if(b[0]!==null)le('n',sh('n')-b[0],r);Z();if(b[1]!==null){K();ge('chi',sl('chi')-b[1],r);ge('nu',sl('nu')-b[1],r);ge('dl',sl('dl')-b[1],r);E();};E();};E();}
    /* removing a set whose inner structure is known: a clique (all adjacent) or an independent set (none adjacent) */
    Z();if(op==='delS'&&a){const b=ownB(a,'k')||[null,null],k0=b[0],k1=b[1],c2=x=>x*(x-1)/2,cq=a.prop==='clique',ind=a.prop==='indep',w=cq?`הסרת הקליקה ${a.name}`:ind?`הסרת הקבוצה הבלתי תלויה ${a.name}`:`הסרת הקבוצה ${a.name}`;
      Z();if(k1!==null){ge('om',sl('om')-(ind?1:k1),w);ge('al',sl('al')-(cq?1:k1),w);ge('m',sl('m')-k1*sh('D')+(cq&&k0!==null?c2(k0):0),w)}
      Z();if(ind)ge('chi',sl('chi')-1,w);
      Z();if(k0!==null&&k1!==null)le('m',sh('m')-k0*sl('dl')+(ind?0:c2(k1)),w);
      Z();if(cq&&k0===2&&k1===2&&prop(src,'tf')==='y')ge('m',sl('m')-(sh('n')-1),'שני שכנים בגרף בלי משולשים: אין להם שכן משותף')}
    /* what the source graph's own nature says about the result */
    Z();if(op==='dele'&&prop(src,'fo')==='y')same('c',1);
    Z();if(op==='dele'&&src.eu==='y'){ge('c',1,'בגרף אוילרי אין גשר: כל קשת על מעגל');le('c',1,'בגרף אוילרי אין גשר: כל קשת על מעגל')}
    Z();if(src.ha==='y'){Z();if(op==='delv'||op==='dele')eq('c',1,'בגרף המילטוני: מה שנשאר מהמעגל מחבר את כל הצמתים');
      Z();if(op==='delS'&&a){const b=ownB(a,'k');Z();if(b&&b[1]!==null)le('c',b[1],'בגרף המילטוני: הסרת קבוצה מפרקת את המעגל לכל היותר למספר חלקים כגודלה')}}
    Z();if(op==='delv'&&a&&a.cut)ge('c',sl('c')+1,`${a.name} צומת מפריד`);
    Z();if(op==='delv'&&prop(src,'tr')==='y'&&a&&dEx(a)!==null)eq('c',dEx(a),'הסרת צומת מעץ: רכיב לכל שכן');
    Z();if(op==='subd'){K();same('n',1);same('m',1);same('c',0);ge('D',sl('D'),r);le('D',Math.max(2,sh('D')),r);le('dl',Math.min(2,sh('dl')),r);E();}
    Z();if(op==='contr'){K();same('n',-1);same('c',0);le('m',sh('m')-1,r);le('chi',sh('chi')+1,r);E();}
    Z();if(op==='compl'){K();same('n',0);ge('m',sl('n')*(sl('n')-1)/2-sh('m'),r);Z();if(sh('n')<Infinity)le('m',sh('n')*(sh('n')-1)/2-sl('m'),r);ge('D',sl('n')-1-sh('dl'),r);le('D',sh('n')-1-sl('dl'),r);ge('dl',sl('n')-1-sh('D'),r);le('dl',sh('n')-1-sl('D'),r);
      ge('om',sl('al'),r);le('om',sh('al'),r);ge('al',sl('om'),r);le('al',sh('om'),r);Z();if(sh('chi')<Infinity)ge('chi',up(sl('n')/sh('chi')),'χ·χ(complement) ≥ n');Z();if(sl('c')>=2)eq('c',1,'המשלים של גרף לא קשיר הוא קשיר');E();};E();}
  /* a component among the components of its graph: what the others take is not available to it */
  Z();if(S&&!S.bad&&g.op==='comp'){K();const sib=compsOf(src).filter(x=>x!==g).map(x=>memo.get(x)).filter(x=>x&&!x.bad),all=compsOf(src).length,cs=S.B.c,full=cs[0]===cs[1]&&cs[0]===all,hid=Math.max(0,cs[0]-all),r=`שאר הרכיבים של ${src.name}`;
    Z();if(sib.length===all-1)for(const k of ['n','m','al','nu','be']){const lo=sib.reduce((t,x)=>t+x.B[k][0],0)+(k==='n'||k==='al'?hid:0),hi=sib.reduce((t,x)=>t+x.B[k][1],0);le(k,S.B[k][1]-lo,r);Z();if(full)ge(k,S.B[k][0]-hi,r)};E();}
  const P0=k=>prop(g,k);
  /* back from the graphs made of this one: what is known about them limits this graph too */
  for(const h of O.filter(o=>o.t==='g'&&o.op&&o.src===X)){const C=memo.get(h);Z();if(!C||C.bad)continue;const cl=k=>{note(h.name,C.W,k,0,C.B[k][0]);return C.B[k][0]},chh=k=>{note(h.name,C.W,k,1,C.B[k][1]);return C.B[k][1]},op=h.op,a=by(h.arg),r=`מ־${h.name}`,back=(k,c)=>{ge(k,cl(k)+c,r);le(k,chh(k)+c,r)};
    Z();if(SUBG.includes(op)){K();for(const k of ['n','m','D','chi','om','nu'])ge(k,cl(k),r);Z();if(op!=='span'&&op!=='dele')ge('al',cl('al'),r);E();}
    Z();if(op==='delv'){K();back('n',1);le('chi',chh('chi')+1,r);le('al',chh('al')+1,r);le('nu',chh('nu')+1,r);le('om',chh('om')+1,r);le('c',chh('c')+1,r);ge('m',cl('m')+(dLo(a)??0),r);le('m',chh('m')+(dHi(a)??chh('n')),r);le('dl',chh('dl')+1,r);E();}
    Z();if(op==='dele'){K();back('n',0);back('m',1);le('chi',chh('chi')+1,r);le('nu',chh('nu')+1,r);le('om',chh('om')+1,r);Z();if(a&&a.bridge)back('c',-1);else{ge('c',cl('c')-1,r);le('c',chh('c'),r)}le('D',chh('D')+1,r);ge('dl',cl('dl'),r);le('dl',chh('dl')+1,r);ge('al',cl('al')-1,r);le('al',chh('al'),r);E();}
    Z();if(op==='adde'){K();back('n',0);back('m',-1);ge('chi',cl('chi')-1,r);le('chi',chh('chi'),r);ge('D',cl('D')-1,r);le('D',chh('D'),r);ge('dl',cl('dl')-1,r);le('dl',chh('dl'),r);ge('nu',cl('nu')-1,r);le('nu',chh('nu'),r);ge('al',cl('al'),r);le('al',chh('al')+1,r);ge('c',cl('c'),r);le('c',chh('c')+1,r);le('om',chh('om'),r);E();}
    Z();if(op==='join'){K();const w=`פירוק החיבור ${h.name}`;back('n',0);ge('m',cl('m')-(H('c')-1),w);le('m',chh('m')-(L('c')-1),w);ge('c',cl('m')-H('m')+1,w);le('c',chh('m')-L('m')+1,w);
      le('chi',chh('chi'),w);Z();if(cl('chi')>=3)ge('chi',cl('chi'),w);le('om',chh('om'),w);Z();if(cl('om')>=3)ge('om',cl('om'),w);
      le('D',chh('D'),w);ge('D',cl('D')-(H('c')-1),w);le('dl',chh('dl'),w);le('nu',chh('nu'),w);ge('nu',cl('nu')-(H('c')-1),w);ge('al',cl('al'),w);le('al',chh('al')+H('c')-1,w);E();}
    Z();if(op==='span'){K();back('n',0);le('al',chh('al'),r);le('c',chh('c'),r);ge('dl',cl('dl'),r);E();}
    Z();if(op==='delS'){K();const b=ownB(a,'k')||[null,null];Z();if(b[0]!==null)ge('n',cl('n')+b[0],r);Z();if(b[1]!==null){K();le('n',chh('n')+b[1],r);le('chi',chh('chi')+b[1],r);le('nu',chh('nu')+b[1],r);E();};E();}
    Z();if(op==='delv'&&a&&a.cut)le('c',chh('c')-1,`${a.name} צומת מפריד`);
    Z();if(op==='delS'&&a){const b=ownB(a,'k')||[null,null],k0=b[0],k1=b[1],c2=x=>x*(x-1)/2,cq=a.prop==='clique',ind=a.prop==='indep',w=cq?`החזרת הקליקה ${a.name} אל ${h.name}`:ind?`החזרת הקבוצה הבלתי תלויה ${a.name} אל ${h.name}`:`החזרת הקבוצה ${a.name} אל ${h.name}`;
      Z();if(k1!==null){le('om',chh('om')+(ind?1:k1),w);le('al',chh('al')+(cq?1:k1),w);le('m',chh('m')+k1*H('D')-(cq&&k0!==null?c2(k0):0),w)}
      Z();if(ind)le('chi',chh('chi')+1,w);
      Z();if(cq&&k0!==null){ge('nu',cl('nu')+dn(k0/2),w);ge('m',cl('m')+c2(k0),w);ge('chi',k0,w)}
      Z();if(k0!==null&&k1!==null)ge('m',cl('m')+k0*L('dl')-(ind?0:c2(k1)),w);
      Z();if(cq&&k0===2&&k1===2&&P0('tf')==='y')le('m',chh('m')+H('n')-1,'שני שכנים בגרף בלי משולשים: אין להם שכן משותף')}
    Z();if(op==='subd'){K();back('n',-1);back('m',-1);back('c',0);E();}
    Z();if(op==='contr'){K();back('n',1);back('c',0);ge('m',cl('m')+1,r);ge('chi',cl('chi')-1,r);E();}
    Z();if(op==='compl'){K();back('n',0);ge('m',cl('n')*(cl('n')-1)/2-chh('m'),r);Z();if(chh('n')<Infinity)le('m',chh('n')*(chh('n')-1)/2-cl('m'),r);ge('D',cl('n')-1-chh('dl'),r);le('D',chh('n')-1-cl('dl'),r);ge('dl',cl('n')-1-chh('D'),r);le('dl',chh('n')-1-cl('D'),r);
      ge('om',cl('al'),r);le('om',chh('al'),r);ge('al',cl('om'),r);le('al',chh('om'),r);Z();if(chh('chi')<Infinity)ge('chi',up(cl('n')/chh('chi')),'χ·χ(complement) ≥ n');Z();if(cl('c')>=2)eq('c',1,'המשלים של גרף לא קשיר הוא קשיר');E();}}
  { const CS=compsOf(g).map(x=>memo.get(x)).filter(x=>x&&!x.bad),all=compsOf(g).length;
    Z();if(all){K();const r='סכום על רכיבי הקשירות',r2='לפי רכיבי הקשירות';ge('c',all,'רכיבי הקשירות שהוגדרו');const full=L('c')===H('c')&&L('c')===all&&CS.length===all,hid=Math.max(0,L('c')-all);
      Z();if(CS.length===all){K();for(const k of ['n','m','al','nu','be']){ge(k,CS.reduce((t,x)=>t+x.B[k][0],0)+(k==='n'||k==='al'?hid:0),r);Z();if(full)le(k,CS.reduce((t,x)=>t+x.B[k][1],0),r)}
        Z();if(!full&&H('c')<Infinity&&H('n')<Infinity){const rest=H('c')-all,R=H('n')-CS.reduce((t,x)=>t+x.B.n[0],0)-(rest-1);Z();if(rest>=1&&R>=1)le('m',CS.reduce((t,x)=>t+x.B.m[1],0)+R*(R-1)/2,'קשתות ברכיבים שהוגדרו, ועוד כל מה שנכנס בצמתים שנותרו')}
        le('dl',Math.min(...CS.map(x=>x.B.dl[1])),r2);ge('D',Math.max(...CS.map(x=>x.B.D[0])),r2);
        Z();if(full){K();for(const k of ['D','chi','om'])le(k,Math.max(...CS.map(x=>x.B[k][1])),r2);ge('dl',Math.min(...CS.map(x=>x.B.dl[0])),r2);E();};E();};E();}}
  /* a property left unknown is also taken from the numbers once they settle it: m = n − c makes a forest */
  const P=k=>{const v=prop(g,k);Z();if(v!=='u')return v;const f=L('m')===H('m')&&L('n')===H('n')&&L('c')===H('c')&&L('m')===L('n')-L('c');
    Z();if(f&&(k==='fo'||k==='pl'||k==='bp'||k==='tf'))return 'y';Z();if(k==='tr'&&f&&L('c')===1)return 'y';Z();if(k==='conn'&&L('c')===1&&H('c')===1)return 'y';if((k==='bp'||k==='tf')&&B.chi[1]<=2)return 'y';return v};
  const ad0=allDeg(g),av=allV(g),vs=O.filter(o=>o.t==='v'&&o.in===X&&o.q!=='all'),ss=O.filter(o=>o.t==='s'&&o.in===X&&o.prop);
  let it=0;
  while(ch&&it++<60){ch=false;
    Z();if(av){K();Z();if(dLo(av)!==null)ge('dl',dLo(av),'כל הדרגות בטווח');Z();if(dHi(av)!==null)le('D',dHi(av),'כל הדרגות בטווח');E();}
    for(const v of vs){const a=dLo(v),b=dHi(v),r=`הדרגה של ${v.name}`;Z();if(v.q==='one'&&v.w==='max'){K();Z();if(a!==null)ge('D',a,r);Z();if(b!==null)le('D',b,r);E();}else if(v.q==='one'&&v.w==='min'){Z();if(a!==null)ge('dl',a,r);Z();if(b!==null)le('dl',b,r)}else{Z();if(a!==null)ge('D',a,r);Z();if(b!==null)le('dl',b,r)}}
    ge('D',L('dl'),'δ ≤ Δ');le('dl',H('D'),'δ ≤ Δ');le('D',H('n')-1,'Δ ≤ n − 1');ge('n',L('D')+1,'Δ ≤ n − 1');
    { const r='סכום הדרגות (1.3)';ge('m',up(L('n')*L('dl')/2),r);Z();if(H('D')<Infinity&&H('n')<Infinity)le('m',dn(H('n')*H('D')/2),r);le('dl',dn(2*H('m')/L('n')),r);Z();if(H('n')<Infinity)ge('D',up(2*L('m')/H('n')),r);Z();if(H('D')<Infinity)ge('n',up(2*L('m')/H('D')),r);Z();if(L('dl')>=1)le('n',dn(2*H('m')/L('dl')),r)}
    { const r='m ≤ n(n − 1) / 2';Z();if(H('n')<Infinity)le('m',H('n')*(H('n')-1)/2,r);let x=1;while(x*(x-1)/2<L('m'))x++;ge('n',x,r)}
    { const r='m ≥ n − c';ge('m',L('n')-H('c'),r);ge('c',L('n')-H('m'),r);le('n',H('m')+H('c'),r)}
    le('c',H('n'),'c ≤ n');ge('n',L('c'),'c ≤ n');
    { const x=H('n')-L('c')+1;Z();if(x<Infinity)le('m',x*(x-1)/2,'m ≤ (n − c + 1)(n − c) / 2')}
    le('c',H('n')-L('nu'),'כל קשת בזיווג מחברת שני צמתים');ge('al',L('c'),'צומת מכל רכיב: קבוצה בלתי תלויה');
    Z();if(H('D')<Infinity&&H('D')>=1){K();ge('be',up(L('m')/H('D')),'צומת מכסה לכל היותר Δ קשתות');ge('nu',up(L('m')/(2*H('D')-1)),'קשת בזיווג חוסמת לכל היותר 2Δ − 1 קשתות');E();}
    le('m',H('be')*H('D'),'צומת מכסה לכל היותר Δ קשתות');
    ge('m',L('om')*(L('om')-1)/2,'קליקה: ω(ω − 1) / 2 קשתות');ge('m',L('chi')*(L('chi')-1)/2,'צביעה ב־χ צבעים דורשת קשת בין כל שני צבעים');
    Z();if(L('c')===1&&H('c')===1){K();Z();if(L('n')>=2)ge('dl',1,'קשיר');Z();if(L('n')>=3)ge('D',2,'קשיר, שלושה צמתים לפחות');E();}
    Z();if(L('dl')>=1)ge('nu',1,'אין צמתים מבודדים');
    Z();if(H('n')<Infinity&&L('n')>=3&&2*L('dl')>=H('n')){K();ge('nu',dn(L('n')/2),'המילטוני (דירק 3.3)');E();}
    Z();if(ad0!==null&&ad0%2===1){K();Z();if(L('n')%2)ge('n',L('n')+1,'דרגות אי-זוגיות: מספר צמתים זוגי');Z();if(H('n')<Infinity&&H('n')%2)le('n',H('n')-1,'דרגות אי-זוגיות: מספר צמתים זוגי');E();}
    Z();if(L('m')>=1){K();le('c',H('n')-1,'יש קשת');ge('D',1,'יש קשת');ge('chi',2,'יש קשת');ge('om',2,'יש קשת');ge('nu',1,'יש קשת');E();}
    Z();if(H('m')===0){K();eq('D',0,'אין קשתות');eq('chi',1,'אין קשתות');eq('nu',0,'אין קשתות');E();}
    Z();if(P('conn')==='y')eq('c',1,'קשיר');
    /* sharpened links found by running whole questions through the solver */
    Z();if(g.sc==='y'){eq('c',1,'גרף או המשלים שלו קשיר, והם איזומורפיים');const r='איזומורפי למשלים: קליקה כאן היא קבוצה בלתי תלויה במשלים',r2='איזומורפי למשלים: Δ + δ = n − 1';ge('om',L('al'),r);le('om',H('al'),r);ge('al',L('om'),r);le('al',H('om'),r);ge('D',L('n')-1-H('dl'),r2);le('D',H('n')-1-L('dl'),r2);ge('dl',L('n')-1-H('D'),r2);le('dl',H('n')-1-L('D'),r2)}
    Z();if(P('bp')==='n'){ge('chi',3,'לא דו-צדדי (1.6)');ge('n',3,'לא דו-צדדי: מעגל אי-זוגי');ge('m',3,'לא דו-צדדי: מעגל אי-זוגי')}
    Z();if(P('pl')==='n'){ge('n',5,'לא מישורי (5.8)');ge('m',9,'לא מישורי (5.8)');ge('D',3,'לא מישורי (5.8)')}
    Z();if(H('al')===1){ge('om',L('n'),'אין שני צמתים לא שכנים: גרף מלא');ge('dl',L('n')-1,'אין שני צמתים לא שכנים: גרף מלא')}
    Z();if(L('n')===H('n')&&L('om')>=L('n'))ge('m',L('n')*(L('n')-1)/2,'גרף מלא');
    Z();if(L('n')===H('n')){const miss=L('n')*(L('n')-1)/2-L('m');ge('dl',L('n')-1-miss,'כל קשת חסרה מורידה דרגה אחת לכל היותר לצומת')}
    le('om',H('n'),'ω ≤ n');le('lv',H('n'),'ℓ ≤ n');
    Z();if(g.eu==='y'){eq('c',1,'אוילרי: קשיר');Z();if(L('n')>=2){ge('dl',2,'אוילרי: כל הדרגות זוגיות, ואין צומת מבודד');ge('m',L('n'),'אוילרי: כל דרגה שתיים לפחות')}}
    Z();if(g.ha==='y'){eq('c',1,'המילטוני: קשיר');ge('n',3,'מעגל המילטון');ge('dl',2,'המילטוני: כל צומת על המעגל');ge('m',L('n'),'המילטוני: קשתות המעגל');ge('nu',dn(L('n')/2),'המילטוני: זיווג מתוך המעגל');Z();if(H('n')<Infinity)le('al',dn(H('n')/2),'המילטוני: לכל היותר כל צומת שני על המעגל');
      Z();if(P('bp')==='y'){Z();if(L('n')%2)ge('n',L('n')+1,'דו-צדדי המילטוני: מעגל באורך זוגי');Z();if(H('n')<Infinity&&H('n')%2)le('n',H('n')-1,'דו-צדדי המילטוני: מעגל באורך זוגי')}}
    Z();if(g.pm==='y'){ge('dl',1,'זיווג מושלם: אין צומת מבודד');Z();if(L('n')%2)ge('n',L('n')+1,'זיווג מושלם: מספר צמתים זוגי');Z();if(H('n')<Infinity&&H('n')%2)le('n',H('n')-1,'זיווג מושלם: מספר צמתים זוגי');ge('nu',up(L('n')/2),'זיווג מושלם');Z();if(H('n')<Infinity)le('nu',dn(H('n')/2),'זיווג מושלם')}
    /* all degrees even, or all odd: known from the data, or carried over from the complement */
    { const ptn=g.op==='compl'?by(g.src):O.find(o=>o.t==='g'&&o.op==='compl'&&o.src===X),ps=ptn&&memo.get(ptn);let par=g.eu==='y'?'e':ad0!==null?(ad0%2?'o':'e'):null,pw=g.eu==='y'?'אוילרי':'כל הדרגות שוות';
      Z();if(!par&&ps&&ps.par&&L('n')===H('n')){par=L('n')%2?ps.par:(ps.par==='e'?'o':'e');pw=`הדרגות ב־${ptn.name} כולן ${ps.par==='e'?'זוגיות':'אי-זוגיות'}, והדרגה כאן היא n − 1 פחות הדרגה שם`}
      Z();if(par!==St.par){St.par=par;St.pw=pw;moved=true}
      Z();if(par){const odd=par==='o'?1:0,r=par==='e'?'כל הדרגות זוגיות':'כל הדרגות אי-זוגיות';
        Z();if(L('dl')%2!==odd)ge('dl',L('dl')+1,r);Z();if(L('D')%2!==odd)ge('D',L('D')+1,r);
        Z();if(H('D')<Infinity&&H('D')%2!==odd)le('D',H('D')-1,r);Z();if(H('dl')<Infinity&&H('dl')%2!==odd)le('dl',H('dl')-1,r);
        Z();if(odd){Z();if(L('n')%2)ge('n',L('n')+1,'דרגות אי-זוגיות: מספר צמתים זוגי');Z();if(H('n')<Infinity&&H('n')%2)le('n',H('n')-1,'דרגות אי-זוגיות: מספר צמתים זוגי')}}}
    Z();if(H('n')<Infinity&&2*L('dl')>=H('n')-1)eq('c',1,'δ ≥ (n − 1) / 2');
    Z();if(H('n')<Infinity&&L('m')>(H('n')-1)*(H('n')-2)/2)eq('c',1,'m > (n − 1)(n − 2) / 2');
    Z();if(P('tr')==='y'){K();const r='עץ (2.5)';eq('c',1,'עץ');ge('m',L('n')-1,r);le('m',H('n')-1,r);ge('n',L('m')+1,r);le('n',H('m')+1,r);
      Z();if(L('n')>=2){K();eq('dl',1,'עלה בעץ (2.3)');eq('chi',2,'עץ הוא דו-צדדי');ge('lv',Math.max(2,L('D')),'בעץ: ℓ ≥ 2, ℓ ≥ Δ');le('D',H('lv'),'בעץ: ℓ ≥ Δ');Z();if(L('n')>=3){K();le('lv',H('n')-1,'בעץ: לא כל הצמתים עלים');le('be',H('n')-L('lv'),'בעץ: הצמתים שאינם עלים מכסים את כל הקשתות');Z();if(H('D')<Infinity&&H('D')>=2&&H('n')<Infinity)le('lv',dn((2+H('n')*(H('D')-2))/(H('D')-1)),'בעץ: סכום הדרגות קובע כמה עלים אפשריים');ge('n',L('lv')+1,'בעץ: לא כל הצמתים עלים');E();}
        Z();if(H('D')<Infinity&&H('D')>=1)ge('nu',up((L('n')-1)/H('D')),'כיסוי בצמתים של עץ: β ≥ m / Δ, קניג');E();};E();}
    Z();if(P('fo')==='y')eq('f',1,'אין מעגלים: פאה אחת');
    Z();if(P('tr')==='y'){E();K();}else if(P('fo')==='y'){sum('n','m','c','יער: m = n − c');le('dl',1,'ביער יש צומת מדרגה קטנה');Z();if(L('m')>=1)ge('lv',2,'רכיב עם קשת ביער הוא עץ: שני עלים');Z();if(L('dl')>=1)ge('lv',2*L('c'),'כל רכיב ביער הוא עץ: שני עלים לרכיב')}
    Z();if(P('pl')==='y'){K();Z();if(L('n')>=3){K();const r='מישורי: m ≤ 3n − 6 (5.4)';le('m',3*H('n')-6,r);ge('n',up((L('m')+6)/3),r);
        Z();if(P('tf')==='y'){K();const r2='מישורי בלי משולשים: m ≤ 2n − 4';le('m',2*H('n')-4,r2);ge('n',up((L('m')+4)/2),r2);E();};E();}
      le('dl',5,'מישורי: δ ≤ 5 (5.5)');le('chi',4,'ארבעת הצבעים (6.3)');
      { const r='נוסחת אוילר (5.3)';ge('f',L('m')-H('n')+L('c')+1,r);le('f',H('m')-L('n')+H('c')+1,r);ge('m',L('f')+L('n')-H('c')-1,r);le('m',H('f')+H('n')-L('c')-1,r);ge('n',L('m')+L('c')+1-H('f'),r);le('n',H('m')+H('c')+1-L('f'),r);ge('c',L('f')-H('m')+L('n')-1,r);le('c',H('f')-L('m')+H('n')-1,r)}
      Z();if(L('n')>=3&&L('m')>=3)le('f',dn(2*H('m')/3),'3f ≤ 2m');E();}
    Z();if(P('bp')==='y'){K();le('chi',2,'דו-צדדי (1.6)');Z();if(H('n')<Infinity)le('m',dn(H('n')*H('n')/4),'דו-צדדי: m ≤ n² / 4');{let x=1;while(dn(x*x/4)<L('m'))x++;ge('n',x,'דו-צדדי: m ≤ n² / 4')}
      const r='קניג (4.16)';ge('be',L('nu'),r);le('be',H('nu'),r);ge('nu',L('be'),r);le('nu',H('be'),r);ge('al',up(L('n')/2),'דו-צדדי: צד אחד הוא בלתי תלוי');E();}
    Z();if(H('n')<Infinity)le('nu',dn(H('n')/2),'ν ≤ n / 2');ge('n',2*L('nu'),'ν ≤ n / 2');
    sum('n','al','be','α + β = n (4.14)');
    ge('be',L('nu'),'β ≥ ν (4.15)');le('nu',H('be'),'β ≥ ν (4.15)');le('be',2*H('nu'),'β ≤ 2ν');ge('nu',up(L('be')/2),'β ≤ 2ν');
    Z();if(L('dl')>=1)sum('n','rho','nu','ρ = n − ν (4.10)');
    Z();if(H('D')<Infinity)ge('al',up(L('n')/(H('D')+1)),'α ≥ n / (Δ + 1)');
    le('chi',H('D')+1,'χ ≤ Δ + 1');ge('D',L('chi')-1,'χ ≤ Δ + 1');
    Z();if(H('al')<Infinity)ge('chi',up(L('n')/H('al')),'n ≤ χ·α');Z();if(H('chi')<Infinity)ge('al',up(L('n')/H('chi')),'n ≤ χ·α');Z();if(H('chi')<Infinity&&H('al')<Infinity)le('n',H('chi')*H('al'),'n ≤ χ·α');
    ge('chi',L('om'),'χ ≥ ω');le('om',H('chi'),'χ ≥ ω');le('chi',H('n'),'χ ≤ n');le('al',H('n'),'α ≤ n');
    Z();if(P('tf')==='y'){le('om',2,'בלי משולשים');Z();if(H('n')<Infinity)le('m',dn(H('n')*H('n')/4),'בלי משולשים: m ≤ n² / 4')}
    for(const S of ss){const b=ownB(S,'k');Z();if(!b)continue;Z();if(S.prop==='indep'&&b[0]!==null)ge('al',b[0],`הקבוצה ${S.name}`);Z();if(S.prop==='clique'&&b[0]!==null)ge('om',b[0],`הקליקה ${S.name}`);Z();if(S.prop==='cover'&&b[1]!==null)le('be',b[1],`הכיסוי ${S.name}`)}
    Z();if(P('sc')==='y'&&L('n')===H('n'))eq('m',L('n')*(L('n')-1)/4,'איזומורפי למשלים');
    for(const k in SYM)if(B[k][0]>B[k][1]){bad=true;ch=false}}
  /* what the ranges say beyond numbers */
  const N=St.N;N.length=0;const T=(t,r)=>N.push([t,r,take()]),ex1=k=>L(k)===H(k),ad=allDeg(g);
  Z();if(!bad){K();
    Z();if(ex1('c')&&L('c')===1&&prop(g,'conn')!=='y')T('הגרף קשיר',W.c[1]||W.c[0]);
    Z();if(prop(g,'tr')==='y'&&g.tr!=='y')T('הגרף הוא עץ',g.op==='comp'?'רכיב קשירות של יער':'יער קשיר');
    Z();if(P('tr')==='y'&&ex1('lv')&&L('lv')===2&&L('n')>=2)T('העץ הוא מסלול','שני עלים בדיוק');Z();if(P('tr')==='y'&&ex1('D')&&ex1('n')&&L('D')===L('n')-1&&L('n')>=3)T('העץ הוא כוכב','Δ = n − 1');
    Z();if(prop(g,'fo')!=='y'&&L('m')>H('n')-L('c'))T('יש בגרף מעגל, ולכן הוא אינו יער','m > n − c');
    Z();if(prop(g,'fo')!=='y'&&ex1('m')&&ex1('n')&&ex1('c')&&L('m')===L('n')-L('c'))T(L('c')===1?'הגרף הוא עץ':'הגרף הוא יער','m = n − c');
    Z();if(ex1('c')&&L('c')===1&&ex1('m')&&ex1('n')&&L('m')===L('n'))T('יש בגרף מעגל אחד בדיוק','קשיר, m = n');
    Z();if(g.ha!=='y'&&L('n')>=3&&H('n')<Infinity&&2*L('dl')>=H('n'))T('הגרף המילטוני','דירק (3.3)');
    Z();if(g.eu!=='y'&&St.par==='e'&&ex1('c')&&L('c')===1&&L('m')>=1)T('הגרף אוילרי',`משפט 3.1: קשיר, ו${St.pw}`);
    Z();if(St.par==='o')T('הגרף אינו אוילרי: כל הדרגות אי-זוגיות',St.pw);
    Z();if(ad!==null&&ad%2===1)T('מספר הצמתים זוגי','מסקנה מ־1.3');
    Z();if(L('dl')>=2)T(`יש מעגל פשוט על ${L('dl')+1} צמתים לפחות`,'פרק 1, שאלה 3');
    Z();if(prop(g,'pl')==='u'&&P('pl')==='u'){K();Z();if(L('n')>=3&&L('m')>3*H('n')-6)T('הגרף אינו מישורי','m > 3n − 6 (5.4)');else if(L('dl')>=6)T('הגרף אינו מישורי','δ ≥ 6 (5.5)');else if(L('chi')>=5)T('הגרף אינו מישורי','χ ≥ 5 (6.3)');E();}
    Z();if(prop(g,'bp')==='u'&&P('bp')==='u'){K();Z();if(H('n')<Infinity&&L('m')>H('n')*H('n')/4)T('הגרף אינו דו-צדדי','m > n² / 4');else if(L('chi')>=3)T('הגרף אינו דו-צדדי','χ ≥ 3 (1.6)');E();}
    Z();if(P('pl')==='y'&&ex1('m')&&ex1('n')&&L('n')>=3){Z();if(L('m')===3*L('n')-6)T('כל הפאות משולשים, ואי אפשר להוסיף קשת בלי לאבד מישוריות','m = 3n − 6 (5.4)');else if(P('tf')==='y'&&L('m')===2*L('n')-4&&P('fo')!=='y')T('כל הפאות מרובעות','m = 2n − 4')}
    Z();if(ex1('om')&&ex1('n')&&L('om')===L('n')&&L('n')>=2)T('הגרף מלא','ω = n');
    Z();if(g.pl==='u'&&prop(g,'pl')==='n')T('הגרף אינו מישורי','מכיל תת-גרף לא מישורי, או נוצר מהעדנה של גרף לא מישורי');
    Z();if(g.bp==='u'&&prop(g,'bp')==='n')T('הגרף אינו דו-צדדי','מכיל תת-גרף לא דו-צדדי');
    Z();if(ex1('nu')&&ex1('n')&&2*L('nu')===L('n'))T('יש זיווג מושלם','ν = n / 2');
    Z();if(ex1('n')&&L('n')%2===1)T('אין זיווג מושלם','מספר צמתים אי-זוגי');E();}
  St.fo=P('fo')==='y';St.pl=P('pl')==='y';St.tf=P('tf')==='y';
  St.bad=bad;return moved||bad}
/* all graphs together: each round lets every graph use what the others have reached, until nothing moves */
function solveAll(extra){const memo=new Map(),x=extra||[];O.push(...x);
  try{let any=true,r=0;while(any&&r++<14){any=false;for(const g of graphs())any=digest(g,memo)||any}}finally{if(x.length)O.splice(O.length-x.length,x.length)}
  return memo}
/* the standard moves, tried on every graph without the user defining them: what is left after removing any vertex, any edge,
   two adjacent or two non-adjacent vertices, after adding an edge, and the complement. Each is a real object for the solver. */
function virtFor(g,d){
  const X=g.name,L=k=>d.B[k][0],H=k=>d.B[k][1],out=[],fin=x=>x===Infinity?null:x;
  const mk=(title,name,op,arg)=>{if(by(name))return;const h=newG(name,{op,src:X,arg:arg?arg.name:null,virt:true});if(arg)arg.virt=true;out.push({title,h,arg})};
  const far=(H('m')<L('n')*(L('n')-1)/2&&L('n')>=2)||L('c')>=2;
  if(L('n')>=2)mk('הסרת צומת כלשהו',`${X}−v`,'delv',{t:'v',name:`v∈${X}`,in:X,q:'one',d:null,dm:'rng',d1:L('dl'),d2:fin(H('D')),cut:false});
  if(L('m')>=1){mk('הסרת קשת כלשהי',`${X}−e`,'dele',{t:'e',name:`e∈${X}`,in:X,bridge:false});
    mk('הסרת שני צמתים שכנים',`${X}−uw`,'delS',{t:'s',name:`שני שכנים ב־${X}`,in:X,k:2,prop:'clique'})}
  if(far&&L('n')>=3){mk('הסרת שני צמתים לא שכנים',`${X}−u,w`,'delS',{t:'s',name:`שני לא שכנים ב־${X}`,in:X,k:2,prop:'indep'});
    mk('הוספת קשת בין שני צמתים לא שכנים',`${X}+e`,'adde',{t:'e',name:`e∉${X}`,in:X,bridge:false})}
  if(L('c')>=2)mk('חיבור הרכיבים במספר קשתות מינימלי',`${X}+F`,'join',null);
  if(!isBar(X)&&!O.some(o=>o.t==='g'&&o.op==='compl'&&o.src===X))mk('המשלים',barName(X),'compl',null);
  return out}
/* bounds on the sum of two degrees: for any pair, for two neighbours and for two non-neighbours. A graph and its complement
   exchange them: neighbours here are non-neighbours there, and each degree is n − 1 minus the degree there. */
function pairBase(g,d,memo){
  const L=k=>d.B[k][0],H=k=>d.B[k][1],CS=compsOf(g).map(x=>memo.get(x)).filter(x=>x&&!x.bad),full=CS.length&&L('c')===H('c')&&CS.length===L('c');
  /* the largest component: all its neighbours stay inside it */
  const rest=L('c')-CS.length,known=CS.length?Math.max(...CS.map(x=>x.B.n[1])):0;
  /* components that were not defined share the vertices the defined ones leave, at least one vertex each */
  const cm=full?known:CS.length&&CS.length===compsOf(g).length&&rest>=1?Math.max(known,H('n')-CS.reduce((t,x)=>t+x.B.n[0],0)-(rest-1)):H('n')-(L('c')-1),lo=2*L('dl'),hi=2*H('D');
  const X=g.name,sb=`<sub>${X}</sub>`,dg=x=>`deg${sb}(${x})`,P={lo,hi,cm,adjLo:lo,nadjLo:lo,adjHi:hi,nadjHi:hi,X};
  /* every explanation is a list of formal lines: [formula, justification] */
  const base=[[`δ${sb} ≤ ${dg('x')} ≤ Δ${sb}  for all x`,'הגדרת הדרגה המינימלית והמקסימלית'],[`δ${sb} ≥ ${L('dl')}${H('D')<Infinity?`,  Δ${sb} ≤ ${H('D')}`:''}`,'מהתמצית']];
  P.eAdjHi=P.eNadjHi=P.eAdjLo=P.eNadjLo=base;
  if(cm<Infinity){const a=d.tf?cm:2*(cm-1);
    if(a<P.adjHi){P.adjHi=a;P.eAdjHi=d.tf?[[`uw ∈ E(${X}),  no triangle in ${X}  ⇒  Γ(u) ∩ Γ(w) = ∅`,'שכן משותף היה סוגר משולש'],[`Γ(u) ∪ Γ(w) ⊆ U,   U the component of u, w`,'שכנים נמצאים באותו רכיב קשירות'],
        [`${dg('u')} + ${dg('w')} = |Γ(u)| + |Γ(w)| = |Γ(u) ∪ Γ(w)| ≤ |U|`,'הקבוצות זרות'],[`|U| ≤ ${cm}`,'הרכיב הגדול ביותר, מהתמצית']]
      :[[`Γ(x) ⊆ U ∖ {x},   U the component of x  ⇒  ${dg('x')} ≤ |U| − 1`,'שכנים נמצאים באותו רכיב קשירות'],[`|U| ≤ ${cm}`,'הרכיב הגדול ביותר, מהתמצית']]}
    const n2=Math.min(2*(H('n')-2),L('c')>=2?2*(cm-1):Infinity);
    if(n2<P.nadjHi&&n2>=0){P.nadjHi=n2;P.eNadjHi=[[`uw ∉ E(${X})  ⇒  Γ(u) ⊆ V ∖ {u, w}  ⇒  ${dg('u')} ≤ n − 2`,'צומת אינו שכן של עצמו ולא של w'],[`Γ(x) ⊆ U ∖ {x}  ⇒  ${dg('x')} ≤ |U| − 1`,'שכנים נמצאים באותו רכיב קשירות'],[`n${sb} ≤ ${H('n')},  |U| ≤ ${cm}`,'מהתמצית']]}}
  return P}
function pairInfo(g,d,memo){
  const P=pairBase(g,d,memo),L=k=>d.B[k][0],H=k=>d.B[k][1],X=g.name;
  const h=g.op==='compl'?by(g.src):O.find(o=>o.t==='g'&&o.op==='compl'&&o.src===g.name),q=h&&memo.get(h);
  if(q&&!q.bad){const Q=pairBase(h,q,memo),nl=2*(L('n')-1),nh=2*(H('n')-1),Y=h.name,dx=x=>`deg<sub>${X}</sub>(${x})`,dy=x=>`deg<sub>${Y}</sub>(${x})`,sx=`${dx('u')} + ${dx('w')}`,sy=`${dy('u')} + ${dy('w')}`;
    const via=(here,there,lines,rel,v,side,nn,res)=>[[`uw ${here} E(${X})  ⇔  uw ${there} E(${Y})`,'הגדרת המשלים'],[`${dx('x')} = n − 1 − ${dy('x')}  for all x`,'הגדרת המשלים'],...lines,[`${sy} ${rel} ${v}`,`מהשורות הקודמות, ב־${Y}`],
      [`${sx} = 2(n − 1) − (${sy}) ${side} 2·(${nn} − 1) − ${v} = ${res}`,'הצבה']];
    if(Q.adjHi<Infinity&&nl-Q.adjHi>P.nadjLo){P.nadjLo=nl-Q.adjHi;P.eNadjLo=via('∉','∈',Q.eAdjHi,'≤',Q.adjHi,'≥',L('n'),P.nadjLo)}
    if(Q.nadjHi<Infinity&&nl-Q.nadjHi>P.adjLo){P.adjLo=nl-Q.nadjHi;P.eAdjLo=via('∈','∉',Q.eNadjHi,'≤',Q.nadjHi,'≥',L('n'),P.adjLo)}
    if(nh<Infinity&&nh-Q.adjLo<P.nadjHi){P.nadjHi=nh-Q.adjLo;P.eNadjHi=via('∉','∈',Q.eAdjLo,'≥',Q.adjLo,'≤',H('n'),P.nadjHi)}
    if(nh<Infinity&&nh-Q.nadjLo<P.adjHi){P.adjHi=nh-Q.nadjLo;P.eAdjHi=via('∈','∉',Q.eNadjLo,'≥',Q.nadjLo,'≤',H('n'),P.adjHi)}}
  /* Ore: every two non-neighbours with degree sum at least n */
  P.ore=L('n')>=3&&H('n')<Infinity&&P.nadjLo>=H('n');
  return P}
/* a derivation: formula on the left, its justification on the right; the last line is the conclusion */
const prf=lines=>`<div class="qpf">${lines.map(([f,j],n)=>`<div class="ps"><div class="pf"><span class="pn">${n+1}.</span><span class="fx">${f}</span></div>${j?`<div class="pj">${j}</div>`:''}</div>`).join('')}</div>`;
function pairRows(g,d,memo){
  const P=pairInfo(g,d,memo),L=k=>d.B[k][0],H=k=>d.B[k][1],s=sub(g),sb=`<sub>${g.name}</sub>`,R=[],dg=`deg${s}(u) + deg${s}(w)`,dgf=`deg${sb}(u) + deg${sb}(w)`,row=(t,f,e)=>R.push({t,f,e});
  const rng=(lo,hi)=>`${lo>0?V(lo)+' ≤ ':''}${dg}${hi<Infinity?' ≤ '+V(hi):''}`;
  const two=(lo,hi,eLo,eHi,who)=>(lo>0?`<p><b>החסם התחתון</b></p>`+prf([...eLo,[`∴  ${dgf} ≥ ${lo}   for all ${who}`,'']]):'')+(hi<Infinity?`<p><b>החסם העליון</b></p>`+prf([...eHi,[`∴  ${dgf} ≤ ${hi}   for all ${who}`,'']]):'');
  if(P.lo>0||P.hi<Infinity)row('סכום הדרגות של שני צמתים כלשהם',rng(P.lo,P.hi),prf([[`δ${sb} ≤ deg${sb}(x) ≤ Δ${sb}  for all x`,'הגדרת הדרגה המינימלית והמקסימלית'],[`2δ${sb} ≤ ${dgf} ≤ 2Δ${sb}`,'חיבור שני אי-שוויונים'],[`∴  ${P.lo} ≤ ${dgf}${P.hi<Infinity?' ≤ '+P.hi:''}`,'הצבה מהתמצית']]));
  if(P.adjLo>0||P.adjHi<Infinity)row('סכום הדרגות של שני שכנים',rng(P.adjLo,P.adjHi),two(P.adjLo,P.adjHi,P.eAdjLo,P.eAdjHi,`uw ∈ E(${g.name})`));
  if(P.nadjLo>0||P.nadjHi<Infinity)row('סכום הדרגות של שני צמתים לא שכנים',rng(P.nadjLo,P.nadjHi),two(P.nadjLo,P.nadjHi,P.eNadjLo,P.eNadjHi,`uw ∉ E(${g.name})`));
  if(H('n')<Infinity){const cn=P.nadjLo-H('n')+2;if(cn>=1)row('שכנים משותפים לשני צמתים לא שכנים',`|Γ(u) ∩ Γ(w)| ≥ ${V(cn)}`,prf([[`uw ∉ E  ⇒  Γ(u) ∪ Γ(w) ⊆ V ∖ {u, w}`,'צומת אינו שכן של עצמו ולא של השני'],[`|Γ(u) ∩ Γ(w)| = |Γ(u)| + |Γ(w)| − |Γ(u) ∪ Γ(w)| ≥ ${dgf} − (n − 2)`,'הכלה והפרדה'],[`${dgf} ≥ ${P.nadjLo},   n ≤ ${H('n')}`,'מהשורה של צמתים לא שכנים'],[`∴  |Γ(u) ∩ Γ(w)| ≥ ${P.nadjLo} − ${H('n')-2} = ${cn}`,'הצבה'],[`∴  dist(u, w) ≤ 2  for all u, w`,'שכן משותף נותן מסלול באורך שתיים']]));
    const ct=P.adjLo-H('n');if(ct>=1)row('שכנים משותפים לשני צמתים שכנים',`|Γ(u) ∩ Γ(w)| ≥ ${V(ct)}`,prf([[`uw ∈ E  ⇒  (Γ(u) ∖ {w}) ∪ (Γ(w) ∖ {u}) ⊆ V ∖ {u, w}`,''],[`|Γ(u) ∩ Γ(w)| ≥ (${dgf} − 2) − (n − 2)`,'הכלה והפרדה'],[`${dgf} ≥ ${P.adjLo},   n ≤ ${H('n')}`,'מהשורה של שני שכנים'],[`∴  |Γ(u) ∩ Γ(w)| ≥ ${P.adjLo} − ${H('n')} = ${ct}`,'הצבה'],[`∴  every edge lies on a triangle`,'']]))}
  return R}

const titleOf=g=>g.op?`${OPS[g.op][0]}${g.arg?' '+g.arg:''} ${g.op==='compl'||g.op==='comp'||g.op==='span'||g.op==='join'?'של':'מתוך'} ${g.src}`:'הגרף הנתון';
/* a reason mixes Hebrew words and formulas: each formula run is set left to right inside the Hebrew line */
const rz=x=>String(x).replace(/[A-Za-zΑ-ωℓ0-9(][^\u0590-\u05FF]*[A-Za-zΑ-ω0-9ℓ)]|[A-Za-zΑ-ωℓ]/g,a=>/[A-Za-zΑ-ωℓ]/.test(a)?`<bdi dir="ltr" class="fx">${a}</bdi>`:a);
const EXPL=new Set(),OPN=new Set();
/* the formal statement behind every rule the solver names in words */
const FORM={'סכום הדרגות (1.3)':'Σ deg(u) = 2m  ⇒  n·δ ≤ 2m ≤ n·Δ','נוסחת אוילר (5.3)':'planar  ⇒  f = m − n + c + 1','עץ (2.5)':'tree  ⇒  m = n − 1','עלה בעץ (2.3)':'tree, n ≥ 2  ⇒  δ = 1','עץ הוא דו-צדדי':'tree, n ≥ 2  ⇒  χ = 2',
 'עץ או יער: m = n − c':'forest  ⇒  m = n − c','יער: m = n − c':'forest  ⇒  m = n − c','עץ':'tree  ⇒  c = 1','בעץ: ℓ ≥ 2, ℓ ≥ Δ':'tree, n ≥ 2  ⇒  ℓ ≥ max(2, Δ)','בעץ: ℓ ≥ Δ':'tree  ⇒  Δ ≤ ℓ','בעץ: לא כל הצמתים עלים':'tree, n ≥ 3  ⇒  ℓ ≤ n − 1',
 'בעץ: הצמתים שאינם עלים מכסים את כל הקשתות':'tree, n ≥ 3  ⇒  β ≤ n − ℓ','בעץ: סכום הדרגות קובע כמה עלים אפשריים':'2(n − 1) = Σ deg(u) ≤ ℓ + (n − ℓ)·Δ  ⇒  ℓ ≤ (2 + n(Δ − 2)) / (Δ − 1)','כיסוי בצמתים של עץ: β ≥ m / Δ, קניג':'tree  ⇒  ν = β ≥ m / Δ',
 'ביער יש צומת מדרגה קטנה':'forest  ⇒  δ ≤ 1','רכיב עם קשת ביער הוא עץ: שני עלים':'forest, m ≥ 1  ⇒  ℓ ≥ 2','כל רכיב ביער הוא עץ: שני עלים לרכיב':'forest, δ ≥ 1  ⇒  ℓ ≥ 2c','אין מעגלים: פאה אחת':'forest  ⇒  f = 1',
 'קשיר':'connected  ⇒  c = 1;   n ≥ 2  ⇒  δ ≥ 1','קשיר, שלושה צמתים לפחות':'connected, n ≥ 3  ⇒  Δ ≥ 2','יש קשת':'m ≥ 1  ⇒  Δ ≥ 1,  χ ≥ 2,  ω ≥ 2,  ν ≥ 1,  c ≤ n − 1','אין קשתות':'m = 0  ⇒  Δ = 0,  χ = 1,  ν = 0',
 'כל הדרגות בטווח':'a ≤ deg(u) ≤ b  for all u  ⇒  δ ≥ a,  Δ ≤ b','ארבעת הצבעים (6.3)':'planar  ⇒  χ ≤ 4','מישורי: m ≤ 3n − 6 (5.4)':'planar, n ≥ 3  ⇒  m ≤ 3n − 6','מישורי בלי משולשים: m ≤ 2n − 4':'planar, no triangle, n ≥ 3  ⇒  m ≤ 2n − 4','מישורי: δ ≤ 5 (5.5)':'planar  ⇒  δ ≤ 5','3f ≤ 2m':'planar, n ≥ 3  ⇒  3f ≤ 2m',
 'דו-צדדי (1.6)':'bipartite  ⇒  χ ≤ 2','דו-צדדי: m ≤ n² / 4':'bipartite (A, B)  ⇒  m ≤ |A|·|B| ≤ n² / 4','דו-צדדי: צד אחד הוא בלתי תלוי':'bipartite (A, B)  ⇒  α ≥ max(|A|, |B|) ≥ n / 2','קניג (4.16)':'bipartite  ⇒  β = ν',
 'בלי משולשים':'no triangle  ⇒  ω ≤ 2','בלי משולשים: m ≤ n² / 4':'no triangle  ⇒  m ≤ n² / 4','צומת מכסה לכל היותר Δ קשתות':'m ≤ β·Δ','קשת בזיווג חוסמת לכל היותר 2Δ − 1 קשתות':'m ≤ ν·(2Δ − 1)','כל קשת בזיווג מחברת שני צמתים':'c ≤ n − ν','צומת מכל רכיב: קבוצה בלתי תלויה':'α ≥ c',
 'קליקה: ω(ω − 1) / 2 קשתות':'m ≥ ω(ω − 1) / 2','צביעה ב־χ צבעים דורשת קשת בין כל שני צבעים':'m ≥ χ(χ − 1) / 2','אין צמתים מבודדים':'δ ≥ 1  ⇒  ν ≥ 1','המילטוני (דירק 3.3)':'δ ≥ n / 2  ⇒  Hamiltonian  ⇒  ν = ⌊n / 2⌋',
 'דרגות אי-זוגיות: מספר צמתים זוגי':'Σ deg(u) = 2m,  deg(u) odd for all u  ⇒  n even','כל הדרגות זוגיות':'deg(u) even for all u  ⇒  δ, Δ even','כל הדרגות אי-זוגיות':'deg(u) odd for all u  ⇒  δ, Δ odd',
 'אוילרי: קשיר':'Eulerian  ⇒  c = 1','אוילרי: כל הדרגות זוגיות, ואין צומת מבודד':'Eulerian, n ≥ 2  ⇒  deg(u) even,  deg(u) ≥ 1  ⇒  δ ≥ 2','אוילרי: כל דרגה שתיים לפחות':'δ ≥ 2  ⇒  2m = Σ deg(u) ≥ 2n  ⇒  m ≥ n',
 'המילטוני: קשיר':'Hamiltonian  ⇒  c = 1','מעגל המילטון':'Hamiltonian  ⇒  n ≥ 3','המילטוני: כל צומת על המעגל':'Hamiltonian  ⇒  δ ≥ 2','המילטוני: קשתות המעגל':'Hamiltonian  ⇒  m ≥ n','המילטוני: זיווג מתוך המעגל':'Hamiltonian  ⇒  ν = ⌊n / 2⌋','המילטוני: לכל היותר כל צומת שני על המעגל':'Hamiltonian  ⇒  α ≤ n / 2',
 'דו-צדדי המילטוני: מעגל באורך זוגי':'bipartite, Hamiltonian  ⇒  n even','זיווג מושלם':'perfect matching  ⇒  ν = n / 2','זיווג מושלם: אין צומת מבודד':'perfect matching  ⇒  δ ≥ 1','זיווג מושלם: מספר צמתים זוגי':'perfect matching  ⇒  n even',
 'גרף או המשלים שלו קשיר, והם איזומורפיים':'G ≅ complement  ⇒  c = 1','איזומורפי למשלים':'G ≅ complement  ⇒  m = n(n − 1) / 4','איזומורפי למשלים: Δ + δ = n − 1':'G ≅ complement  ⇒  Δ + δ = n − 1','איזומורפי למשלים: קליקה כאן היא קבוצה בלתי תלויה במשלים':'G ≅ complement  ⇒  ω = α',
 'לא דו-צדדי (1.6)':'not bipartite  ⇒  χ ≥ 3','לא דו-צדדי: מעגל אי-זוגי':'not bipartite  ⇒  odd cycle  ⇒  n ≥ 3,  m ≥ 3','לא מישורי (5.8)':'not planar  ⇒  subdivision of K₅ or K₃,₃  ⇒  n ≥ 5,  m ≥ 9,  Δ ≥ 3',
 'אין שני צמתים לא שכנים: גרף מלא':'α = 1  ⇒  ω = n,  δ = n − 1','גרף מלא':'ω = n  ⇒  m = n(n − 1) / 2','כל קשת חסרה מורידה דרגה אחת לכל היותר לצומת':'δ ≥ (n − 1) − (n(n − 1) / 2 − m)','המשלים של גרף לא קשיר הוא קשיר':'c(G) ≥ 2  ⇒  c(complement) = 1',
 'סכום על רכיבי הקשירות':'x(G) = Σ x(Cᵢ)   for x ∈ {n, m, α, ν, β}','לפי רכיבי הקשירות':'Δ(G) = max Δ(Cᵢ),  δ(G) = min δ(Cᵢ),  χ(G) = max χ(Cᵢ),  ω(G) = max ω(Cᵢ)','רכיבי הקשירות שהוגדרו':'c ≥ number of defined components',
 'קשתות ברכיבים שהוגדרו, ועוד כל מה שנכנס בצמתים שנותרו':'m ≤ Σ m(Cᵢ) + r(r − 1) / 2,   r vertices left','הסרת צומת מעץ: רכיב לכל שכן':'T tree  ⇒  c(T − v) = deg(v)','בגרף אוילרי אין גשר: כל קשת על מעגל':'Eulerian  ⇒  c(G − e) = c(G)',
 'בגרף המילטוני: מה שנשאר מהמעגל מחבר את כל הצמתים':'Hamiltonian  ⇒  c(G − v) = c(G − e) = 1','בגרף המילטוני: הסרת קבוצה מפרקת את המעגל לכל היותר למספר חלקים כגודלה':'Hamiltonian  ⇒  c(G − S) ≤ |S|',
 'שני שכנים בגרף בלי משולשים: אין להם שכן משותף':'uw ∈ E, no triangle  ⇒  Γ(u) ∩ Γ(w) = ∅  ⇒  deg(u) + deg(w) ≤ n','דירק (3.3)':'δ ≥ n / 2,  n ≥ 3  ⇒  Hamiltonian','מסקנה מ־1.3':'Σ deg(u) = 2m,  deg(u) odd for all u  ⇒  n even','משפט 3.1':'connected, deg(u) even for all u  ⇔  Eulerian',
 'קשיר, m = n':'connected, m = n  ⇒  exactly one cycle','רכיב קשירות של יער':'forest, connected  ⇒  tree','יער קשיר':'forest, connected  ⇒  tree','שני עלים בדיוק':'tree, ℓ = 2  ⇒  Δ ≤ 2  ⇒  path','מספר צמתים אי-זוגי':'n odd  ⇒  ν ≤ (n − 1) / 2 < n / 2',
 'פרק 1, שאלה 3':'δ ≥ 2  ⇒  simple cycle on at least δ + 1 vertices','מכיל תת-גרף לא דו-צדדי':'H ⊆ G,  H not bipartite  ⇒  G not bipartite','מכיל תת-גרף לא מישורי, או נוצר מהעדנה של גרף לא מישורי':'H ⊆ G,  H not planar  ⇒  G not planar'};
/* the formal reading of each insight */
const INSF={'הגרף קשיר':'c = 1','הגרף המילטוני':'Hamiltonian','הגרף אוילרי':'Eulerian','הגרף אינו מישורי':'not planar','הגרף אינו דו-צדדי':'not bipartite','הגרף הוא עץ':'tree','הגרף הוא יער':'forest','יש זיווג מושלם':'ν = n / 2','אין זיווג מושלם':'ν < n / 2',
 'יש בגרף מעגל אחד בדיוק':'exactly one cycle','הגרף מלא':'m = n(n − 1) / 2','יש בגרף מעגל, ולכן הוא אינו יער':'m > n − c  ⇒  not a forest','מספר הצמתים זוגי':'n even','העץ הוא מסלול':'path','העץ הוא כוכב':'star','הגרף אינו אוילרי: כל הדרגות אי-זוגיות':'not Eulerian'};
/* what each operation does to the quantities; x′ is the quantity after the operation */
const OPF={compl:"n′ = n,   m + m′ = n(n − 1) / 2,   Δ′ = n − 1 − δ,   δ′ = n − 1 − Δ,   ω′ = α,   α′ = ω",
 delv:"n′ = n − 1,   m′ = m − deg(v),   χ − 1 ≤ χ′ ≤ χ,   α − 1 ≤ α′ ≤ α,   ν − 1 ≤ ν′ ≤ ν,   δ′ ≥ δ − 1,   Δ′ ≤ Δ",
 dele:"n′ = n,   m′ = m − 1,   c ≤ c′ ≤ c + 1,   χ − 1 ≤ χ′ ≤ χ,   ν − 1 ≤ ν′ ≤ ν,   α ≤ α′ ≤ α + 1",
 adde:"n′ = n,   m′ = m + 1,   c − 1 ≤ c′ ≤ c,   χ ≤ χ′ ≤ χ + 1,   ν ≤ ν′ ≤ ν + 1,   α − 1 ≤ α′ ≤ α",
 delS:"n′ = n − |S|,   x′ ≤ x  for x ∈ {m, Δ, χ, ω, ν, α},   χ′ ≥ χ − |S|,   ν′ ≥ ν − |S|",
 ind:"H ⊆ G  ⇒  x(H) ≤ x(G)  for x ∈ {n, m, Δ, χ, ω, ν, α}",span:"H ⊆ G, V(H) = V(G)  ⇒  n′ = n,   m′ ≤ m,   c′ ≥ c,   α′ ≥ α,   χ′ ≤ χ",
 comp:"C component of G  ⇒  c(C) = 1,   δ(C) ≥ δ(G),   x(C) ≤ x(G)  for x ∈ {n, m, Δ, χ, ω, ν, α}",subd:"n′ = n + 1,   m′ = m + 1,   c′ = c",contr:"n′ = n − 1,   c′ = c,   m′ ≤ m − 1",
 join:"F joins the components, |F| = c − 1, every edge of F a bridge  ⇒  n′ = n,  m′ = m + c − 1,  c′ = 1,  χ′ = max(χ, 2),  ω′ = max(ω, 2),  Δ ≤ Δ′ ≤ Δ + c − 1,  ν ≤ ν′ ≤ ν + c − 1,  α − (c − 1) ≤ α′ ≤ α"};
const hasHeb=x=>/[֐-׿]/.test(x);
const symOf=x=>SYM[x.k]+(by(x.g)?sub(by(x.g)):`<sub>${x.g}</sub>`);
/* premises, the rule in its formal form, and the conclusion */
function derive(u,r,concl,name){
  const lines=u.map(x=>[`${symOf(x)} ${x.i?'≤':'≥'} ${x.v}`,rz(x.r)]);
  if(r==='נתון')return prf([[concl,'נתון']]);
  if(r==='מהפעולה')return prf([...lines,[concl,`הפעולה שיצרה את ${name}, לפי נתוני גרף המקור`]]);
  if(r==='מהנתונים')return prf([...lines,[concl,'ישירות מהנתונים']]);
  if(r.startsWith('חיבור הרכיבים של ')||r.startsWith('פירוק החיבור ')){lines.push([OPF.join,`${rz(r)}; הסימן ′ הוא הגודל אחרי החיבור`]);lines.push([`∴  ${concl}`,'הצבה']);return prf(lines)}
  if(r.startsWith('מ־')){const Y=r.slice(2),me=by(name),ot=by(Y),lk=me&&me.op&&me.src===Y?me:ot&&ot.op&&ot.src===name?ot:null;
    if(lk&&OPF[lk.op]){lines.push([OPF[lk.op],`${OPS[lk.op][0]}: ${rz(lk.name)} מתוך ${rz(lk.src)}, והסימן ′ הוא הגודל ב־${rz(lk.name)}`]);lines.push([`∴  ${concl}`,'הצבה']);return prf(lines)}}
  const f=FORM[r]||(hasHeb(r)?'':r.replace(/\s*\(\d+\.\d+\)$/,'')),ref=(r.match(/\((\d+\.\d+)\)$/)||[])[1];
  if(f)lines.push([f,hasHeb(r)?rz(r):ref?`משפט ${ref}`:'כלל']);
  lines.push([`∴  ${concl}`,f?'הצבה':rz(r)]);return prf(lines)}
function tell(g,k,i,d,one){const v=d.B[k][i],r=d.W[k][i],u=one?[...d.U[k][0],...d.U[k][1]].filter((x,n,A)=>A.findIndex(y=>y.g===x.g&&y.k===x.k&&y.i===x.i)===n):d.U[k][i]||[];
  const cl=`${SYM[k]+sub(g)} ${one?'=':i?'≤':'≥'} ${v}`;
  return `<div class="qpb"><div class="qph"><span>${DEF[k]}: ${one?'הערך':i?'החסם העליון':'החסם התחתון'}</span><bdi dir="ltr" class="fx">${cl}</bdi></div>${derive(u,r,cl,g.name)}</div>`}
function digestHtml(){
  const G=graphs(),open=!COL.has('Σ'),first=solveAll(),VR=new Map();
  for(const g of G){const d=first.get(g);if(d&&!d.bad)VR.set(g,virtFor(g,d))}
  const memo=solveAll([...VR.values()].flat().flatMap(x=>x.arg?[x.arg,x.h]:[x.h]));
  const body=G.map(g=>{const d=memo.get(g),s=sub(g),rows=[];
    if(d.bad)return `<div class="qtp"><div class="qsg"><span class="name">${g.name}</span><b>${titleOf(g)}</b></div><div class="qwarn">הנתונים של ${g.name} סותרים זה את זה, ולכן אין תמצית.</div></div>`;
    for(const k in SYM){if(k==='f'&&!d.pl)continue;if(k==='lv'&&!d.fo)continue;if(k==='c'&&g.op==='comp')continue;const [lo,hi]=d.B[k],w=d.W[k],sym=SYM[k]+s;
      if(lo===D0[k]&&hi===Infinity)continue;const given=val(g,k)!==null;
      const why=given?'נתון':[...new Set([lo>D0[k]?w[0]:null,hi<Infinity?w[1]:null].filter(Boolean))].map(rz).join(' · ');
      const f=lo===hi?`${sym} = ${V(lo)}`:`${lo>D0[k]?V(lo)+' ≤ ':''}${sym}${hi<Infinity?' ≤ '+V(hi):''}`;
      const key=g.name+'|'+k,opn=EXPL.has(key),one=lo===hi&&(w[0]===w[1]||lo===D0[k]);
      const ex=opn?`<div class="qex">${one?tell(g,k,lo===D0[k]?1:0,d,true):(lo>D0[k]?tell(g,k,0,d):'')+(hi<Infinity?tell(g,k,1,d):'')}</div>`:'';
      rows.push(`<div class="qi${given?'':' der'}"><div class="qn">${DEF[k]}</div><div class="qf"><span class="fx qsub">${f}</span><button class="qexb" data-ex="${key}" aria-expanded="${opn}">${opn?'הסתר הסבר':'הסבר'}</button></div>${ex}</div>`)}
    d.N.forEach(([t,r,u],n)=>{const key=g.name+'|i'+n,opn=EXPL.has(key);rows.push(`<div class="qi ins"><div class="qn">תובנה</div><div class="qf"><span class="qins">${t}</span><button class="qexb" data-ex="${key}" aria-expanded="${opn}">${opn?'הסתר הסבר':'הסבר'}</button></div>${opn?`<div class="qex">${derive(u||[],r,`${g.name}:  ${INSF[t]||t.replace(/^יש מעגל פשוט על (\d+) צמתים לפחות$/,'simple cycle on ≥ $1 vertices')}`,g.name)}</div>`:''}</div>`)});
    { const P=pairInfo(g,d,memo);if(P.ore&&g.ha!=='y'&&!d.N.some(x=>x[0]==='הגרף המילטוני')){const key=g.name+'|ore',opn=EXPL.has(key);
        rows.push(`<div class="qi ins"><div class="qn">תובנה</div><div class="qf"><span class="qins">הגרף המילטוני</span><button class="qexb" data-ex="${key}" aria-expanded="${opn}">${opn?'הסתר הסבר':'הסבר'}</button></div>${opn?`<div class="qex">${prf([...P.eNadjLo,[`deg<sub>${g.name}</sub>(u) + deg<sub>${g.name}</sub>(w) ≥ ${P.nadjLo} ≥ ${d.B.n[1]} ≥ n   for all uw ∉ E(${g.name})`,'מהשורות הקודמות'],[`deg(u) + deg(w) ≥ n  for all uw ∉ E,  n ≥ 3  ⇒  Hamiltonian`,'משפט אור (3.2)'],[`∴  ${g.name} Hamiltonian`,'']])}</div>`:''}</div>`)}}
    /* the standard moves on this graph */
    const mv=[],oo=OPN.has(g.name);
    if(oo){for(const r of pairRows(g,d,memo)){const key=g.name+'|p'+mv.length,opn=EXPL.has(key);mv.push(`<div class="qi der"><div class="qn">${r.t}</div><div class="qf"><span class="fx qsub">${r.f}</span><button class="qexb" data-ex="${key}" aria-expanded="${opn}">${opn?'הסתר הסבר':'הסבר'}</button></div>${opn?`<div class="qex">${r.e}</div>`:''}</div>`)}
      /* the standard moves as one table: a row for each move, a column for each quantity */
      const KS=['n','m','c','D','dl','chi','al','nu','om'],tb=[];
      const cell=([lo,hi],k)=>lo===hi?`<span class="qv">${lo}</span>`:lo>D0[k]&&hi<Infinity?`<span class="qv">${lo}</span> … <span class="qv">${hi}</span>`:hi<Infinity?`≤ <span class="qv">${hi}</span>`:lo>D0[k]?`≥ <span class="qv">${lo}</span>`:'<span class="na">—</span>';
      for(const v of VR.get(g)||[]){const e=memo.get(v.h);if(!e)continue;const key=g.name+'|v'+v.h.name,opn=EXPL.has(key),ks=KS.filter(k=>!(e.B[k][0]===D0[k]&&e.B[k][1]===Infinity));
        const cells=e.bad?`<td colspan="${KS.length}" class="bad">הפעולה סותרת את הנתונים</td>`:KS.map(k=>`<td class="fx"><bdi dir="ltr">${cell(e.B[k],k)}</bdi></td>`).join('');
        tb.push(`<tr><th scope="row">${v.title} <bdi dir="ltr" class="fx nm">${v.h.name}</bdi></th>${cells}<td class="bx">${e.bad?'':`<button class="qexb" data-ex="${key}" aria-expanded="${opn}">${opn?'הסתר':'הסבר'}</button>`}</td></tr>`);
        if(opn&&!e.bad)tb.push(`<tr class="exr"><td colspan="${KS.length+2}"><div class="qex">${ks.map(k=>{const [lo,hi]=e.B[k],one=lo===hi&&(e.W[k][0]===e.W[k][1]||lo===D0[k]);return one?tell(v.h,k,lo===D0[k]?1:0,e,true):(lo>D0[k]?tell(v.h,k,0,e):'')+(hi<Infinity?tell(v.h,k,1,e):'')}).join('')}</div></td></tr>`)}
      if(tb.length)mv.push(`<div class="qtw"><table class="qtab"><thead><tr><th scope="col">אחרי הפעולה, הגרף <bdi dir="ltr" class="fx">${g.name}′</bdi></th>${KS.map(k=>`<th scope="col" class="fx" title="${DEF[k]}"><bdi dir="ltr">${SYM[k]}<sub>${g.name}′</sub></bdi></th>`).join('')}<th></th></tr></thead><tbody>${tb.join('')}</tbody></table></div><dl class="qtl">${[['−v','הסרת צומת אחד, כלשהו'],['−e','הסרת קשת אחת, כלשהי'],['−uw','הסרת שני צמתים שכנים: uw היא קשת'],['−u,w','הסרת שני צמתים שאינם שכנים'],['+e','הוספת קשת אחת בין שני צמתים שאינם שכנים'],['+F','הוספת קבוצת קשתות F שמחברת את כל הרכיבים: כל קשת בין שני רכיבים שונים, ומספר הקשתות הוא מספר הרכיבים פחות אחת'],['′','בכותרות: הגודל בגרף שמתקבל אחרי הפעולה']].map(([a,b])=>`<div><dt><bdi dir="ltr" class="fx">${a}</bdi></dt><dd>${b}</dd></div>`).join('')}</dl>`)}
    const moves=`<button class="qmv" data-mv="${g.name}" aria-expanded="${oo}">${oo?'▾':'◂'} פעולות על ${g.name} <span class="lab">זוגות צמתים, הסרות, הוספת קשת ומשלים, בלי להגדיר אותן</span></button>${oo?`<div class="qitems one">${mv.join('')}</div>`:''}`;
    return `<div class="qtp"><div class="qsg"><span class="name">${g.name}</span><b>${titleOf(g)}</b><span class="lab">${rows.length}</span></div><div class="qitems">${rows.join('')||'<div class="hint">אין עדיין נתונים שמצמצמים משהו.</div>'}</div>${moves}</div>`}).join('');
  return `<section class="qt qsum"><h3 class="qcap"><button class="qmin" data-tp="Σ" aria-expanded="${open}">${open?'▾':'◂'}</button>תמצית <span class="lab">מה נובע מכל הנוסחאות יחד: הערך או הטווח של כל גודל, עם הסבר לכל חסם</span></h3>${open?body:''}</section>`}
function renderSheet(){
  document.getElementById('qsheet').innerHTML=graphs().map(sheetFor).join('')+digestHtml();
  const L=[];for(const g of graphs()){const s=sub(g);for(const k in SYM){if(k==='f'&&g.pl==='n')continue;{const e=ex(g,k).num,iv=e===null?interval(g,k):null;L.push([SYM[k]+s,DEF[k]+' של '+g.name,e!==null?e:iv?`${iv[0]??'?'} … ${iv[1]??'?'}`:null])}}}
  for(const o of O){if(o.t==='v'&&o.q!=='all')L.push([`deg${sub(by(o.in))}(${o.name})`,`הדרגה של ${o.name} ב־${o.in}${o.q==='one'&&o.w?(o.w==='max'?', הגבוהה ביותר':', הנמוכה ביותר'):''}`,dEx(o)!==null?dEx(o):dLo(o)!==null||dHi(o)!==null?`${dLo(o)??'?'} … ${dHi(o)??'?'}`:null]);if(o.t==='s')L.push([`|${o.name}|`,`מספר הצמתים ב־${o.name}`,o.k])}
  L.push(['Γ(X)','קבוצת השכנים של צומתי X',null]);
  document.getElementById('qlegend').innerHTML=L.map(([k,d,v])=>`<div class="${v!==null?'given':''}"><dt class="fx">${k}${v!==null?' = '+v:''}</dt><dd>${d}</dd></div>`).join('')}
document.addEventListener('input',ev=>{const t=ev.target,i=t.dataset.i,k=t.dataset.k;if(i===undefined||!t.closest('.qb'))return;const o=O[i];
  if(t.dataset.r){const q=parseNum(t.value);(o.tx=o.tx||{})[k]=t.value;(o.rg=o.rg||{})[k]=q.r;o[k]=q.v;t.setAttribute('aria-invalid',String(!!q.bad));
    if(o.t==='v'&&k==='d'){o.dm=q.r?'rng':'eq';o.d1=q.r?q.r[0]:null;o.d2=q.r?q.r[1]:null}}
  else o[k]=t.type==='checkbox'?t.checked:t.value;
  if(['op','src','in','arg','dm','q'].includes(k)){if(o.t==='g'&&o.op)ensureArg(o);O.filter(g=>g.t==='g'&&g.op).forEach(ensureArg);fixNames();renderObjs()}
  renderSheet()});
document.addEventListener('click',ev=>{const t=ev.target.closest&&ev.target.closest('.qsheet [data-mv]');if(t){const k=t.dataset.mv;if(OPN.has(k))OPN.delete(k);else OPN.add(k);renderSheet()}});
document.addEventListener('click',ev=>{const t=ev.target.closest&&ev.target.closest('.qsheet [data-ex]');if(t){const k=t.dataset.ex;if(EXPL.has(k))EXPL.delete(k);else EXPL.add(k);renderSheet()}});
document.addEventListener('click',ev=>{const t=ev.target.closest&&ev.target.closest('.qsheet [data-min]');if(t){const k=t.dataset.min;if(COLG.has(k))COLG.delete(k);else COLG.add(k);renderSheet()}});
document.addEventListener('click',ev=>{const t=ev.target.closest&&ev.target.closest('.qsheet [data-tp]');if(t){const k=t.dataset.tp;if(COL.has(k))COL.delete(k);else COL.add(k);renderSheet()}});
document.addEventListener('click',ev=>{if(!ev.target.closest||!ev.target.closest('.qb'))return;const a=ev.target.closest('[data-add]'),d=ev.target.closest('[data-del]'),mo=ev.target.closest('[data-more]');
  if(mo){const o=O[Number(mo.dataset.more)];o.more=!o.more}
  else if(d){removeObj(d.dataset.del)}
  else if(a){const t=a.dataset.add,last=graphs()[graphs().length-1].name;
    if(t==='v')O.push({t:'v',name:fresh('v'),in:last,q:'one',d:null,cut:false});
    if(t==='e')O.push({t:'e',name:fresh('e'),in:last,bridge:false});
    if(t==='s')O.push({t:'s',name:fresh('s'),in:last,k:null,prop:''});
    if(t==='g'){const g=newG(fresh('g'),{op:'compl',src:last,arg:null});O.push(g);ensureArg(g);fixNames()}}
  else return;renderObjs();renderSheet()});
return{
/* for tests: solve a list of objects without touching the page */
solve(list){const keep=O.slice();O.splice(0,O.length,...list.map(o=>o.t==='g'?newG(o.name,o):o));
  try{const m=solveAll();return graphs().map(g=>{const d=m.get(g);return{name:g.name,bad:d.bad,B:JSON.parse(JSON.stringify(d.B,(k,v)=>v===Infinity?'inf':v)),N:d.N.map(x=>x[0]),P:d.bad?null:(q=>({adjLo:q.adjLo,adjHi:q.adjHi===Infinity?'inf':q.adjHi,nadjLo:q.nadjLo,nadjHi:q.nadjHi===Infinity?'inf':q.nadjHi,ore:q.ore}))(pairInfo(g,d,m)),ore:!d.bad&&pairInfo(g,d,m).ore}})}finally{O.splice(0,O.length,...keep)}},
render(){
  document.getElementById('conds').innerHTML=`<div class="qb"><div class="colhead"><h2>נתוני השאלה</h2><span class="lab">אובייקטים, פעולות וערכים</span></div><div id="qobjs" class="qlist"></div>
  <div class="qbox"><div class="lab">הוסף אובייקט</div><div class="addrow"><button class="addb" data-add="v">+ צומת</button><button class="addb" data-add="e">+ קשת</button><button class="addb" data-add="s">+ קבוצת צמתים</button><button class="addb" data-add="g">+ גרף מפעולה</button></div>
  <p class="hint">גרף מפעולה נוצר מגרף קיים, ואפשר להפעיל עליו פעולה נוספת. הכמת של צומת קובע לאן הדרגה שלו נכנסת בנוסחאות.</p><p class="hint">בכל תא מספרי אפשר לכתוב מספר או טווח: <span class="fx">2-5</span>, לפחות <span class="fx">3-</span>, לכל היותר <span class="fx">-5</span>.</p></div></div>`;
  document.getElementById('main').innerHTML=`<div class="qsheet" id="qsheet"></div>`;
  document.getElementById('card').innerHTML=`<div class="cardhead"><h2>מקרא הסמלים</h2></div><dl id="qlegend" class="qleg"></dl><p class="hint">סמל צבוע הוא נתון. השאר לא נתונים, ומוצגים בנוסחאות לפי ההגדרה שלהם.</p>`;
  renderObjs();renderSheet()}};
})();
