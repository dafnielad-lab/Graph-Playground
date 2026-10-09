/* ---------- formula-sheet mode: objects, operations, live substitution ---------- */
const SHEET=(()=>{
const V=x=>`<span class="qv">${x}</span>`;
/* objects of the question, in order; a derived graph may only use objects defined above it.
   graph properties are tri-state: 'y' given true, 'n' given false, 'u' unknown */
const newG=(name,o)=>Object.assign({t:'g',name,n:null,m:null,c:null,D:null,dl:null,f:null,chi:null,al:null,nu:null,be:null,rho:null,pl:'u',tr:'u',bp:'u',more:false},o);
let O=[newG('G',{n:10,c:1,pl:'y'}),
       {t:'v',name:'v',in:'G',q:'one',d:3,cut:false},
       newG('H',{op:'delv',src:'G',arg:'v',c:2})];
const NAMES={v:['v','u','w','x','y','z'],e:['e','e₂','e₃','e₄'],s:['S','T','A','B'],g:['H','K','L','M','N']};
const OPS={delv:['הסרת הצומת','v'],dele:['הסרת הצלע','e'],delS:['הסרת קבוצת הצמתים','s'],adde:['הוספת צלע',null],contr:['כיווץ הצלע','e'],subd:['העדנת הצלע','e'],compl:['המשלים',null],ind:['תת-גרף מושרה על','s'],comp:['רכיב קשירות',null],span:['תת-גרף פורש',null]};
const SYM={n:'n',m:'m',c:'c',D:'Δ',dl:'δ',f:'f',chi:'χ',al:'α',nu:'ν',be:'β',rho:'ρ'};
const DEF={n:'מספר הצמתים',m:'מספר הצלעות',c:'מספר רכיבי הקשירות',D:'הדרגה המקסימלית',dl:'הדרגה המינימלית',f:'מספר הפאות בשיכון מישורי',chi:'מספר הצביעה',al:'גודל קבוצה בלתי תלויה מקסימלית',nu:'גודל זיווג מקסימום',be:'גודל מינימלי של כיסוי בצמתים',rho:'גודל מינימלי של כיסוי בצלעות'};
const PROPS={pl:'מישורי',tr:'עץ',bp:'דו-צדדי',conn:'קשיר'};
const by=n=>O.find(o=>o.name===n),graphs=()=>O.filter(o=>o.t==='g');
const fresh=t=>NAMES[t].find(n=>!by(n))||NAMES[t][0]+O.length;
function ensureArg(g){const need=OPS[g.op][1];if(!need){g.arg=null;return}
  const cur=by(g.arg);if(cur&&cur.t===need&&cur.in===g.src&&O.indexOf(cur)<O.indexOf(g))return;
  let a=O.find(o=>o.t===need&&o.in===g.src&&O.indexOf(o)<O.indexOf(g));
  if(!a){a=need==='v'?{t:'v',name:fresh('v'),in:g.src,q:'one',d:null,cut:false}:need==='e'?{t:'e',name:fresh('e'),in:g.src,bridge:false}:{t:'s',name:fresh('s'),in:g.src,k:null,prop:''};O.splice(O.indexOf(g),0,a)}
  g.arg=a.name}
function removeObj(name){const dep=O.filter(o=>o.in===name||o.src===name||o.arg===name).map(o=>o.name);O=O.filter(o=>o.name!==name);dep.forEach(removeObj)}
const opt=(list,cur)=>list.map(([v,l])=>`<option value="${v}" ${v===cur?'selected':''}>${l}</option>`).join('');
const num=(i,k,val,lab)=>`<label class="cell">${lab}<input type="number" min="0" data-i="${i}" data-k="${k}" value="${val===null||val===undefined?'':val}" placeholder="?" id="f${i}${k}"></label>`;
const tri=(i,k,val,lab)=>`<label class="cell">${lab}<select data-i="${i}" data-k="${k}" id="f${i}${k}">${opt([['u','לא ידוע'],['y','כן'],['n','לא']],val)}</select></label>`;
const chk=(i,k,val,lab)=>`<label class="cell">${lab}<input type="checkbox" data-i="${i}" data-k="${k}" id="f${i}${k}" ${val?'checked':''}></label>`;
function renderObjs(){
  document.getElementById('qobjs').innerHTML=O.map((o,i)=>{const gs=opt(graphs().filter(g=>o.t!=='g'||O.indexOf(g)<i).map(g=>[g.name,g.name]),o.t==='g'?o.src:o.in),x=o.name==='G'?'':`<button class="x" data-del="${o.name}" aria-label="הסר את ${o.name}">×</button>`;
    if(o.t==='g')return `<div class="qbox"><div class="qrow"><span class="name">${o.name}</span>${o.op?`<span>=</span><select data-i="${i}" data-k="op" id="f${i}op" aria-label="פעולה">${opt(Object.entries(OPS).map(([k,v])=>[k,v[0]]),o.op)}</select>${o.arg?`<select data-i="${i}" data-k="arg" id="f${i}arg" aria-label="על מה">${opt(O.filter(a=>a.t===OPS[o.op][1]&&a.in===o.src&&O.indexOf(a)<i).map(a=>[a.name,a.name]),o.arg)}</select>`:''}<span>${o.op==='compl'||o.op==='comp'||o.op==='span'?'של':'מתוך'}</span><select data-i="${i}" data-k="src" id="f${i}src" aria-label="גרף מקור">${gs}</select>`:'<span>הגרף הנתון</span>'}${x}</div>
      <div class="qrow">${num(i,'n',o.n,'צמתים')}${num(i,'m',o.m,'צלעות')}${num(i,'c',o.c,'רכיבים')}</div>
      <div class="qrow">${tri(i,'pl',o.pl,'מישורי')}${tri(i,'tr',o.tr,'עץ')}${tri(i,'bp',o.bp,'דו-צדדי')}</div>
      ${o.more?`<div class="qrow">${['D','dl','f','chi','al','nu','be','rho'].map(k=>num(i,k,o[k],`<span class="fx">${SYM[k]}</span>`)).join('')}</div>`:''}
      <button class="link" data-more="${i}">${o.more?'הסתר גדלים נוספים':'גדלים נוספים: דרגות, פאות, צביעה, זיווג'}</button></div>`;
    if(o.t==='v')return `<div class="qbox"><div class="qrow"><span class="name v">${o.name}</span><select data-i="${i}" data-k="q" id="f${i}q" aria-label="כמת">${opt([['one','צומת מסוים'],['all','כל צומת'],['ex','קיים צומת']],o.q)}</select><span>ב־</span><select data-i="${i}" data-k="in" id="f${i}in" aria-label="בגרף">${gs}</select>${x}</div><div class="qrow"><span class="cell">דרגה</span><select data-i="${i}" data-k="dm" id="f${i}dm" aria-label="סוג הנתון על הדרגה">${opt([['eq','בדיוק'],['rng','בטווח']],o.dm||'eq')}</select>${o.dm==='rng'?num(i,'d1',o.d1,'מ־')+num(i,'d2',o.d2,'עד'):num(i,'d',o.d,'')}${chk(i,'cut',o.cut,'צומת מפריד')}</div></div>`;
    if(o.t==='e')return `<div class="qbox"><div class="qrow"><span class="name v">${o.name}</span><span>צלע ב־</span><select data-i="${i}" data-k="in" id="f${i}in" aria-label="בגרף">${gs}</select>${x}</div><div class="qrow">${chk(i,'bridge',o.bridge,'גשר (הסרתה מנתקת)')}</div></div>`;
    return `<div class="qbox"><div class="qrow"><span class="name v">${o.name}</span><span>קבוצת צמתים ב־</span><select data-i="${i}" data-k="in" id="f${i}in" aria-label="בגרף">${gs}</select>${x}</div><div class="qrow">${num(i,'k',o.k,'גודל')}<select data-i="${i}" data-k="prop" id="f${i}prop" aria-label="תכונה">${opt([['','בלי תכונה נוספת'],['indep','בלתי תלויה'],['clique','קליקה'],['cover','כיסוי בצמתים'],['side','צד בגרף דו-צדדי']],o.prop)}</select></div></div>`}).join('')}
/* symbol of a graph quantity: the given value in colour, otherwise the symbol (with the graph's name unless it is G) */
const sub=g=>g.name==='G'?'':`<sub>${g.name}</sub>`;
/* a vertex degree is exact, or a range with either end optional */
const dLo=v=>v.dm==='rng'?(v.d1??null):v.d,dHi=v=>v.dm==='rng'?(v.d2??null):v.d,dEx=v=>dLo(v)!==null&&dLo(v)===dHi(v)?dLo(v):null;
const allV=g=>O.find(o=>o.t==='v'&&o.in===g.name&&o.q==='all'&&(dLo(o)!==null||dHi(o)!==null));
const allDeg=g=>{const v=allV(g);return v?dEx(v):null};
const rngTxt=(lo,mid,hi)=>`${lo!==null?V(lo)+' ≤ ':''}${mid}${hi!==null?' ≤ '+V(hi):''}`;
const val=(g,k)=>g[k]!==null&&g[k]!==undefined?g[k]:(k==='D'||k==='dl')?allDeg(g):null;
const sy=(g,k)=>{const v=val(g,k);return v!==null?V(v):SYM[k]+sub(g)};
const degOf=v=>dEx(v)!==null?V(dEx(v)):`deg(${v.name})`;
const prop=(g,k)=>k==='conn'?(g.c===1||g.tr==='y'?'y':g.c!==null&&g.c>1?'n':'u'):g[k];
function sheetFor(g){
  const s=sub(g),q=k=>sy(g,k),n=q('n'),m=q('m'),c=q('c'),D=q('D'),dl=q('dl'),ad=allDeg(g),F=[],X=g.name;
  const add=(t,r,gen,st,need)=>F.push({t,r,g:gen,s:st,need});
  const src=g.op?by(g.src):null;
  if(src){const Q=k=>sy(src,k),N=Q('n'),M=Q('m'),C=Q('c'),a=by(g.arg),P=src.name,rel=(t,gn,st)=>F.push({t,r:'מהפעולה',g:gn,s:st,rel:1});
    if(g.op==='delv'){rel('צמתים אחרי הסרת צומת',`n(${X}) = n(${P}) − 1`,`${n} = ${N} − 1`);rel('צלעות אחרי הסרת צומת',`m(${X}) = m(${P}) − deg(${a.name})`,`${m} = ${M} − ${degOf(a)}`);
      rel('רכיבי קשירות אחרי הסרת צומת',`c(${X}) ≤ c(${P}) + deg(${a.name}) − 1`,`${c} ≤ ${C} + ${degOf(a)} − 1`);if(dEx(a)===null&&(dLo(a)!==null||dHi(a)!==null))rel('צלעות אחרי הסרת צומת, לפי טווח הדרגה',`m(${P}) − max deg ≤ m(${X}) ≤ m(${P}) − min deg`,`${dHi(a)!==null?M+' − '+V(dHi(a))+' ≤ ':''}${m}${dLo(a)!==null?' ≤ '+M+' − '+V(dLo(a)):''}`);
      if(a.cut)rel(`${a.name} צומת מפריד`,`c(${X}) ≥ c(${P}) + 1`,`${c} ≥ ${C} + 1`)}
    if(g.op==='dele'){rel('צמתים אחרי הסרת צלע',`n(${X}) = n(${P})`,`${n} = ${N}`);rel('צלעות אחרי הסרת צלע',`m(${X}) = m(${P}) − 1`,`${m} = ${M} − 1`);
      if(a.bridge)rel(`${a.name} גשר`,`c(${X}) = c(${P}) + 1`,`${c} = ${C} + 1`);else rel('רכיבי קשירות אחרי הסרת צלע',`c(${P}) ≤ c(${X}) ≤ c(${P}) + 1`,`${C} ≤ ${c} ≤ ${C} + 1`)}
    if(g.op==='delS'){const k=a.k!==null?V(a.k):`|${a.name}|`;rel('צמתים אחרי הסרת קבוצה',`n(${X}) = n(${P}) − |${a.name}|`,`${n} = ${N} − ${k}`);rel('צלעות אחרי הסרת קבוצה',`m(${X}) ≥ m(${P}) − |${a.name}|·Δ(${P})`,`${m} ≥ ${M} − ${k}·${Q('D')}`);
      if(a.prop==='indep')rel('הקבוצה בלתי תלויה: כל צלע שנוגעת בה נספרת פעם אחת',`m(${X}) = m(${P}) − Σ deg(u), u ∈ ${a.name}`,`${m} = ${M} − Σ deg(u), u ∈ ${a.name}`)}
    if(g.op==='adde'){rel('צמתים אחרי הוספת צלע',`n(${X}) = n(${P})`,`${n} = ${N}`);rel('צלעות אחרי הוספת צלע',`m(${X}) = m(${P}) + 1`,`${m} = ${M} + 1`);rel('רכיבי קשירות אחרי הוספת צלע',`c(${P}) − 1 ≤ c(${X}) ≤ c(${P})`,`${C} − 1 ≤ ${c} ≤ ${C}`)}
    if(g.op==='contr'){rel('צמתים אחרי כיווץ צלע',`n(${X}) = n(${P}) − 1`,`${n} = ${N} − 1`);rel('צלעות אחרי כיווץ צלע (שכנים משותפים מתאחדים)',`m(${X}) ≤ m(${P}) − 1`,`${m} ≤ ${M} − 1`);rel('רכיבי קשירות אחרי כיווץ',`c(${X}) = c(${P})`,`${c} = ${C}`)}
    if(g.op==='subd'){rel('צמתים אחרי העדנת צלע',`n(${X}) = n(${P}) + 1`,`${n} = ${N} + 1`);rel('צלעות אחרי העדנת צלע',`m(${X}) = m(${P}) + 1`,`${m} = ${M} + 1`);rel('רכיבי קשירות אחרי העדנה',`c(${X}) = c(${P})`,`${c} = ${C}`);F.push({t:'העדנה שומרת על מישוריות',r:'טענה 5.7',g:`${X} planar ⇔ ${P} planar`,s:'',rel:1,text:1})}
    if(g.op==='compl'){rel('צמתים במשלים',`n(${X}) = n(${P})`,`${n} = ${N}`);rel('צלעות בגרף ובמשלים',`m(${P}) + m(${X}) = n(n − 1) / 2`,`${M} + ${m} = ${N}·(${N} − 1) / 2`);const xd=allDeg(src);rel('דרגה במשלים',`deg in ${X} = n − 1 − deg in ${P}`,`deg in ${X} = ${N} − 1 − ${xd!==null?V(xd):'deg in '+P}`);
      rel('דרגה מקסימלית במשלים',`Δ(${X}) = n − 1 − δ(${P})`,`${D} = ${N} − 1 − ${Q('dl')}`);rel('קליקה במשלים היא קבוצה בלתי תלויה בגרף',`ω(${X}) = α(${P})`,`ω${s} = ${Q('al')}`)}
    if(g.op==='ind'){const k=a.k!==null?V(a.k):`|${a.name}|`;rel('צמתים בתת-גרף מושרה',`n(${X}) = |${a.name}|`,`${n} = ${k}`);rel('צלעות בתת-גרף מושרה',`m(${X}) ≤ m(${P})`,`${m} ≤ ${M}`);rel('צביעה של תת-גרף',`χ(${X}) ≤ χ(${P})`,`${q('chi')} ≤ ${Q('chi')}`);
      if(a.prop==='indep')rel('מושרה על קבוצה בלתי תלויה',`m(${X}) = 0`,`${m} = ${V(0)}`);if(a.prop==='clique')rel('מושרה על קליקה',`m(${X}) = |${a.name}|(|${a.name}| − 1) / 2`,`${m} = ${k}·(${k} − 1) / 2`)}
    if(g.op==='comp'){rel('רכיב קשירות הוא קשיר',`c(${X}) = 1`,`${c} = ${V(1)}`);rel('צמתים ברכיב',`n(${X}) ≤ n(${P})`,`${n} ≤ ${N}`);rel('צלעות ברכיב',`m(${X}) ≤ m(${P})`,`${m} ≤ ${M}`)}
    if(g.op==='span'){rel('תת-גרף פורש: אותם צמתים',`n(${X}) = n(${P})`,`${n} = ${N}`);rel('צלעות בתת-גרף פורש',`m(${X}) ≤ m(${P})`,`${m} ≤ ${M}`);rel('רכיבי קשירות בתת-גרף פורש',`c(${X}) ≥ c(${P})`,`${c} ≥ ${C}`);F.push({t:'כל גרף קשיר מכיל עץ פורש',r:'טענה 2.6',g:`${P} connected ⇒ exists spanning tree`,s:'',rel:1,text:1})}}
  /* degrees */
  const av=allV(g),aLo=av?dLo(av):null,aHi=av?dHi(av):null;
  add('סכום הדרגות','טענה 1.3','Σ deg(u) = 2m',`${ad!==null?V(ad)+'·'+n:'Σ deg(u)'} = 2·${m}`);
  if(av&&ad===null){add('סכום הדרגות כשכל הדרגות בטווח','טענה 1.3','n·min deg ≤ 2m ≤ n·max deg',`${aLo!==null?n+'·'+V(aLo)+' ≤ ':''}2·${m}${aHi!==null?' ≤ '+n+'·'+V(aHi):''}`);
    add('כל הדרגות בטווח','מההגדרה','min deg ≤ δ ≤ Δ ≤ max deg',rngTxt(aLo,`${dl} ≤ ${D}`,aHi))}
  add('דרגה מינימלית, ממוצעת ומקסימלית','מההגדרה','δ ≤ 2m / n ≤ Δ',`${dl} ≤ 2·${m} / ${n} ≤ ${D}`);
  add('דרגה מקסימלית בגרף פשוט','מההגדרה','Δ ≤ n − 1',`${D} ≤ ${n} − 1`);
  for(const v of O.filter(o=>o.t==='v'&&o.in===X&&o.q!=='all')){add(v.q==='ex'?'קיים צומת בדרגה נתונה':`הדרגה של ${v.name}`,'מההגדרה',`δ ≤ deg(${v.name}) ≤ Δ`,dEx(v)!==null||(dLo(v)===null&&dHi(v)===null)?`${dl} ≤ ${degOf(v)} ≤ ${D}`:[dHi(v)!==null?`${dl} ≤ ${V(dHi(v))}`:'',dLo(v)!==null?`${V(dLo(v))} ≤ ${D}`:''].filter(Boolean).join(',   '));
    if(dEx(v)===null&&(dLo(v)!==null||dHi(v)!==null))add(`טווח הדרגה של ${v.name}`,'נתון',`min ≤ deg(${v.name}) ≤ max`,rngTxt(dLo(v),`deg(${v.name})`,dHi(v)))}
  /* edges, components, trees */
  add('מספר הצלעות המרבי בגרף פשוט','מההגדרה','m ≤ n(n − 1) / 2',`${m} ≤ ${n}·(${n} − 1) / 2`);
  add('מספר הצלעות המזערי לפי רכיבי הקשירות','פרק 2','m ≥ n − c',`${m} ≥ ${n} − ${c}`);
  add('עץ: מספר הצלעות','משפט 2.5','m = n − 1',`${m} = ${n} − 1`,[['tr','y']]);
  add('עץ עם שני צמתים לפחות: יש עלה','טענה 2.3','δ = 1',`${dl} = ${V(1)}`,[['tr','y']]);
  add('מספר העצים המתויגים על אותם צמתים','משפט 2.9 (קיילי)','nⁿ⁻²',`${n} ^ (${n} − 2)`,[['tr','y']]);
  /* bipartite */
  add('דו-צדדי: אין מעגל באורך אי-זוגי','משפט 1.6','no odd cycle','',[['bp','y']]);
  add('דו-צדדי: שני צבעים מספיקים','משפט 1.6','χ ≤ 2',`${q('chi')} ≤ ${V(2)}`,[['bp','y']]);
  /* Euler, Hamilton */
  add('אוילרי, אם ורק אם כל הדרגות זוגיות','משפט 3.1','Eulerian ⇔ deg(u) even for all u',ad!==null?`Eulerian ⇔ ${V(ad)} even`:'',[['conn','y']]);
  add('תנאי אור: לכל שני צמתים לא שכנים (שלושה צמתים לפחות)','משפט 3.2','deg(u) + deg(w) ≥ n ⇒ Hamiltonian',`${ad!==null?V(ad)+' + '+V(ad):'deg(u) + deg(w)'} ≥ ${n}`);
  add('תנאי דירק להמילטוניות (שלושה צמתים לפחות)','משפט 3.3','δ ≥ n / 2 ⇒ Hamiltonian',`${dl} ≥ ${n} / 2`);
  /* matchings and covers */
  add('זיווג מכסה שני צמתים לכל צלע','מההגדרה','ν ≤ n / 2',`${q('nu')} ≤ ${n} / 2`);
  add('כיסוי בצלעות וזיווג (בלי צמתים מבודדים)','משפט 4.10','ρ = n − ν',`${q('rho')} = ${n} − ${q('nu')}`);
  add('קבוצה בלתי תלויה וכיסוי בצמתים','טענה 4.14','α + β = n',`${q('al')} + ${q('be')} = ${n}`);
  add('כיסוי בצמתים מול זיווג','טענה 4.15','β ≥ ν',`${q('be')} ≥ ${q('nu')}`);
  add('דו-צדדי: כיסוי בצמתים שווה לזיווג','משפט 4.16 (קניג)','β = ν',`${q('be')} = ${q('nu')}`,[['bp','y']]);
  for(const S of O.filter(o=>o.t==='s'&&o.in===X&&o.prop)){const k=S.k!==null?V(S.k):`|${S.name}|`,A=S.name;
    if(S.prop==='indep')add('קבוצה בלתי תלויה נתונה','מההגדרה',`α ≥ |${A}|`,`${q('al')} ≥ ${k}`);
    if(S.prop==='clique')add('קליקה נתונה','מההגדרה',`χ ≥ ω ≥ |${A}|`,`${q('chi')} ≥ ω${s} ≥ ${k}`);
    if(S.prop==='cover')add('כיסוי בצמתים נתון','מההגדרה',`β ≤ |${A}|`,`${q('be')} ≤ ${k}`);
    if(S.prop==='side'){add(`כל צלע נוגעת בצומת אחד של ${A}`,'מההגדרה',`Σ deg(u) = m, u ∈ ${A}`,`Σ deg(u) = ${m}, u ∈ ${A}`,[['bp','y']]);
      add(`תנאי הול לזיווג שמכסה את ${A}`,'משפט 4.7 (הול)',`|Γ(X)| ≥ |X| for all X ⊆ ${A}  ⇔  ν = |${A}|`,`|Γ(X)| ≥ |X| for all X ⊆ ${A}  ⇔  ${q('nu')} = ${k}`,[['bp','y']]);
      add('זיווג מושלם בגרף דו-צדדי','מסקנה 4.8',`perfect matching ⇔ |${A}| = n − |${A}| and Hall`,`${k} = ${n} − ${k}`,[['bp','y']])}}
  /* planarity */
  add('נוסחת אוילר','משפט 5.3','f = m − n + 2',`${q('f')} = ${m} − ${n} + 2`,[['pl','y'],['conn','y']]);
  add('נוסחת אוילר לגרף מישורי כלשהו','הכללה של 5.3','f = m − n + c + 1',`${q('f')} = ${m} − ${n} + ${c} + 1`,[['pl','y']]);
  add('חסם הצלעות בגרף מישורי (שלושה צמתים לפחות)','מסקנה 5.4','m ≤ 3n − 6',`${m} ≤ 3·${n} − 6`,[['pl','y']]);
  add('כל פאה תחומה בשלוש צלעות לפחות','פרק 5','3f ≤ 2m',`3·${q('f')} ≤ 2·${m}`,[['pl','y']]);
  add('סכום אורכי הפאות','פרק 5','Σ len(face) = 2m',`Σ len(face) = 2·${m}`,[['pl','y']]);
  add('בגרף מישורי יש צומת מדרגה קטנה','מסקנה 5.5','δ ≤ 5',`${dl} ≤ ${V(5)}`,[['pl','y']]);
  add('משפט ארבעת הצבעים','משפט 6.3','χ ≤ 4',`${q('chi')} ≤ ${V(4)}`,[['pl','y']]);
  add('לא מישורי: מכיל העדנה של K₅ או של K₃,₃','משפט 5.8 (קורטובסקי)','contains a subdivision of K₅ or K₃,₃','',[['pl','n']]);
  add('לא מישורי: גדלים מזעריים','משפט 5.8','n ≥ 5,  m ≥ 9',`${n} ≥ 5,  ${m} ≥ 9`,[['pl','n']]);
  /* colouring */
  add('חסם על מספר הצביעה','פרק 6, שאלה 1','χ ≤ Δ + 1',`${q('chi')} ≤ ${D} + 1`);
  add('משפט ברוקס (פרט לרכיב שהוא גרף מלא או מעגל אי-זוגי)','משפט 6.2','χ ≤ Δ',`${q('chi')} ≤ ${D}`);
  add('כל צבע הוא קבוצה בלתי תלויה','מההגדרה','n ≤ χ·α',`${n} ≤ ${q('chi')}·${q('al')}`);
  /* status of each formula: applies, hidden (a needed property is given as the opposite), or conditional (unknown) */
  const st=f=>{if(!f.need)return 'on';let u=false;for(const [k,w] of f.need){const p=prop(g,k);if(p==='u')u=true;else if(p!==w)return 'hide'}return u?'hide':'on'};
  const cond=f=>f.need.filter(([k])=>prop(g,k)==='u').map(([k,w])=>(w==='n'?'לא ':'')+PROPS[k]).join(' ו');
  const card=f=>{const z=st(f);return `<article class="f${z==='if'?' off':''}${f.rel?' rel':''}"><div class="fh"><b>${f.t}</b><span class="ref">${f.r}</span>${z==='if'?`<span class="need">אם ${X} ${cond(f)}</span>`:''}</div><div class="fx gen">${f.g}</div>${f.s&&f.s.includes('class="qv"')?`<div class="fx qsub">${f.s}</div>`:''}</article>`};
  const title=g.op?`${OPS[g.op][0]}${g.arg?' '+g.arg:''} ${g.op==='compl'||g.op==='comp'||g.op==='span'?'של':'מתוך'} ${g.src}`:'הגרף הנתון';
  const vis=F.filter(f=>st(f)!=='hide');
  return `<h3 class="gt"><span class="name">${X}</span> ${title}</h3>${vis.filter(f=>st(f)==='on').map(card).join('')}${vis.filter(f=>st(f)==='if').map(card).join('')}`}
function renderSheet(){
  document.getElementById('qsheet').innerHTML=graphs().map(sheetFor).join('');
  const L=[];for(const g of graphs()){const s=sub(g);for(const k in SYM){if(k==='f'&&g.pl==='n')continue;L.push([SYM[k]+s,DEF[k]+' של '+g.name,val(g,k)])}}
  for(const o of O){if(o.t==='v'&&o.q!=='all')L.push([`deg(${o.name})`,`הדרגה של ${o.name} ב־${o.in}`,dEx(o)!==null?dEx(o):dLo(o)!==null||dHi(o)!==null?`${dLo(o)??'?'} … ${dHi(o)??'?'}`:null]);if(o.t==='s')L.push([`|${o.name}|`,`מספר הצמתים ב־${o.name}`,o.k])}
  L.push(['ω','גודל קליקה מקסימלית',null],['Γ(X)','קבוצת השכנים של צומתי X',null]);
  document.getElementById('qlegend').innerHTML=L.map(([k,d,v])=>`<div class="${v!==null?'given':''}"><dt class="fx">${k}${v!==null?' = '+v:''}</dt><dd>${d}</dd></div>`).join('')}
document.addEventListener('input',ev=>{const t=ev.target,i=t.dataset.i,k=t.dataset.k;if(i===undefined||!t.closest('.qb'))return;const o=O[i];
  o[k]=t.type==='checkbox'?t.checked:t.type==='number'?(t.value===''?null:Number(t.value)):t.value;
  if(['op','src','in','arg','dm'].includes(k)){if(o.t==='g'&&o.op)ensureArg(o);O.filter(g=>g.t==='g'&&g.op).forEach(ensureArg);renderObjs()}
  renderSheet()});
document.addEventListener('click',ev=>{if(!ev.target.closest||!ev.target.closest('.qb'))return;const a=ev.target.closest('[data-add]'),d=ev.target.closest('[data-del]'),mo=ev.target.closest('[data-more]');
  if(mo){const o=O[Number(mo.dataset.more)];o.more=!o.more}
  else if(d){removeObj(d.dataset.del)}
  else if(a){const t=a.dataset.add,last=graphs()[graphs().length-1].name;
    if(t==='v')O.push({t:'v',name:fresh('v'),in:last,q:'one',d:null,cut:false});
    if(t==='e')O.push({t:'e',name:fresh('e'),in:last,bridge:false});
    if(t==='s')O.push({t:'s',name:fresh('s'),in:last,k:null,prop:''});
    if(t==='g'){const g=newG(fresh('g'),{op:'compl',src:last,arg:null});O.push(g);ensureArg(g)}}
  else return;renderObjs();renderSheet()});
return{render(){
  document.getElementById('conds').innerHTML=`<div class="qb"><div class="colhead"><h2>נתוני השאלה</h2><span class="lab">אובייקטים, פעולות וערכים</span></div><div id="qobjs" class="qlist"></div>
  <div class="qbox"><div class="lab">הוסף אובייקט</div><div class="addrow"><button class="addb" data-add="v">+ צומת</button><button class="addb" data-add="e">+ צלע</button><button class="addb" data-add="s">+ קבוצת צמתים</button><button class="addb" data-add="g">+ גרף מפעולה</button></div>
  <p class="hint">גרף מפעולה נוצר מגרף קיים, ואפשר להפעיל עליו פעולה נוספת. הכמת של צומת קובע לאן הדרגה שלו נכנסת בנוסחאות.</p></div></div>`;
  document.getElementById('main').innerHTML=`<div class="hero qhero"><p>דף הנוסחאות של האובייקטים שבשאלה, בלי הגבלה על מספר הצמתים. הערכים הנתונים מוצבים <b>בצבע</b>, ומה שלא נתון נשאר כסמל.</p><p>ערך שמצאת בעצמך אפשר למלא בצד ימין, והוא יוצב בכל שאר הנוסחאות.</p></div><div class="qgrid" id="qsheet"></div>`;
  document.getElementById('card').innerHTML=`<div class="cardhead"><h2>מקרא הסמלים</h2></div><dl id="qlegend" class="qleg"></dl><p class="hint">סמל צבוע הוא נתון. השאר לא נתונים, ומוצגים בנוסחאות לפי ההגדרה שלהם.</p>`;
  renderObjs();renderSheet()}};
})();
