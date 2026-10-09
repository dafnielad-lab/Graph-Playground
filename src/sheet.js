/* ---------- formula-sheet mode: objects, operations, live substitution ---------- */
const SHEET=(()=>{

const V=x=>`<span class="qv">${x}</span>`;
/* objects of the question, in order; a derived graph may only use objects defined above it */
let O=[{t:'g',name:'G',n:10,m:null,c:1,pl:true,tr:false},
       {t:'v',name:'v',in:'G',q:'one',d:3},
       {t:'g',name:'H',op:'delv',src:'G',arg:'v',n:null,m:null,c:2,pl:true,tr:false}];
const NAMES={v:['v','u','w','x','y','z'],e:['e','e₂','e₃','e₄'],s:['S','T','A','B'],g:['H','K','L','M','N']};
const OPS={delv:['הסרת הצומת','v'],dele:['הסרת הצלע','e'],adde:['הוספת צלע',null],compl:['המשלים',null],ind:['תת-גרף מושרה על','s']};
const by=n=>O.find(o=>o.name===n),graphs=()=>O.filter(o=>o.t==='g');
const fresh=t=>NAMES[t].find(n=>!by(n))||NAMES[t][0]+O.length;
function ensureArg(g){const need=OPS[g.op][1];if(!need){g.arg=null;return}
  const cur=by(g.arg);if(cur&&cur.t===need&&cur.in===g.src)return;
  let a=O.find(o=>o.t===need&&o.in===g.src&&O.indexOf(o)<O.indexOf(g));
  if(!a){a=need==='v'?{t:'v',name:fresh('v'),in:g.src,q:'one',d:null}:need==='e'?{t:'e',name:fresh('e'),in:g.src}:{t:'s',name:fresh('s'),in:g.src,k:null,prop:''};O.splice(O.indexOf(g),0,a)}
  g.arg=a.name}
function removeObj(name){const dep=O.filter(o=>o.in===name||o.src===name||o.arg===name).map(o=>o.name);O=O.filter(o=>o.name!==name);dep.forEach(removeObj)}
const opt=(list,cur)=>list.map(([v,l])=>`<option value="${v}" ${v===cur?'selected':''}>${l}</option>`).join('');
const num=(i,k,val,lab)=>`<label class="cell">${lab}<input type="number" min="0" data-i="${i}" data-k="${k}" value="${val===null?'':val}" placeholder="?" id="f${i}${k}"></label>`;
function renderObjs(){
  document.getElementById('qobjs').innerHTML=O.map((o,i)=>{const gs=opt(graphs().filter(g=>o.t!=='g'||O.indexOf(g)<i).map(g=>[g.name,g.name]),o.t==='g'?o.src:o.in),x=o.name==='G'?'':`<button class="x" data-del="${o.name}" aria-label="הסר את ${o.name}">×</button>`;
    if(o.t==='g')return `<div class="qbox"><div class="qrow"><span class="name">${o.name}</span>${o.op?`<span>=</span><select data-i="${i}" data-k="op" id="f${i}op" aria-label="פעולה">${opt(Object.entries(OPS).map(([k,v])=>[k,v[0]]),o.op)}</select>${o.arg?`<select data-i="${i}" data-k="arg" id="f${i}arg" aria-label="על מה">${opt(O.filter(a=>a.t===OPS[o.op][1]&&a.in===o.src&&O.indexOf(a)<i).map(a=>[a.name,a.name]),o.arg)}</select>`:''}<span>מתוך</span><select data-i="${i}" data-k="src" id="f${i}src" aria-label="גרף מקור">${gs}</select>`:'<span>הגרף הנתון</span>'}${x}</div>
      <div class="qrow">${num(i,'n',o.n,'צמתים')}${num(i,'m',o.m,'צלעות')}${num(i,'c',o.c,'רכיבים')}<label class="cell">מישורי<input type="checkbox" data-i="${i}" data-k="pl" id="f${i}pl" ${o.pl?'checked':''}></label><label class="cell">עץ<input type="checkbox" data-i="${i}" data-k="tr" id="f${i}tr" ${o.tr?'checked':''}></label></div></div>`;
    if(o.t==='v')return `<div class="qbox"><div class="qrow"><span class="name v">${o.name}</span><select data-i="${i}" data-k="q" id="f${i}q" aria-label="כמת">${opt([['one','צומת מסוים'],['all','כל צומת'],['ex','קיים צומת']],o.q)}</select><span>ב־</span><select data-i="${i}" data-k="in" id="f${i}in" aria-label="בגרף">${gs}</select>${x}</div><div class="qrow">${num(i,'d',o.d,'דרגה')}</div></div>`;
    if(o.t==='e')return `<div class="qbox"><div class="qrow"><span class="name v">${o.name}</span><span>צלע ב־</span><select data-i="${i}" data-k="in" id="f${i}in" aria-label="בגרף">${gs}</select>${x}</div></div>`;
    return `<div class="qbox"><div class="qrow"><span class="name v">${o.name}</span><span>קבוצת צמתים ב־</span><select data-i="${i}" data-k="in" id="f${i}in" aria-label="בגרף">${gs}</select>${x}</div><div class="qrow">${num(i,'k',o.k,'גודל')}<select data-i="${i}" data-k="prop" id="f${i}prop" aria-label="תכונה">${opt([['','בלי תכונה נוספת'],['indep','בלתי תלויה'],['clique','קליקה']],o.prop)}</select></div></div>`}).join('')}
/* symbol of a graph quantity: the given value in blue, otherwise the symbol (with the graph's name unless it is G) */
const sub=g=>g.name==='G'?'':`<sub>${g.name}</sub>`;
const sy=(g,k)=>g[k]!==null&&g[k]!==undefined?V(g[k]):k+sub(g);
const allDeg=g=>{const v=O.find(o=>o.t==='v'&&o.in===g.name&&o.q==='all'&&o.d!==null);return v?v.d:null};
const degOf=v=>v.d!==null?V(v.d):`deg(${v.name})`;
function sheetFor(g){
  const n=sy(g,'n'),m=sy(g,'m'),c=sy(g,'c'),s=sub(g),ad=allDeg(g),D=ad!==null?V(ad):'Δ'+s,dl=ad!==null?V(ad):'δ'+s,conn=g.c===1||g.tr,F=[];
  const src=g.op?by(g.src):null;
  if(src){const N=sy(src,'n'),M=sy(src,'m'),C=sy(src,'c'),a=by(g.arg),rel=(t,gn,st)=>F.push({t,r:'מהפעולה',g:gn,s:st,rel:1}),H=g.name,X=src.name;
    if(g.op==='delv'){rel('צמתים אחרי הסרת צומת',`n(${H}) = n(${X}) − 1`,`${n} = ${N} − 1`);rel('צלעות אחרי הסרת צומת',`m(${H}) = m(${X}) − deg(${a.name})`,`${m} = ${M} − ${degOf(a)}`)}
    if(g.op==='dele'){rel('צמתים אחרי הסרת צלע',`n(${H}) = n(${X})`,`${n} = ${N}`);rel('צלעות אחרי הסרת צלע',`m(${H}) = m(${X}) − 1`,`${m} = ${M} − 1`);rel('רכיבי קשירות אחרי הסרת צלע',`c(${X}) ≤ c(${H}) ≤ c(${X}) + 1`,`${C} ≤ ${c} ≤ ${C} + 1`)}
    if(g.op==='adde'){rel('צלעות אחרי הוספת צלע',`m(${H}) = m(${X}) + 1`,`${m} = ${M} + 1`);rel('רכיבי קשירות אחרי הוספת צלע',`c(${X}) − 1 ≤ c(${H}) ≤ c(${X})`,`${C} − 1 ≤ ${c} ≤ ${C}`)}
    if(g.op==='compl'){rel('צמתים במשלים',`n(${H}) = n(${X})`,`${n} = ${N}`);rel('צלעות בגרף ובמשלים',`m(${X}) + m(${H}) = n(n − 1) / 2`,`${M} + ${m} = ${N}·(${N} − 1) / 2`);const xd=allDeg(src);rel('דרגה במשלים',`deg in ${H} = n − 1 − deg in ${X}`,`deg in ${H} = ${N} − 1 − ${xd!==null?V(xd):'deg in '+X}`)}
    if(g.op==='ind'){const k=a.k!==null?V(a.k):`|${a.name}|`;rel('צמתים בתת-גרף מושרה',`n(${H}) = |${a.name}|`,`${n} = ${k}`);rel('צלעות בתת-גרף מושרה',`m(${H}) ≤ m(${X})`,`${m} ≤ ${M}`);
      if(a.prop==='indep')rel('מושרה על קבוצה בלתי תלויה',`m(${H}) = 0`,`${m} = ${V(0)}`);if(a.prop==='clique')rel('מושרה על קליקה',`m(${H}) = |${a.name}|(|${a.name}| − 1) / 2`,`${m} = ${k}·(${k} − 1) / 2`)}}
  F.push({t:'סכום הדרגות',r:'טענה 1.3',g:'Σ deg(u) = 2m',s:`${ad!==null?V(ad)+'·'+n:'Σ deg(u)'} = 2·${m}`},
    {t:'דרגה מינימלית, ממוצעת ומקסימלית',r:'מההגדרה',g:'δ ≤ 2m / n ≤ Δ',s:`${dl} ≤ 2·${m} / ${n} ≤ ${D}`});
  for(const v of O.filter(o=>o.t==='v'&&o.in===g.name&&o.q!=='all'))F.push({t:v.q==='ex'?'קיים צומת בדרגה נתונה':`הדרגה של ${v.name}`,r:'מההגדרה',g:`δ ≤ deg(${v.name}) ≤ Δ`,s:`δ${s} ≤ ${degOf(v)} ≤ Δ${s}`});
  for(const S of O.filter(o=>o.t==='s'&&o.in===g.name&&o.prop)){const k=S.k!==null?V(S.k):`|${S.name}|`;
    if(S.prop==='indep')F.push({t:'קבוצה בלתי תלויה נתונה',r:'מההגדרה',g:`α ≥ |${S.name}|`,s:`α${s} ≥ ${k}`});
    else F.push({t:'קליקה נתונה',r:'מההגדרה',g:`χ ≥ ω ≥ |${S.name}|`,s:`χ${s} ≥ ω${s} ≥ ${k}`})}
  F.push({t:'מספר הצלעות המרבי בגרף פשוט',r:'מההגדרה',g:'m ≤ n(n − 1) / 2',s:`${m} ≤ ${n}·(${n} − 1) / 2`},
    {t:'מספר הצלעות המזערי לפי רכיבי הקשירות',r:'פרק 2',g:'m ≥ n − c',s:`${m} ≥ ${n} − ${c}`},
    {t:'חסם על מספר הצביעה',r:'פרק 6, שאלה 1',g:'χ ≤ Δ + 1',s:`χ${s} ≤ ${D} + 1`},
    {t:'עץ: מספר הצלעות',r:'משפט 2.5',g:'m = n − 1',s:`${m} = ${n} − 1`,need:g.name+' עץ',ok:g.tr},
    {t:'נוסחת אוילר',r:'משפט 5.3',g:'f = m − n + 2',s:`f${s} = ${m} − ${n} + 2`,need:g.name+' מישורי וקשיר',ok:g.pl&&conn},
    {t:'חסם הצלעות בגרף מישורי (שלושה צמתים לפחות)',r:'מסקנה 5.4',g:'m ≤ 3n − 6',s:`${m} ≤ 3·${n} − 6`,need:g.name+' מישורי',ok:g.pl},
    {t:'סכום אורכי הפאות',r:'פרק 5',g:'Σ len(face) = 2m',s:`Σ len(face) = 2·${m}`,need:g.name+' מישורי',ok:g.pl});
  const card=f=>{const off=f.need&&!f.ok;return `<article class="f${off?' off':''}${f.rel?' rel':''}"><div class="fh"><b>${f.t}</b><span class="ref">${f.r}</span>${off?`<span class="need">חסר: ${f.need}</span>`:''}</div><div class="fx gen">${f.g}</div>${off?'':(f.s.includes('class="qv"')?`<div class="fx qsub">${f.s}</div>`:'<div class="same">אין נתון להצבה בנוסחה הזו</div>')}</article>`};
  const title=g.op?`${g.name} = ${OPS[g.op][0]}${g.arg?' '+g.arg:''} מתוך ${g.src}`:'G, הגרף הנתון';
  return `<h3 class="gt"><span class="name">${g.name}</span> ${title}</h3>${F.filter(f=>!f.need||f.ok).map(card).join('')}${F.filter(f=>f.need&&!f.ok).map(card).join('')}`}
function renderSheet(){
  document.getElementById('qsheet').innerHTML=graphs().map(sheetFor).join('');
  const L=[];for(const g of graphs()){const s=sub(g),ad=allDeg(g);L.push(['n'+s,'מספר הצמתים של '+g.name,g.n],['m'+s,'מספר הצלעות של '+g.name,g.m],['c'+s,'מספר רכיבי הקשירות של '+g.name,g.c],['Δ'+s,'הדרגה המקסימלית ב־'+g.name,ad],['δ'+s,'הדרגה המינימלית ב־'+g.name,ad],['χ'+s,'מספר הצביעה של '+g.name,null]);if(g.pl)L.push(['f'+s,'מספר הפאות של '+g.name+' בשיכון מישורי',null])}
  for(const o of O){if(o.t==='v'&&o.q!=='all')L.push([`deg(${o.name})`,`הדרגה של ${o.name} ב־${o.in}`,o.d]);if(o.t==='s')L.push([`|${o.name}|`,`מספר הצמתים ב־${o.name}`,o.k])}
  document.getElementById('qlegend').innerHTML=L.map(([k,d,v])=>`<div class="${v!==null?'given':''}"><dt class="fx">${k}${v!==null?' = '+v:''}</dt><dd>${d}</dd></div>`).join('')}
document.addEventListener('input',ev=>{const t=ev.target,i=t.dataset.i,k=t.dataset.k;if(i===undefined||!t.closest('.qb'))return;const o=O[i];
  o[k]=t.type==='checkbox'?t.checked:t.type==='number'?(t.value===''?null:Number(t.value)):t.value;
  if(['op','src','in','arg'].includes(k)){if(o.t==='g'&&o.op)ensureArg(o);O.filter(g=>g.t==='g'&&g.op).forEach(ensureArg);renderObjs()}
  renderSheet()});
document.addEventListener('click',ev=>{if(!ev.target.closest||!ev.target.closest('.qb'))return;const a=ev.target.closest('[data-add]'),d=ev.target.closest('[data-del]');
  if(d){removeObj(d.dataset.del)}
  else if(a){const t=a.dataset.add,last=graphs()[graphs().length-1].name;
    if(t==='v')O.push({t:'v',name:fresh('v'),in:last,q:'one',d:null});
    if(t==='e')O.push({t:'e',name:fresh('e'),in:last});
    if(t==='s')O.push({t:'s',name:fresh('s'),in:last,k:null,prop:''});
    if(t==='g'){const g={t:'g',name:fresh('g'),op:'compl',src:last,arg:null,n:null,m:null,c:null,pl:false,tr:false};O.push(g);ensureArg(g)}}
  else return;renderObjs();renderSheet()});
return{render(){
  document.getElementById('conds').innerHTML=`<div class="qb"><div class="colhead"><h2>נתוני השאלה</h2><span class="lab">אובייקטים, פעולות וערכים</span></div><div id="qobjs" class="qlist"></div>
  <div class="qbox"><div class="lab">הוסף אובייקט</div><div class="addrow"><button class="addb" data-add="v">+ צומת</button><button class="addb" data-add="e">+ צלע</button><button class="addb" data-add="s">+ קבוצת צמתים</button><button class="addb" data-add="g">+ גרף מפעולה</button></div>
  <p class="hint">גרף מפעולה נוצר מגרף קיים, ואפשר להפעיל עליו פעולה נוספת. הכמת של צומת קובע לאן הדרגה שלו נכנסת בנוסחאות.</p></div></div>`;
  document.getElementById('main').innerHTML=`<div class="hero qhero"><p>דף הנוסחאות של האובייקטים שבשאלה, בלי הגבלה על מספר הצמתים. הערכים הנתונים מוצבים <b>בצבע</b>, ומה שלא נתון נשאר כסמל.</p><p>הדף לא פותר: המטרה היא לזהות לבד אילו נוסחאות אפשר לחבר כדי למצוא עוד נתונים.</p></div><div class="qgrid" id="qsheet"></div>`;
  document.getElementById('card').innerHTML=`<div class="cardhead"><h2>מקרא הסמלים</h2></div><dl id="qlegend" class="qleg"></dl><p class="hint">סמל צבוע הוא נתון. השאר לא נתונים, ומוצגים בנוסחאות לפי ההגדרה שלהם.</p>`;
  renderObjs();renderSheet()}};
})();
