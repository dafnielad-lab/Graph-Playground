/* ---------- the cardinalities playground: sets built from known sets by constructions, and the cardinality that follows from the structure ---------- */
const CARD=(()=>{
const esc=s=>String(s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
/* a cardinal is either finite, {t:'f', n: BigInt, or null when too large to write}, or infinite, {t:'b', k}: ℶ_k, where ℶ_0 = ℵ0 and ℶ_(k+1) = 2^ℶ_k.
   The atoms are at most the continuum and every construction here keeps cardinals inside this family. */
const F=n=>({t:'f',n:n===null?null:BigInt(n)}),B=k=>({t:'b',k}),ALEPH=B(0);
const fin=c=>c.t==='f',zero=c=>fin(c)&&c.n===0n,one=c=>fin(c)&&c.n===1n,LIM=3400;
const bits=n=>n.toString(2).length;
const add=(x,y)=>fin(x)&&fin(y)?(x.n===null||y.n===null?F(null):F(x.n+y.n)):B(Math.max(fin(x)?0:x.k,fin(y)?0:y.k));
const mul=(x,y)=>zero(x)||zero(y)?F(0):fin(x)&&fin(y)?(x.n===null||y.n===null||bits(x.n)+bits(y.n)>LIM?F(null):F(x.n*y.n)):B(Math.max(fin(x)?0:x.k,fin(y)?0:y.k));
/* base ^ exp: the number of functions from a set of size exp to a set of size base */
function pow(b,e){if(zero(e))return F(1);if(zero(b))return F(0);if(one(b))return F(1);
  if(fin(b)&&fin(e)){if(b.n===null||e.n===null||e.n>BigInt(LIM)||Number(e.n)*(bits(b.n)-1)>LIM)return F(null);return F(b.n**e.n)}
  if(fin(b))return B(e.k+1);if(fin(e))return B(b.k);return B(e.k<b.k?b.k:e.k+1)}
const cmp=(x,y)=>fin(x)&&fin(y)?(x.n===null||y.n===null?(x.n===y.n?null:x.n===null?1:-1):x.n<y.n?-1:x.n>y.n?1:0):fin(x)?-1:fin(y)?1:x.k-y.k;
const same=(x,y)=>cmp(x,y)===0;
/* typesetting */
const sup=(b,e)=>`${b}<sup>${e}</sup>`,par=s=>/[ <]/.test(s)?`(${s})`:s;
const fmt=c=>fin(c)?(c.n===null?'<i>N</i>':c.n.toString().length>40?c.n.toString().slice(0,6)+'…  ('+c.n.toString().length+' digits)':c.n.toString()):c.k===0?'ℵ₀':sup('2',fmt(B(c.k-1)));
const word=c=>fin(c)?(zero(c)?'הקבוצה הריקה':c.n===null?'סופית, גדולה מכדי לכתוב':'סופית'):c.k===0?'בת־מנייה':c.k===1?'עוצמת הרצף':'גדולה מעוצמת הרצף';

/* ---------- the kinds of sets ---------- */
const NAMES='ABCDEFGHJKLM';
const KINDS={fin:{l:'קבוצה סופית בגודל נתון',n:true,sym:(a,b,n)=>n===0?'∅':n===1?'{1}':n===2?'{1, 2}':`{1, …, ${n}}`},
  N:{l:'הטבעיים',sym:()=>'ℕ'},Z:{l:'השלמים',sym:()=>'ℤ'},Q:{l:'הרציונליים',sym:()=>'ℚ'},R:{l:'הממשיים',sym:()=>'ℝ'},I:{l:'הקטע הפתוח בין אפס לאחת',sym:()=>'(0, 1)'},
  sum:{l:'איחוד זר של שתי קבוצות',src:2,sym:(a,b)=>`${a} ⊔ ${b}`},prod:{l:'מכפלה קרטזית',src:2,sym:(a,b)=>`${a} × ${b}`},
  fun:{l:'כל הפונקציות מקבוצה לקבוצה',src:2,lab:['מ־','אל'],sym:(a,b)=>`${a} → ${b}`},
  seq:{l:'סדרות אינסופיות של איברי הקבוצה',src:1,sym:a=>`ℕ → ${a}`},tup:{l:'סדרות באורך נתון',src:1,n:true,sym:(a,b,n)=>sup(par(a),n)},
  star:{l:'כל הסדרות הסופיות',src:1,sym:a=>sup(par(a),'*')},pow:{l:'קבוצת החזקה',src:1,sym:a=>`P(${a})`},pfin:{l:'כל התת־קבוצות הסופיות',src:1,sym:a=>`P<sub>fin</sub>(${a})`}};
const nOf=s=>Math.max(0,Math.min(1000000,Math.floor(Number(s.n))||0));
/* ---------- the cardinality of a set, with the steps that lead to it. Each step is a formula and the reason for it ---------- */
const maxWhy='כשלפחות אחת מהעוצמות אינסופית, התוצאה היא הגדולה מהשתיים';
function powSteps(b,e){const fb=fmt(b),fe=fmt(e),r=pow(b,e),S=[];
  if(zero(e))S.push([`${sup(par(fb),'0')} = 1`,'מקבוצה ריקה יש פונקציה אחת בלבד, הפונקציה הריקה']);
  else if(zero(b))S.push([`${sup('0',fe)} = 0`,'אין פונקציה מקבוצה לא ריקה אל הקבוצה הריקה']);
  else if(one(b))S.push([`${sup('1',fe)} = 1`,'אל קבוצה של איבר אחד יש פונקציה אחת בלבד']);
  else if(fin(b)&&fin(e))S.push([`${sup(par(fb),fe)} = ${fmt(r)}`,'חזקה של מספרים טבעיים']);
  else if(fin(b)&&b.n===2n)S.push([`${fmt(r)}`,fe==='ℵ₀'?'אין מה לפשט: זו עוצמת הרצף, עוצמת קבוצת החזקה של הטבעיים':'אין מה לפשט: זו עוצמת קבוצת החזקה, ולפי משפט קנטור היא גדולה ממש מהמעריך']);
  else if(fin(b)){const k=fmt(e);S.push([`${sup('2',k)} ≤ ${sup(par(fb),k)} ≤ ${sup(par(sup('2',k)),k)} = ${sup('2',`${k} · ${k}`)} = ${sup('2',k)}`,`הבסיס נמצא בין 2 לבין ${sup('2',k)}, ומכפלת עוצמה אינסופית בעצמה שווה לה`]);S.push([`${sup(par(fb),k)} = ${fmt(r)}`,'קנטור–ברנשטיין: חסם תחתון וחסם עליון שווים'])}
  else if(fin(e))S.push([`${sup(par(fb),fe)} = ${e.n===1n?fb:`${fb} · … · ${fb}`} = ${fmt(r)}`,e.n===1n?'חזקה ראשונה':'מכפלה של עוצמה אינסופית בעצמה, מספר סופי של פעמים, שווה לה']);
  else if(b.k>=1){const lo=fmt(B(b.k-1)),mx=fmt(B(Math.max(b.k-1,e.k)));S.push([`${sup(par(fb),fe)} = ${sup('2',`${lo} · ${fe}`)}`,'חזקה של חזקה היא חזקה במכפלת המעריכים']);S.push([`${sup('2',`${lo} · ${fe}`)} = ${sup('2',mx)}${fmt(r)===sup('2',mx)?'':' = '+fmt(r)}`,`${lo} · ${fe} = ${mx}: ${maxWhy}`])}
  else{S.push([`${sup('2',fe)} ≤ ${sup(par(fb),fe)} ≤ ${sup(par(sup('2',fb)),fe)} = ${sup('2',`${fb} · ${fe}`)} = ${sup('2',fe)}`,`הבסיס נמצא בין 2 לבין ${sup('2',fb)}, ו־${fb} · ${fe} = ${fe}`]);S.push([`${sup(par(fb),fe)} = ${fmt(r)}`,'קנטור–ברנשטיין: חסם תחתון וחסם עליון שווים'])}
  return S}
function cardOf(s,ca,cb,nm,na,nb){const k=s.kind,X=`|${nm}|`,S=[];let c;
  if(k==='fin'){c=F(nOf(s));S.push([`${X} = ${fmt(c)}`,'נתון'])}
  else if(k==='N'){c=ALEPH;S.push([`${X} = ℵ₀`,'ההגדרה של ℵ₀'])}
  else if(k==='Z'){c=ALEPH;S.push([`${X} = ℵ₀`,'השלמים בני־מנייה: אפשר לסדר אותם בסדרה 0, 1, −1, 2, −2, …'])}
  else if(k==='Q'){c=ALEPH;S.push([`ℵ₀ ≤ ${X} ≤ |ℤ × ℕ| = ℵ₀ · ℵ₀ = ℵ₀`,'כל רציונלי הוא שבר של שלם וטבעי, והטבעיים מוכלים ברציונליים']);S.push([`${X} = ℵ₀`,'קנטור–ברנשטיין'])}
  else if(k==='R'||k==='I'){c=B(1);S.push([`${X} = ${fmt(c)}`,k==='R'?'עוצמת הרצף: הממשיים שקולים לקבוצת החזקה של הטבעיים':'קטע פתוח שקול לכל הממשיים, למשל דרך הפונקציה tan'])}
  else if(k==='sum'){c=add(ca,cb);S.push([`${X} = |${na}| + |${nb}| = ${fmt(ca)} + ${fmt(cb)}`,'איחוד זר: העוצמה היא סכום העוצמות']);S.push([`${fmt(ca)} + ${fmt(cb)} = ${fmt(c)}`,fin(c)?'חיבור של מספרים טבעיים':maxWhy])}
  else if(k==='prod'){c=mul(ca,cb);S.push([`${X} = |${na}| · |${nb}| = ${fmt(ca)} · ${fmt(cb)}`,'מכפלה קרטזית: העוצמה היא מכפלת העוצמות']);
    S.push([`${fmt(ca)} · ${fmt(cb)} = ${fmt(c)}`,zero(c)?'מכפלה בקבוצה ריקה היא ריקה':fin(c)?'כפל של מספרים טבעיים':'שתי העוצמות שונות מאפס, ו'+maxWhy])}
  else if(k==='fun'){c=pow(cb,ca);S.push([`${X} = ${sup(`|${nb}|`,`|${na}|`)} = ${sup(par(fmt(cb)),fmt(ca))}`,'מספר הפונקציות: עוצמת הטווח בחזקת עוצמת התחום']);S.push(...powSteps(cb,ca))}
  else if(k==='seq'){c=pow(ca,ALEPH);S.push([`${X} = ${sup(`|${na}|`,'|ℕ|')} = ${sup(par(fmt(ca)),'ℵ₀')}`,'סדרה אינסופית היא פונקציה מהטבעיים אל הקבוצה']);S.push(...powSteps(ca,ALEPH))}
  else if(k==='tup'){const n=F(nOf(s));c=pow(ca,n);S.push([`${X} = ${sup(`|${na}|`,fmt(n))} = ${sup(par(fmt(ca)),fmt(n))}`,'סדרה באורך n היא בחירה של איבר לכל אחד מ־n המקומות']);S.push(...powSteps(ca,n))}
  else if(k==='pow'){c=pow(F(2),ca);S.push([`${X} = ${sup('2',`|${na}|`)} = ${sup('2',fmt(ca))}`,'תת־קבוצה היא בחירה, לכל איבר, אם הוא בפנים או בחוץ']);if(fin(ca))S.push([`${sup('2',fmt(ca))} = ${fmt(c)}`,'חזקה של מספרים טבעיים']);else S.push([`${sup('2',fmt(ca))} > ${fmt(ca)}`,'משפט קנטור: קבוצת החזקה גדולה ממש מהקבוצה'])}
  else if(k==='star'){const a=fmt(ca);if(zero(ca)){c=F(1);S.push([`${X} = 1`,'מעל קבוצה ריקה יש רק הסדרה הריקה'])}
    else if(fin(ca)){c=ALEPH;S.push([`${X} = Σ ${sup(par(a),'n')},   n = 0, 1, 2, …`,'איחוד זר לפי אורך הסדרה']);S.push([`${X} = ℵ₀`,'איחוד בן־מנייה של קבוצות סופיות לא ריקות וזרות הוא בן־מנייה'])}
    else{c=ca;S.push([`${X} = Σ ${sup(par(a),'n')},   n = 0, 1, 2, …`,'איחוד זר לפי אורך הסדרה']);S.push([`${sup(par(a),'n')} = ${a},   n ≥ 1`,'מכפלה של עוצמה אינסופית בעצמה, מספר סופי של פעמים, שווה לה']);S.push([`${X} = 1 + ℵ₀ · ${a} = ${a}`,'ℵ₀ מחוברים שכל אחד מהם '+a+', ו'+maxWhy])}}
  else if(k==='pfin'){const a=fmt(ca);if(fin(ca)){c=pow(F(2),ca);S.push([`${X} = ${sup('2',a)} = ${fmt(c)}`,'בקבוצה סופית כל תת־קבוצה סופית'])}
    else{c=ca;S.push([`${a} ≤ ${X}`,'לכל איבר יש יחידון, ואלה תת־קבוצות סופיות שונות']);S.push([`${X} ≤ |${sup(par(na),'*')}| = ${a}`,'כל תת־קבוצה סופית היא קבוצת האיברים של סדרה סופית']);S.push([`${X} = ${a}`,'קנטור–ברנשטיין'])}}
  return{c,steps:S}}

/* ---------- state ---------- */
let SETS=[{name:'A',kind:'N'},{name:'B',kind:'fin',n:2},{name:'C',kind:'fun',a:'A',b:'B'},{name:'D',kind:'R'},{name:'E',kind:'seq',a:'D'},{name:'F',kind:'pow',a:'D'},{name:'G',kind:'star',a:'A'}],CUR=4;
/* every set in order: its cardinality, its steps, and its full expression in terms of the atoms. A set may use only sets listed before it */
function solve(list){const out=[];list.forEach((s,i)=>{const K=KINDS[s.kind],ix=nm=>{const j=list.findIndex(x=>x.name===nm);return j>=0&&j<i?j:-1},ia=K.src?ix(s.a):-1,ib=K.src===2?ix(s.b):-1;
  if((K.src>=1&&ia<0)||(K.src===2&&ib<0)){out.push({bad:true,expr:'?',kids:[]});return}
  const A=ia>=0?out[ia]:null,Bq=ib>=0?out[ib]:null;if((A&&A.bad)||(Bq&&Bq.bad)){out.push({bad:true,expr:'?',kids:[]});return}
  const r=cardOf(s,A&&A.c,Bq&&Bq.c,s.name,s.a,s.b),atom=!K.src,expr=K.sym(A?(KINDS[list[ia].kind].src?par(A.expr):A.expr):'',Bq?(KINDS[list[ib].kind].src?par(Bq.expr):Bq.expr):'',nOf(s));
  out.push({c:r.c,steps:r.steps,expr,atom,kids:[ia,ib].filter(x=>x>=0)})});return out}
const fx=t=>`<bdi dir="ltr" class="fx">${t}</bdi>`;
const short=s=>KINDS[s.kind].sym(s.a||'',s.b||'',nOf(s));
function renderSide(R){const opt=(l,c)=>l.map(([v,t])=>`<option value="${v}" ${v===c?'selected':''}>${t}</option>`).join('');
  document.getElementById('cdobjs').innerHTML=SETS.map((s,i)=>{const K=KINDS[s.kind],before=SETS.slice(0,i).map(x=>[x.name,x.name]),kinds=Object.entries(KINDS).filter(([k,x])=>!x.src||i>0).map(([k,x])=>[k,x.l]);
    return `<div class="qbox${i===CUR?' rlcur':''}"><div class="qrow"><button class="name v rlnm" data-cs="${i}" aria-pressed="${i===CUR}" aria-label="הצג את ${s.name}">${s.name}</button><select data-ci="${i}" data-f="kind" aria-label="סוג הקבוצה">${opt(kinds,s.kind)}</select>${SETS.length>1?`<button class="x" data-cdel="${i}" aria-label="הסר את ${s.name}">×</button>`:''}</div>
      ${K.src||K.n?`<div class="qrow">${K.src?`<label class="cell">${K.lab?K.lab[0]:'של'}<select data-ci="${i}" data-f="a">${opt(before,s.a)}</select></label>`:''}${K.src===2?`<label class="cell">${K.lab?K.lab[1]:'ושל'}<select data-ci="${i}" data-f="b">${opt(before,s.b)}</select></label>`:''}${K.n?`<label class="cell">${s.kind==='fin'?'גודל':'אורך'}<input type="number" min="0" class="rn" dir="ltr" data-ci="${i}" data-f="n" value="${nOf(s)}"></label>`:''}</div>`:''}
      <div class="gfset fx">${s.name} = ${short(s)}${R[i].bad?'':`,   |${s.name}| = ${fmt(R[i].c)}`}</div></div>`}).join('')}
function renderMain(R){if(CUR>=SETS.length)CUR=SETS.length-1;const s=SETS[CUR],r=R[CUR];
  /* the structure tree: the set, and under it the sets it is built from, down to the atoms */
  const tree=(i,d)=>`<div class="cdn" style="margin-inline-start:${d*22}px"><span class="name v">${SETS[i].name}</span>${fx(`${R[i].expr}`)}<span class="cdc">${fx(fmt(R[i].c))}</span><span class="lab">${R[i].atom?'גרעין':KINDS[SETS[i].kind].l}</span></div>${R[i].kids.map(j=>tree(j,d+1)).join('')}`;
  /* the proof: the sets the current one rests on, each once, in the order they are needed */
  const order=[],seen=new Set(),go=i=>{if(seen.has(i))return;seen.add(i);R[i].kids.forEach(go);order.push(i)};if(!r.bad)go(CUR);
  const block=i=>`<div class="qpb"><div class="qph"><span>${SETS[i].name}: ${KINDS[SETS[i].kind].l}</span>${fx(`|${SETS[i].name}| = ${fmt(R[i].c)}`)}</div><div class="qpf">${R[i].steps.map(([f,w],n)=>`<div class="ps"><div class="pf"><span class="pn">${n+1}</span>${fx(f)}</div><div class="pj">${w}</div></div>`).join('')}</div></div>`;
  const rows=SETS.map((x,i)=>`<tr class="${i===CUR?'cur':''}"><th scope="row"><button data-cs="${i}">${x.name}</button></th><td>${fx(R[i].expr)}</td><td class="c">${R[i].bad?'':fx(fmt(R[i].c))}</td><td>${R[i].bad?'חסרה קבוצת מקור':word(R[i].c)}</td></tr>`).join('');
  document.getElementById('main').innerHTML=`<div class="gfwrap cd">
    <section class="gfb"><h3>כל הקבוצות</h3><div class="rlmw"><table class="cdtab"><thead><tr><th></th><th scope="col">המבנה, עד הגרעינים</th><th scope="col">העוצמה</th><th scope="col">סוג</th></tr></thead><tbody>${rows}</tbody></table></div></section>
    ${r.bad?`<div class="qwarn">הקבוצה ${s.name} נשענת על קבוצה שאינה מוגדרת מעליה.</div>`:`<div class="gfeq fx">|${s.name}| = ${fmt(r.c)}</div>
    <section class="gfb"><h3>עץ המבנה של ${s.name}</h3><p class="hint">בכל שורה: הקבוצה, המבנה שלה, העוצמה שלה, והפעולה שבנתה אותה. מתחתיה הקבוצות שמהן נבנתה.</p><div class="cdtree">${tree(CUR,0)}</div></section>
    <section class="gfb"><h3>החישוב, קבוצה אחר קבוצה</h3><p class="hint">מהגרעינים ועד ${s.name}. בכל שורה נוסחה, ומתחתיה הנימוק.</p>${order.map(block).join('')}</section>`}</div>`;
  /* the card: all the sets in order of cardinality */
  const ok=SETS.map((x,i)=>i).filter(i=>!R[i].bad).sort((i,j)=>(cmp(R[i].c,R[j].c)||0)||i-j),chain=[];
  ok.forEach((i,n)=>{if(n)chain.push(same(R[ok[n-1]].c,R[i].c)?' = ':' < ');chain.push(`|${SETS[i].name}|`)});
  const groups=[];for(const i of ok){const g=groups[groups.length-1];if(g&&same(g.c,R[i].c))g.m.push(i);else groups.push({c:R[i].c,m:[i]})}
  document.getElementById('card').innerHTML=`<div class="gfcard cd"><div class="cardhead"><h2>סדר העוצמות</h2></div><div class="cdchain">${fx(chain.join(''))}</div>
    ${groups.map(g=>`<div class="cdg"><div class="cdgh">${fx(fmt(g.c))}<span>${word(g.c)}</span></div><div class="cdgm">${fx(g.m.map(i=>SETS[i].name).join(', '))}</div></div>`).join('')}
    <p class="qnote" role="note"><b>על מה החישוב נשען.</b> על הגרעינים הידועים ועל כללי חשבון העוצמות: סכום ומכפלה של עוצמות שלפחות אחת מהן אינסופית שווים לגדולה מהשתיים, חזקה של חזקה היא חזקה במכפלה, ומשפט קנטור–ברנשטיין. הכללים האלה משתמשים באקסיומת הבחירה, כמקובל.</p>
    <p class="hint">${fx(sup('2','ℵ₀'))} היא עוצמת הרצף. עוצמה סופית גדולה מכדי לכתוב מסומנת ${fx('<i>N</i>')}.</p></div>`}
function renderAll(){const R=solve(SETS);renderSide(R);renderMain(R)}
document.addEventListener('click',ev=>{const t=ev.target;if(!t.closest||!t.closest('.cd'))return;const cs=t.closest('[data-cs]'),del=t.closest('[data-cdel]'),add=t.closest('[data-cadd]');
  if(cs){CUR=Number(cs.dataset.cs);renderAll()}
  else if(del&&SETS.length>1){const i=Number(del.dataset.cdel);SETS.splice(i,1);if(CUR>=i&&CUR>0)CUR--;renderAll()}
  else if(add){const name=[...NAMES].find(x=>!SETS.some(s=>s.name===x));if(!name)return;const src=SETS[CUR].name;SETS.push(add.dataset.cadd==='atom'?{name,kind:'N'}:{name,kind:'pow',a:src,b:src,n:2});CUR=SETS.length-1;renderAll()}});
document.addEventListener('change',ev=>{const t=ev.target;if(!t.closest||!t.closest('.cd')||t.dataset.ci===undefined)return;const s=SETS[Number(t.dataset.ci)],i=Number(t.dataset.ci);if(!s)return;s[t.dataset.f]=t.value;
  if(t.dataset.f==='kind'){const K=KINDS[s.kind],prev=SETS[Math.max(0,i-1)].name;if(K.src&&!SETS.slice(0,i).some(x=>x.name===s.a))s.a=prev;if(K.src===2&&!SETS.slice(0,i).some(x=>x.name===s.b))s.b=prev;if(K.n&&(s.n===undefined||s.n===''))s.n=2}renderAll()});
return{
/* for tests */
lib:{F,B,add,mul,pow,cmp,same,fmt,solve,KINDS},
render(){
  document.getElementById('conds').innerHTML=`<div class="qb cd"><div class="colhead"><h2>הקבוצות</h2><span class="lab">גרעינים ומה שנבנה מהם</span></div><div id="cdobjs" class="qlist"></div>
    <div class="qbox"><div class="lab">הוסף קבוצה</div><div class="addrow"><button class="addb" data-cadd="atom">+ קבוצה ידועה</button><button class="addb" data-cadd="op">+ קבוצה מפעולה</button></div>
    <p class="hint">קבוצה מפעולה נבנית מקבוצות שמעליה. לחיצה על שם הקבוצה מציגה את המבנה ואת החישוב שלה.</p></div></div>`;
  renderAll()}};
})();
