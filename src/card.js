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
  uni:{l:'איחוד',src:2,rel:true,sym:(a,b)=>`${a} ∪ ${b}`},int:{l:'חיתוך',src:2,rel:true,sym:(a,b)=>`${a} ∩ ${b}`},dif:{l:'הפרש',src:2,rel:true,lab:['מתוך','מסירים את'],sym:(a,b)=>`${a} ∖ ${b}`},sym:{l:'הפרש סימטרי',src:2,rel:true,sym:(a,b)=>`${a} △ ${b}`},
  cond:{l:'סדרות אינסופיות שמקיימות תנאי',src:1,cond:true,sym:(a,b,n,s)=>`{ a: ℕ → ${a} | ${(CONDS[s&&s.cond]||CONDS.const).t(Math.max(1,n))} }`},
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

/* ---------- union, intersection, difference: the cardinalities of the two sets do not settle the answer, so the result is a range
   unless something is known about how the sets sit: disjoint, or one inside the other ---------- */
const lt=(x,y)=>cmp(x,y)<0,mn=(x,y)=>lt(y,x)?y:x,mx=(x,y)=>lt(x,y)?y:x,minus=(x,y)=>x.n===null||y.n===null?null:F(x.n>y.n?x.n-y.n:0n);
const RELS={'':'לא נתון',dis:'זרות',sub:'הראשונה מוכלת בשנייה',sup:'השנייה מוכלת בראשונה'};
/* what is known without being told: the standard sets sit inside one another, and the open interval misses the integers */
function autoRel(sa,sb){const rank={fin:0,N:1,Z:2,Q:3,R:4},a=sa.kind,b=sb.kind;if(a==='fin'&&nOf(sa)===0)return 'sub';if(b==='fin'&&nOf(sb)===0)return 'sup';
  if(a in rank&&b in rank){if(a==='fin'&&b==='fin')return nOf(sa)<=nOf(sb)?'sub':'sup';return rank[a]<=rank[b]?'sub':'sup'}
  if(a==='I'&&b==='I')return 'sub';if(a==='I'&&b==='R')return 'sub';if(a==='R'&&b==='I')return 'sup';if((a==='I'&&(b==='fin'||b==='N'||b==='Z'))||(b==='I'&&(a==='fin'||a==='N'||a==='Z')))return 'dis';return ''}
function diffIn(a,b,X,big,small){/* big ∖ small, where small ⊆ big */const S=[];
  if(fin(a)){const r=minus(a,b);if(r){S.push([`${X} = |${big}| − |${small}| = ${fmt(a)} − ${fmt(b)} = ${fmt(r)}`,`${small} מוכלת ב־${big}, ושתיהן סופיות`]);return{lo:r,hi:r,steps:S}}S.push([`0 ≤ ${X} ≤ ${fmt(a)}`,'הגדלים גדולים מכדי לחסר']);return{lo:F(0),hi:a,steps:S}}
  if(lt(b,a)){S.push([`${fmt(a)} = |${big}| = ${X} + |${small}| = ${X} + ${fmt(b)}`,`${big} היא איחוד זר של ההפרש ושל ${small}`]);S.push([`${X} = ${fmt(a)}`,`אילו ההפרש היה קטן מ־${fmt(a)}, גם הסכום היה קטן מ־${fmt(a)}: ${maxWhy}`]);return{lo:a,hi:a,steps:S}}
  S.push([`0 ≤ ${X} ≤ ${fmt(a)}`,`שתי הקבוצות באותה עוצמה אינסופית, וההפרש תלוי בקבוצות עצמן: הוא יכול להיות ריק, סופי, או בעוצמה ${fmt(a)}`]);return{lo:F(0),hi:a,steps:S}}
function setOp(kind,rel,a,b,nm,na,nb){const X=`|${nm}|`,fa=fmt(a),fb=fmt(b),S=[],ex=(c,f,w)=>{S.push([f,w]);return{lo:c,hi:c,steps:S}},rg=(lo,hi,f,w)=>{S.push([f,w]);return{lo,hi,steps:S}};
  if(kind==='uni'){if(rel==='dis'){const c=add(a,b);S.push([`${X} = |${na}| + |${nb}| = ${fa} + ${fb}`,'הקבוצות זרות: העוצמה היא סכום העוצמות']);return ex(c,`${fa} + ${fb} = ${fmt(c)}`,fin(c)?'חיבור של מספרים טבעיים':maxWhy)}
    if(rel==='sub')return ex(b,`${nm} = ${nb},   ${X} = ${fb}`,`${na} מוכלת ב־${nb}, ולכן האיחוד הוא ${nb}`);if(rel==='sup')return ex(a,`${nm} = ${na},   ${X} = ${fa}`,`${nb} מוכלת ב־${na}, ולכן האיחוד הוא ${na}`);
    const lo=mx(a,b),hi=add(a,b);S.push([`${fmt(lo)} ≤ ${X} ≤ ${fa} + ${fb} = ${fmt(hi)}`,'כל אחת מהקבוצות מוכלת באיחוד, והאיחוד אינו גדול מהאיחוד הזר']);
    return same(lo,hi)?ex(lo,`${X} = ${fmt(lo)}`,'קנטור–ברנשטיין: חסם תחתון וחסם עליון שווים'):{lo,hi,steps:S}}
  if(kind==='int'){if(rel==='dis')return ex(F(0),`${nm} = ∅,   ${X} = 0`,'הקבוצות זרות');if(rel==='sub')return ex(a,`${nm} = ${na},   ${X} = ${fa}`,`${na} מוכלת ב־${nb}, ולכן החיתוך הוא ${na}`);if(rel==='sup')return ex(b,`${nm} = ${nb},   ${X} = ${fb}`,`${nb} מוכלת ב־${na}, ולכן החיתוך הוא ${nb}`);
    const hi=mn(a,b);return zero(hi)?ex(hi,`${X} = 0`,'אחת הקבוצות ריקה'):rg(F(0),hi,`0 ≤ ${X} ≤ ${fmt(hi)}`,'החיתוך מוכל בכל אחת מהקבוצות, ובלי מידע נוסף הוא יכול להיות גם ריק')}
  if(kind==='dif'){if(rel==='dis')return ex(a,`${nm} = ${na},   ${X} = ${fa}`,'הקבוצות זרות: שום איבר לא מוסר');if(rel==='sub')return ex(F(0),`${nm} = ∅,   ${X} = 0`,`${na} מוכלת ב־${nb}: כל האיברים מוסרים`);if(rel==='sup')return diffIn(a,b,X,na,nb);
    if(zero(a))return ex(a,`${X} = 0`,'מקבוצה ריקה אין מה להסיר');
    if(fin(a)){const lo=fin(b)?(minus(a,b)||F(0)):F(0);return same(lo,a)?ex(a,`${X} = ${fa}`,'הקבוצה שמסירים ריקה'):rg(lo,a,`${fmt(lo)} ≤ ${X} ≤ ${fa}`,fin(b)?'מוסרים לכל היותר כמספר איברי הקבוצה השנייה, ולכל הפחות אף איבר':'ההפרש מוכל בקבוצה הראשונה, ואולי כולה מוסרת')}
    if(lt(b,a)){S.push([`${fa} = |${na}| = ${X} + |${na} ∩ ${nb}|,   |${na} ∩ ${nb}| ≤ ${fb}`,`${na} היא איחוד זר של ההפרש ושל החיתוך, והחיתוך מוכל ב־${nb}`]);return ex(a,`${X} = ${fa}`,`אילו ההפרש היה קטן מ־${fa}, גם הסכום היה קטן מ־${fa}: ${maxWhy}`)}
    return rg(F(0),a,`0 ≤ ${X} ≤ ${fa}`,'הקבוצה שמסירים אינה קטנה מהראשונה, ולכן ההפרש תלוי בקבוצות עצמן')}
  /* symmetric difference */
  if(rel==='dis'){const c=add(a,b);S.push([`${nm} = ${na} ∪ ${nb},   ${X} = ${fa} + ${fb}`,'הקבוצות זרות: ההפרש הסימטרי הוא האיחוד']);return ex(c,`${fa} + ${fb} = ${fmt(c)}`,fin(c)?'חיבור של מספרים טבעיים':maxWhy)}
  if(rel==='sub'){S.push([`${nm} = ${nb} ∖ ${na}`,`${na} מוכלת ב־${nb}`]);const r=diffIn(b,a,X,nb,na);return{lo:r.lo,hi:r.hi,steps:[...S,...r.steps]}}
  if(rel==='sup'){S.push([`${nm} = ${na} ∖ ${nb}`,`${nb} מוכלת ב־${na}`]);const r=diffIn(a,b,X,na,nb);return{lo:r.lo,hi:r.hi,steps:[...S,...r.steps]}}
  if(fin(a)&&fin(b)){const d=lt(a,b)?minus(b,a):minus(a,b),lo=d||F(0),hi=add(a,b);return same(lo,hi)?ex(lo,`${X} = ${fmt(lo)}`,'אחת הקבוצות ריקה'):rg(lo,hi,`${fmt(lo)} ≤ ${X} ≤ ${fmt(hi)}`,'החסם התחתון כשאחת מוכלת בשנייה, והעליון כשהן זרות')}
  if(!same(a,b)){const big=mx(a,b),[P,Q]=lt(b,a)?[na,nb]:[nb,na];S.push([`|${P} ∖ ${Q}| = ${fmt(big)}`,`${Q} קטנה מ־${P}, ולכן הסרתה אינה משנה את העוצמה האינסופית`]);return ex(big,`${fmt(big)} ≤ ${X} ≤ ${fa} + ${fb} = ${fmt(big)}`,`${P} ∖ ${Q} מוכלת בהפרש הסימטרי, והוא מוכל באיחוד`)}
  return rg(F(0),a,`0 ≤ ${X} ≤ ${fa}`,'שתי הקבוצות באותה עוצמה אינסופית, וההפרש הסימטרי תלוי בקבוצות עצמן')}
/* a construction over sets whose cardinality is only known as a range: the ends of the ranges, since every construction here only grows when its sets grow */
function ranged(s,A,Bq,list,ia,ib){const K=KINDS[s.kind],X=`|${s.name}|`,ends=q=>q?(same(q.lo,q.hi)?[q.lo]:[q.lo,q.hi]):[null];let lo=null,hi=null;
  const rel=K.rel?(s.rel||autoRel(list[ia],list[ib])):'';
  for(const a of ends(A))for(const b of ends(Bq)){const r=K.rel?setOp(s.kind,rel,a,b,s.name,s.a,s.b):(c=>({lo:c,hi:c}))(cardOf(s,a,b,s.name,s.a,s.b).c);lo=lo===null?r.lo:mn(lo,r.lo);hi=hi===null?r.hi:mx(hi,r.hi)}
  /* the least symmetric difference is not at an end when the two ranges meet */
  if(s.kind==='sym'&&rel===''&&A&&Bq&&!lt(A.hi,Bq.lo)&&!lt(Bq.hi,A.lo))lo=F(0);
  return{lo,hi,steps:[[same(lo,hi)?`${X} = ${fmt(lo)}`:`${fmt(lo)} ≤ ${X} ≤ ${fmt(hi)}`,'עוצמת אחד המקורות ידועה רק כטווח. מציבים את קצות הטווחים: הקטנים ביותר לחסם התחתון, והגדולים ביותר לעליון']]}}

/* ---------- infinite sequences cut out by a condition. Each condition from a closed list comes with its structure:
   what the set is equivalent to, or what it lies between. The cardinality then follows as before ---------- */
const ORD=new Set(['fin','N','Z','Q','R','I']);
const CONDS={const:{l:'קבועה',t:()=>'aₙ = a₁'},per:{l:'מחזורית, עם מחזור נתון',p:'מחזור',t:p=>`aₙ₊${p} = aₙ`.replace(/₊(\d+)/,(m,d)=>'₊'+d.split('').map(x=>'₀₁₂₃₄₅₆₇₈₉'[x]).join(''))},anyper:{l:'מחזורית, במחזור כלשהו',t:()=>'∃p ∀n: aₙ₊ₚ = aₙ'},
  evconst:{l:'קבועה ממקום מסוים',t:()=>'∃m ∀n ≥ m: aₙ = aₘ'},finsup:{l:'שווה לאיבר נתון c, פרט למספר סופי של מקומות',t:()=>'∃m ∀n ≥ m: aₙ = c'},
  fixk:{l:'ערכים נתונים במספר סופי של מקומות',p:'מקומות',t:p=>`a given at ${p} places`},fixeven:{l:'ערכים נתונים בכל המקומות הזוגיים',t:()=>'a₂ₙ given'},pairs:{l:'כל איבר במקום זוגי שווה לקודמו',t:()=>'a₂ₙ = a₂ₙ₋₁'},
  never:{l:'איבר נתון c אינו מופיע',t:()=>'∀n: aₙ ≠ c'},once:{l:'איבר נתון c מופיע לפחות פעם אחת',t:()=>'∃n: aₙ = c'},inf:{l:'איבר נתון c מופיע אינסוף פעמים',t:()=>'aₙ = c for infinitely many n'},fintimes:{l:'איבר נתון c מופיע רק מספר סופי של פעמים',t:()=>'aₙ = c for finitely many n'},
  inj:{l:'חד-חד-ערכית: אין איבר שחוזר',t:()=>'a one-to-one'},surj:{l:'על: כל איבר של הקבוצה מופיע',t:()=>'a onto'},
  nd:{l:'לא יורדת',ord:true,t:()=>'aₙ ≤ aₙ₊₁'},si:{l:'עולה ממש',ord:true,t:()=>'aₙ < aₙ₊₁'},ni:{l:'לא עולה',ord:true,t:()=>'aₙ ≥ aₙ₊₁'},sd:{l:'יורדת ממש',ord:true,t:()=>'aₙ > aₙ₊₁'}};
function condOf(s,k,srcKind,nm,na){const X=`|${nm}|`,q=CONDS[s.cond]||CONDS.const,key=CONDS[s.cond]?s.cond:'const',p=Math.max(1,nOf(s)),fk=fmt(k),all=pow(k,ALEPH),S=[],big=fin(k)&&!zero(k)&&!one(k);
  const ex=(c,f,w)=>{S.push([f,w]);return{lo:c,hi:c,steps:S}},CB=c=>ex(c,`${X} = ${fmt(c)}`,'קנטור–ברנשטיין: חסם תחתון וחסם עליון שווים'),seqA=`ℕ → ${na}`;
  if(q.ord&&!ORD.has(srcKind))return{bad:'התנאי משווה בין איברים, ולכן הקבוצה צריכה להיות קבוצת מספרים: סופית, הטבעיים, השלמים, הרציונליים, הממשיים או הקטע'};
  if(zero(k))return ex(F(0),`${X} = 0`,`אין אף סדרה אינסופית של איברי קבוצה ריקה`);
  /* the cardinality of "a finite stretch of free choices, then no more choices": 1, ℵ0 or κ */
  const tail=(parts,low,lowWhy)=>{S.push([`${nm} = ∪ ${nm}ₘ,   m = 1, 2, 3, …,   ${nm}ₘ ≅ ${parts}`,low[0]]);if(one(k))return ex(F(1),`${X} = 1`,'מעל קבוצה של איבר אחד יש סדרה אחת בלבד');
    if(fin(k)){S.push([`ℵ₀ ≤ ${X}`,lowWhy]);S.push([`${X} ≤ ℵ₀`,'איחוד בן־מנייה של קבוצות סופיות']);return CB(ALEPH)}
    S.push([`${fk} ≤ ${X}`,'הסדרות הקבועות מקיימות את התנאי, ויש אחת לכל איבר']);S.push([`${X} ≤ ℵ₀ · ${fk} = ${fk}`,`איחוד בן־מנייה של קבוצות שכל אחת מהן בעוצמה ${fk}`]);return CB(k)};
  const free=(why)=>{S.push([`${nm} ≅ ${seqA}`,why]);S.push([`${X} = ${sup(par(fk),'ℵ₀')}`,'קבוצות שקולות הן באותה עוצמה']);S.push(...powSteps(k,ALEPH));return{lo:all,hi:all,steps:S}};
  const between=(lowWhy)=>{S.push([`${fmt(all)} ≤ ${X}`,lowWhy]);S.push([`${X} ≤ |${seqA}| = ${fmt(all)}`,'הקבוצה מוכלת בקבוצת כל הסדרות']);return CB(all)};
  if(key==='const'){S.push([`${nm} ≅ ${na}`,'סדרה קבועה נקבעת על ידי האיבר שלה, ולכל איבר יש סדרה כזאת']);return ex(k,`${X} = |${na}| = ${fk}`,'קבוצות שקולות הן באותה עוצמה')}
  if(key==='per'){const c=pow(k,F(p));S.push([`${nm} ≅ ${sup(par(na),p)}`,`סדרה עם מחזור ${p} נקבעת על ידי ${p} האיברים הראשונים שלה, וכל בחירה שלהם נותנת סדרה כזאת`]);S.push([`${X} = ${sup(par(fk),p)}`,'קבוצות שקולות הן באותה עוצמה']);S.push(...powSteps(k,F(p)));return{lo:c,hi:c,steps:S}}
  if(key==='anyper')return tail(sup(par(na),'m'),['לפי אורך המחזור m: סדרה עם מחזור m נקבעת על ידי m האיברים הראשונים'],'לכל m יש סדרה שהמחזור הקצר ביותר שלה הוא m: בלוק באורך m שבו איבר אחד פעם אחת ואחריו רק איבר אחר, וחוזר חלילה');
  if(key==='evconst')return tail(`${sup(par(na),'m')}`,['לפי המקום m שממנו הסדרה קבועה: היא נקבעת על ידי m האיברים הראשונים'],'לכל m יש סדרה שנעשית קבועה בדיוק במקום m: איבר אחד בכל המקומות שלפני m, ואיבר אחר ממנו והלאה');
  if(key==='finsup')return tail(`${sup(par(na),'m')}`,['לפי המקום m שממנו כל האיברים שווים ל־c: הסדרה נקבעת על ידי האיברים שלפניו'],'לכל m יש סדרה ששונה מ־c בדיוק במקום m');
  if(key==='fixk')return free(`${p} המקומות הנתונים אינם בחירה. נשארים ℵ₀ מקומות חופשיים, והסדרה נקבעת על ידי האיברים שבהם`);
  if(key==='fixeven')return free('המקומות הזוגיים אינם בחירה. המקומות האי־זוגיים חופשיים, ויש ℵ₀ כאלה');
  if(key==='pairs')return free('האיברים במקומות האי־זוגיים חופשיים, והם קובעים את השאר');
  if(key==='never'){const m=fin(k)?(k.n===null?F(null):F(k.n-1n)):k,c=pow(m,ALEPH);S.push([`${nm} = ℕ → (${na} ∖ {c})`,'אלה בדיוק הסדרות של שאר האיברים']);S.push([`|${na} ∖ {c}| = ${fmt(m)}`,fin(k)?'איבר אחד פחות':'הסרת איבר אחד אינה משנה עוצמה אינסופית']);S.push([`${X} = ${sup(par(fmt(m)),'ℵ₀')}`,'סדרה אינסופית היא פונקציה מהטבעיים']);S.push(...powSteps(m,ALEPH));return{lo:c,hi:c,steps:S}}
  if(key==='once'){if(one(k))return ex(F(1),`${X} = 1`,'הסדרה היחידה מכילה את c');return between('סדרה שמתחילה ב־c וממשיכה באופן חופשי מקיימת את התנאי, ויש כאלה כמספר כל הסדרות')}
  if(key==='inf'){if(one(k))return ex(F(1),`${X} = 1`,'הסדרה היחידה היא c בכל מקום');return between('c בכל המקומות הזוגיים, והמקומות האי־זוגיים חופשיים')}
  if(key==='fintimes'){if(one(k))return ex(F(0),`${X} = 0`,'הסדרה היחידה היא c בכל מקום, אינסוף פעמים');
    if(fin(k)&&k.n===2n){S.push([`${nm} = { a | ∃m ∀n ≥ m: aₙ = d },   ${na} = {c, d}`,'כש־c מופיע מספר סופי של פעמים, ממקום מסוים מופיע רק האיבר השני']);S.push([`ℵ₀ ≤ ${X}`,'לכל m יש סדרה שבה c מופיע בדיוק במקום m']);S.push([`${X} ≤ ℵ₀`,'איחוד בן־מנייה, לפי המקום האחרון של c, של קבוצות סופיות']);return CB(ALEPH)}
    S.push([`ℕ → (${na} ∖ {c})  ⊆  ${nm}`,'סדרה שבה c אינו מופיע כלל מקיימת את התנאי']);S.push([`|ℕ → (${na} ∖ {c})| = ${fmt(all)}`,fin(k)?'אחרי הסרת c נשארים לפחות שני איברים, והעוצמה היא עוצמת הרצף':'הסרת איבר אחד אינה משנה עוצמה אינסופית']);return between('לפי שתי השורות הקודמות')}
  if(key==='inj'){if(fin(k))return ex(F(0),`${X} = 0`,'עקרון שובך היונים: בסדרה אינסופית של איברי קבוצה סופית יש איבר שחוזר');
    S.push([`|${na} × ℕ| = ${fk} · ℵ₀ = ${fk}`,`ולכן מספיק לספור סדרות חד-חד-ערכיות של איברי ${na} × ℕ`]);return between(`לכל סדרה f של איברי ${na}, הסדרה n ↦ (f(n), n) חד-חד-ערכית, וסדרות שונות נותנות סדרות שונות`)}
  if(key==='surj'){if(one(k))return ex(F(1),`${X} = 1`,'הסדרה היחידה מכסה את האיבר היחיד');if(!fin(k)&&k.k>=1)return ex(F(0),`${X} = 0`,'בסדרה מופיעים לכל היותר ℵ₀ איברים שונים, והקבוצה גדולה מזה');
    return between(fin(k)?`${fk} המקומות הראשונים עוברים על כל האיברים, והשאר חופשיים`:'במקומות האי־זוגיים עוברים על כל האיברים, כי הקבוצה בת־מנייה, והמקומות הזוגיים חופשיים')}
  /* monotone sequences of numbers */
  const up=key==='nd'||key==='si',strict=key==='si'||key==='sd';
  if(srcKind==='fin'){if(strict)return ex(F(0),`${X} = 0`,'סדרה מונוטונית ממש היא חד-חד-ערכית, ובקבוצה סופית אין מספיק איברים');if(one(k))return ex(F(1),`${X} = 1`,'יש סדרה אחת בלבד');
    S.push([`${nm} ⊆ { a | ∃m ∀n ≥ m: aₙ = aₘ }`,'מעל קבוצה סופית הסדרה משתנה מספר סופי של פעמים, ולכן היא קבועה ממקום מסוים']);S.push([`${X} ≤ ℵ₀`,'הסדרות הקבועות ממקום מסוים מעל קבוצה סופית הן בנות־מנייה']);S.push([`ℵ₀ ≤ ${X}`,'לכל m יש סדרה מונוטונית שמשתנה בדיוק במקום m']);return CB(ALEPH)}
  if(srcKind==='N'&&!up){if(strict)return ex(F(0),`${X} = 0`,'אין סדרה אינסופית יורדת ממש של טבעיים: מתחת לכל טבעי יש מספר סופי של טבעיים');
    S.push([`${nm} ⊆ { a | ∃m ∀n ≥ m: aₙ = aₘ }`,'סדרה לא עולה של טבעיים יורדת מספר סופי של פעמים, ולכן היא קבועה ממקום מסוים']);S.push([`${X} ≤ ℵ₀`,'הסדרות של טבעיים שקבועות ממקום מסוים הן בנות־מנייה']);S.push([`ℵ₀ ≤ ${X}`,'הסדרות הקבועות מקיימות את התנאי']);return CB(ALEPH)}
  const C1=B(1);
  if(srcKind==='N'){if(strict){S.push([`${nm} ≅ { T ⊆ ℕ | T infinite }`,'סדרה עולה ממש נקבעת על ידי קבוצת האיברים שלה, וכל קבוצה אינסופית של טבעיים מסודרת כסדרה עולה אחת']);S.push([`|P(ℕ)| = ${fmt(C1)},   |P<sub>fin</sub>(ℕ)| = ℵ₀`,'הקבוצות האינסופיות הן כל התת־קבוצות פרט לסופיות']);return ex(C1,`${X} = ${fmt(C1)}`,'הסרת קבוצה קטנה מקבוצה אינסופית אינה משנה את העוצמה')}
    S.push([`${nm} ≅ ℕ × (ℕ → ℕ)`,'סדרה לא יורדת נקבעת על ידי האיבר הראשון ועל ידי סדרת ההפרשים, וכל בחירה כזאת מתאימה']);return ex(C1,`${X} = ℵ₀ · ${sup('ℵ₀','ℵ₀')} = ℵ₀ · ${fmt(C1)} = ${fmt(C1)}`,maxWhy)}
  S.push([`${fmt(C1)} ≤ ${X}`,`ב־${na} יש סדרה אינסופית ${up?'עולה':'יורדת'} ממש b₁, b₂, …. כל סדרה עולה ממש של טבעיים n₁ < n₂ < … נותנת תת־סדרה שונה שלה, ויש ${fmt(C1)} כאלה`]);S.push([`${X} ≤ |${seqA}| = ${fmt(all)}`,'הקבוצה מוכלת בקבוצת כל הסדרות']);return CB(C1)}

/* ---------- state ---------- */
let SETS=[{name:'A',kind:'N'},{name:'B',kind:'fin',n:2},{name:'C',kind:'fun',a:'A',b:'B'},{name:'D',kind:'R'},{name:'E',kind:'seq',a:'D'},{name:'F',kind:'pow',a:'D'},{name:'G',kind:'star',a:'A'},{name:'H',kind:'Q'},{name:'J',kind:'dif',a:'D',b:'H'},{name:'K',kind:'int',a:'C',b:'E'},{name:'L',kind:'cond',a:'A',cond:'si'},{name:'M',kind:'cond',a:'B',cond:'evconst'}],CUR=10;
/* every set in order: its cardinality, its steps, and its full expression in terms of the atoms. A set may use only sets listed before it */
function solve(list){const out=[];list.forEach((s,i)=>{const K=KINDS[s.kind],ix=nm=>{const j=list.findIndex(x=>x.name===nm);return j>=0&&j<i?j:-1},ia=K.src?ix(s.a):-1,ib=K.src===2?ix(s.b):-1;
  if((K.src>=1&&ia<0)||(K.src===2&&ib<0)){out.push({bad:true,expr:'?',kids:[]});return}
  const A=ia>=0?out[ia]:null,Bq=ib>=0?out[ib]:null;if((A&&A.bad)||(Bq&&Bq.bad)){out.push({bad:true,expr:'?',kids:[]});return}
  const exactIn=(!A||A.c)&&(!Bq||Bq.c),rel=K.rel?(s.rel||autoRel(list[ia],list[ib])):'';
  if(K.cond){const ex0=K.sym(KINDS[list[ia].kind].src?par(A.expr):A.expr,'',nOf(s),s),hi0=pow(A.hi,ALEPH);
    const r=A.c?condOf(s,A.c,list[ia].kind,s.name,s.a):{lo:F(0),hi:hi0,steps:[[`0 ≤ |${s.name}| ≤ ${fmt(hi0)}`,`עוצמת ${s.a} ידועה רק כטווח, והתנאי אינו תלוי בה באופן מונוטוני. נשאר רק החסם של כל הסדרות`]]};
    if(r.bad){out.push({bad:true,msg:r.bad,expr:ex0,kids:[ia]});return}const c=same(r.lo,r.hi)?r.lo:null;
    out.push({c,lo:r.lo,hi:r.hi,steps:r.steps,expr:ex0,atom:false,kids:[ia],txt:c?`|${s.name}| = ${fmt(c)}`:`${fmt(r.lo)} ≤ |${s.name}| ≤ ${fmt(r.hi)}`,val:c?fmt(c):`${fmt(r.lo)} … ${fmt(r.hi)}`});return}
  const r=!exactIn?ranged(s,A,Bq,list,ia,ib):K.rel?setOp(s.kind,rel,A.c,Bq.c,s.name,s.a,s.b):(q=>({lo:q.c,hi:q.c,steps:q.steps}))(cardOf(s,A&&A.c,Bq&&Bq.c,s.name,s.a,s.b));
  const atom=!K.src,expr=K.sym(A?(KINDS[list[ia].kind].src?par(A.expr):A.expr):'',Bq?(KINDS[list[ib].kind].src?par(Bq.expr):Bq.expr):'',nOf(s)),c=same(r.lo,r.hi)?r.lo:null;
  out.push({c,lo:r.lo,hi:r.hi,steps:r.steps,expr,atom,rel,auto:K.rel&&!s.rel&&rel?rel:'',kids:[ia,ib].filter(x=>x>=0),txt:c?`|${s.name}| = ${fmt(c)}`:`${fmt(r.lo)} ≤ |${s.name}| ≤ ${fmt(r.hi)}`,val:c?fmt(c):`${fmt(r.lo)} … ${fmt(r.hi)}`})});return out}
const fx=t=>`<bdi dir="ltr" class="fx">${t}</bdi>`;
const short=s=>KINDS[s.kind].sym(s.a||'',s.b||'',nOf(s),s);
function renderSide(R){const opt=(l,c)=>l.map(([v,t])=>`<option value="${v}" ${v===c?'selected':''}>${t}</option>`).join('');
  document.getElementById('cdobjs').innerHTML=SETS.map((s,i)=>{const K=KINDS[s.kind],before=SETS.slice(0,i).map(x=>[x.name,x.name]),kinds=Object.entries(KINDS).filter(([k,x])=>!x.src||i>0).map(([k,x])=>[k,x.l]);
    return `<div class="qbox${i===CUR?' rlcur':''}"><div class="qrow"><button class="name v rlnm" data-cs="${i}" aria-pressed="${i===CUR}" aria-label="הצג את ${s.name}">${s.name}</button><select data-ci="${i}" data-f="kind" aria-label="סוג הקבוצה">${opt(kinds,s.kind)}</select>${SETS.length>1?`<button class="x" data-cdel="${i}" aria-label="הסר את ${s.name}">×</button>`:''}</div>
      ${K.src||K.n?`<div class="qrow">${K.src?`<label class="cell">${K.lab?K.lab[0]:'של'}<select data-ci="${i}" data-f="a">${opt(before,s.a)}</select></label>`:''}${K.src===2?`<label class="cell">${K.lab?K.lab[1]:'ושל'}<select data-ci="${i}" data-f="b">${opt(before,s.b)}</select></label>`:''}${K.n?`<label class="cell">${s.kind==='fin'?'גודל':'אורך'}<input type="number" min="0" class="rn" dir="ltr" data-ci="${i}" data-f="n" value="${nOf(s)}"></label>`:''}</div>`:''}${K.cond?`<div class="qrow"><label class="cell">התנאי<select data-ci="${i}" data-f="cond">${opt(Object.entries(CONDS).map(([v,x])=>[v,x.l]),s.cond||'const')}</select></label>${(CONDS[s.cond]||{}).p?`<label class="cell">${CONDS[s.cond].p}<input type="number" min="1" class="rn" dir="ltr" data-ci="${i}" data-f="n" value="${Math.max(1,nOf(s))}"></label>`:''}</div>`:''}${K.rel?`<div class="qrow"><label class="cell">היחס בין השתיים<select data-ci="${i}" data-f="rel">${opt(Object.entries(RELS).map(([v,t])=>[v,v===''&&R[i].auto?`מזוהה לבד: ${RELS[R[i].auto]}`:t]),s.rel||'')}</select></label></div>`:''}
      <div class="gfset fx">${s.name} = ${short(s)}${R[i].bad?'':`,   ${R[i].txt}`}</div></div>`}).join('')}
function renderMain(R){if(CUR>=SETS.length)CUR=SETS.length-1;const s=SETS[CUR],r=R[CUR];
  /* the structure tree: the set, and under it the sets it is built from, down to the atoms */
  const tree=(i,d)=>`<div class="cdn" style="margin-inline-start:${d*22}px"><span class="name v">${SETS[i].name}</span>${fx(`${R[i].expr}`)}<span class="cdc">${fx(R[i].val)}</span><span class="lab">${R[i].atom?'גרעין':KINDS[SETS[i].kind].l}</span></div>${R[i].kids.map(j=>tree(j,d+1)).join('')}`;
  /* the proof: the sets the current one rests on, each once, in the order they are needed */
  const order=[],seen=new Set(),go=i=>{if(seen.has(i))return;seen.add(i);R[i].kids.forEach(go);order.push(i)};if(!r.bad)go(CUR);
  const block=i=>`<div class="qpb"><div class="qph"><span>${SETS[i].name}: ${KINDS[SETS[i].kind].l}</span>${fx(R[i].txt)}</div><div class="qpf">${R[i].steps.map(([f,w],n)=>`<div class="ps"><div class="pf"><span class="pn">${n+1}</span>${fx(f)}</div><div class="pj">${w}</div></div>`).join('')}</div></div>`;
  const rows=SETS.map((x,i)=>`<tr class="${i===CUR?'cur':''}"><th scope="row"><button data-cs="${i}">${x.name}</button></th><td>${fx(R[i].expr)}</td><td class="c">${R[i].bad?'':fx(R[i].val)}</td><td>${R[i].bad?(R[i].msg?'התנאי אינו מתאים לקבוצה':'חסרה קבוצת מקור'):R[i].c?word(R[i].c):'טווח: המבנה לא קובע את העוצמה'}</td></tr>`).join('');
  document.getElementById('main').innerHTML=`<div class="gfwrap cd">
    <section class="gfb"><h3>כל הקבוצות</h3><div class="rlmw"><table class="cdtab"><thead><tr><th></th><th scope="col">המבנה, עד הגרעינים</th><th scope="col">העוצמה</th><th scope="col">סוג</th></tr></thead><tbody>${rows}</tbody></table></div></section>
    ${r.bad?`<div class="qwarn">${r.msg||`הקבוצה ${s.name} נשענת על קבוצה שאינה מוגדרת מעליה.`}</div>`:`<div class="gfeq fx">${r.txt}</div>
    <section class="gfb"><h3>עץ המבנה של ${s.name}</h3><p class="hint">בכל שורה: הקבוצה, המבנה שלה, העוצמה שלה, והפעולה שבנתה אותה. מתחתיה הקבוצות שמהן נבנתה.</p><div class="cdtree">${tree(CUR,0)}</div></section>
    <section class="gfb"><h3>החישוב, קבוצה אחר קבוצה</h3><p class="hint">מהגרעינים ועד ${s.name}. בכל שורה נוסחה, ומתחתיה הנימוק.</p>${order.map(block).join('')}</section>`}</div>`;
  /* the card: all the sets in order of cardinality */
  const open=SETS.map((x,i)=>i).filter(i=>!R[i].bad&&!R[i].c),ok=SETS.map((x,i)=>i).filter(i=>!R[i].bad&&R[i].c).sort((i,j)=>(cmp(R[i].c,R[j].c)||0)||i-j),chain=[];
  ok.forEach((i,n)=>{if(n)chain.push(same(R[ok[n-1]].c,R[i].c)?' = ':' < ');chain.push(`|${SETS[i].name}|`)});
  const groups=[];for(const i of ok){const g=groups[groups.length-1];if(g&&same(g.c,R[i].c))g.m.push(i);else groups.push({c:R[i].c,m:[i]})}
  document.getElementById('card').innerHTML=`<div class="gfcard cd"><div class="cardhead"><h2>סדר העוצמות</h2></div><div class="cdchain">${fx(chain.join(''))}</div>
    ${groups.map(g=>`<div class="cdg"><div class="cdgh">${fx(fmt(g.c))}<span>${word(g.c)}</span></div><div class="cdgm">${fx(g.m.map(i=>SETS[i].name).join(', '))}</div></div>`).join('')}
    ${open.length?`<div class="cdg"><div class="cdgh"><span>טווח בלבד</span></div>${open.map(i=>`<div class="cdgm">${fx(R[i].txt)}</div>`).join('')}</div>`:''}
    <p class="qnote" role="note"><b>על מה החישוב נשען.</b> על הגרעינים הידועים ועל כללי חשבון העוצמות: סכום ומכפלה של עוצמות שלפחות אחת מהן אינסופית שווים לגדולה מהשתיים, חזקה של חזקה היא חזקה במכפלה, ומשפט קנטור–ברנשטיין. הכללים האלה משתמשים באקסיומת הבחירה, כמקובל.</p>
    <p class="hint">${fx(sup('2','ℵ₀'))} היא עוצמת הרצף. עוצמה סופית גדולה מכדי לכתוב מסומנת ${fx('<i>N</i>')}.</p></div>`}
function renderAll(){const R=solve(SETS);renderSide(R);renderMain(R)}
document.addEventListener('click',ev=>{const t=ev.target;if(!t.closest||!t.closest('.cd'))return;const cs=t.closest('[data-cs]'),del=t.closest('[data-cdel]'),add=t.closest('[data-cadd]');
  if(cs){CUR=Number(cs.dataset.cs);renderAll()}
  else if(del&&SETS.length>1){const i=Number(del.dataset.cdel);SETS.splice(i,1);if(CUR>=i&&CUR>0)CUR--;renderAll()}
  else if(add){const name=[...NAMES].find(x=>!SETS.some(s=>s.name===x));if(!name)return;const src=SETS[CUR].name;SETS.push(add.dataset.cadd==='atom'?{name,kind:'N'}:{name,kind:'pow',a:src,b:src,n:2});CUR=SETS.length-1;renderAll()}});
document.addEventListener('change',ev=>{const t=ev.target;if(!t.closest||!t.closest('.cd')||t.dataset.ci===undefined)return;const s=SETS[Number(t.dataset.ci)],i=Number(t.dataset.ci);if(!s)return;s[t.dataset.f]=t.value;
  if(t.dataset.f==='kind'){const K=KINDS[s.kind],prev=SETS[Math.max(0,i-1)].name;if(K.src&&!SETS.slice(0,i).some(x=>x.name===s.a))s.a=prev;if(K.src===2&&!SETS.slice(0,i).some(x=>x.name===s.b))s.b=prev;if(K.n&&(s.n===undefined||s.n===''))s.n=2;if(K.cond&&!s.cond)s.cond='evconst'}if(t.dataset.f==='cond'&&CONDS[s.cond].p&&!(Number(s.n)>=1))s.n=2;renderAll()});
return{
/* for tests */
lib:{F,B,add,mul,pow,cmp,same,fmt,solve,KINDS,setOp,CONDS},
render(){
  document.getElementById('conds').innerHTML=`<div class="qb cd"><div class="colhead"><h2>הקבוצות</h2><span class="lab">גרעינים ומה שנבנה מהם</span></div><div id="cdobjs" class="qlist"></div>
    <div class="qbox"><div class="lab">הוסף קבוצה</div><div class="addrow"><button class="addb" data-cadd="atom">+ קבוצה ידועה</button><button class="addb" data-cadd="op">+ קבוצה מפעולה</button></div>
    <p class="hint">קבוצה מפעולה נבנית מקבוצות שמעליה. לחיצה על שם הקבוצה מציגה את המבנה ואת החישוב שלה.</p></div></div>`;
  renderAll()}};
})();
