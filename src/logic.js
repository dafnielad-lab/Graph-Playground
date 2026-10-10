/* ---------- the logic playground: propositions built from menus, one joint truth table, and what the data force ---------- */
const LOGIC=(()=>{
const OPS={not:['¬','לא',1],and:['∧','וגם',2],or:['∨','או',2],imp:['→','גורר',2],iff:['↔','אם ורק אם',2],xor:['⊕','או מוציא: בדיוק אחד',2]};
const EV={not:a=>!a,and:(a,b)=>a&&b,or:(a,b)=>a||b,imp:(a,b)=>!a||b,iff:(a,b)=>a===b,xor:(a,b)=>a!==b};
const VN='pqrstuvwxyz',FN='ABCDEFGHJKLMNPQRSTUVWXYZ',MAXV=8;
/* the propositions of the question, in order; a compound one may only use those above it. given: 'u' not given, 'T', 'F' */
let L=[{name:'p',t:'v',given:'u'},{name:'q',t:'v',given:'u'},{name:'A',t:'f',op:'imp',a:'p',b:'q',given:'T'},{name:'B',t:'f',op:'not',a:'q',b:null,given:'T'},{name:'C',t:'f',op:'not',a:'p',b:null,given:'u'}];
const by=n=>L.find(x=>x.name===n),vars=()=>L.filter(x=>x.t==='v');
const fresh=t=>{const pool=t==='v'?VN:FN;for(const ch of pool)if(!by(ch))return ch;for(let i=1;;i++){const nm=pool[0]+i;if(!by(nm))return nm}};
const esc=x=>String(x).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
/* the proposition written out in the variables, with brackets only where they are needed */
function text(x,top){if(x.t==='v')return x.name;const a=by(x.a),b=x.b&&by(x.b),w=y=>y.t==='v'||y.op==='not'?text(y):`(${text(y)})`;
  return x.op==='not'?`¬${w(a)}`:`${w(a)} ${OPS[x.op][0]} ${w(b)}`}
function value(x,asg,memo){if(memo.has(x))return memo.get(x);let v;if(x.t==='v')v=asg[x.name];else{const a=value(by(x.a),asg,memo);v=x.op==='not'?EV.not(a):EV[x.op](a,value(by(x.b),asg,memo))}memo.set(x,v);return v}
/* every assignment of the variables, true first as in a textbook table; for each the value of every proposition */
function table(){const V=vars(),k=V.length,rows=[];
  for(let r=0;r<(1<<k);r++){const asg={};V.forEach((v,i)=>{asg[v.name]=!((r>>(k-1-i))&1)});const memo=new Map(),vals=L.map(x=>value(x,asg,memo));
    rows.push({vals,ok:L.every((x,i)=>x.given==='u'||(x.given==='T')===vals[i])})}
  return rows}
/* what the table says about each proposition: by itself, and under the data */
function facts(rows){const live=rows.filter(r=>r.ok);
  return L.map((x,i)=>{const all=rows.map(r=>r.vals[i]),lv=live.map(r=>r.vals[i]),tA=all.filter(Boolean).length,tL=lv.filter(Boolean).length;
    return{kind:tA===all.length?'taut':tA===0?'contra':'cont',tA,nA:all.length,forced:!live.length?null:tL===lv.length?'T':tL===0?'F':null,tL,nL:lv.length}})}
const opt=(list,cur)=>list.map(([v,l])=>`<option value="${esc(v)}" ${v===cur?'selected':''}>${esc(l)}</option>`).join('');
function fix(){/* operands must exist and stand above; a compound proposition that lost one falls back to the nearest above */
  L.forEach((x,i)=>{if(x.t!=='f')return;const up=L.slice(0,i).map(y=>y.name);if(!up.length){x.t='v';x.op=x.a=x.b=undefined;rename(x,fresh('v'));return}
    if(!up.includes(x.a))x.a=up[up.length-1];if(OPS[x.op][2]===2){if(!up.includes(x.b))x.b=up[0]}else x.b=null})}
function rename(x,nm){const old=x.name;x.name=nm;L.forEach(y=>{if(y.a===old)y.a=nm;if(y.b===old)y.b=nm})}
function renderList(){
  const nv=vars().length;
  document.getElementById('lgobjs').innerHTML=L.map((x,i)=>{const up=L.slice(0,i).map(y=>[y.name,y.name]),canF=i>0;
    const typ=`<select data-i="${i}" data-k="t" aria-label="סוג">${opt([['v','משתנה'],...(canF?[['f','פסוק מורכב']]:[])],x.t)}</select>`;
    const body=x.t==='v'?'':`<div class="qrow lgrow" dir="ltr">${OPS[x.op][2]===2?`<select data-i="${i}" data-k="a" aria-label="פסוק ראשון">${opt(up,x.a)}</select>`:''}<select data-i="${i}" data-k="op" class="lgop" aria-label="קשר">${opt(Object.entries(OPS).map(([k,v])=>[k,`${v[0]}  ${v[1]}`]),x.op)}</select><select data-i="${i}" data-k="${OPS[x.op][2]===2?'b':'a'}" aria-label="${OPS[x.op][2]===2?'פסוק שני':'פסוק'}">${opt(up,OPS[x.op][2]===2?x.b:x.a)}</select></div><div class="lgtxt fx">${esc(x.name)} = ${esc(text(x))}</div>`;
    return `<div class="qbox"><div class="qrow"><span class="name${x.t==='v'?' v':''}">${esc(x.name)}</span>${typ}<label class="cell">נתון<select data-i="${i}" data-k="given" class="lggiv ${x.given}">${opt([['u','לא נתון'],['T','אמת'],['F','שקר']],x.given)}</select></label><button class="x" data-del="${i}" aria-label="הסר את ${esc(x.name)}">×</button></div>${body}</div>`}).join('');
  document.getElementById('lgadd').innerHTML=`<button class="addb" data-add="v" ${nv>=MAXV?'disabled':''}>+ משתנה</button><button class="addb" data-add="f" ${L.length?'':'disabled'}>+ פסוק מורכב</button>`+(nv>=MAXV?`<p class="hint">עד ${MAXV} משתנים, כדי שהלוח יישאר קריא.</p>`:'')}
function renderTable(){
  const rows=table(),F=facts(rows),live=rows.filter(r=>r.ok).length,given=L.filter(x=>x.given!=='u');
  const head=L.map((x,i)=>{const f=F[i],tag=x.given!=='u'?'<span class="lgtag g">נתון</span>':f.forced?`<span class="lgtag ${f.forced}">נובע</span>`:'';
    return `<th scope="col" class="${x.t==='v'?'v':''}${x.given!=='u'?' giv':''}"><span class="fx nm">${esc(x.name)}</span>${x.t==='f'?`<span class="fx tx">${esc(text(x))}</span>`:''}${tag}</th>`}).join('');
  const body=rows.map((r,n)=>`<tr class="${r.ok?'':'out'}"><td class="rn">${n+1}</td>${r.vals.map((v,i)=>`<td class="${v?'T':'F'}${L[i].given!=='u'?' giv':''}${L[i].given!=='u'&&(L[i].given==='T')!==v?' clash':''}">${v?'T':'F'}</td>`).join('')}</tr>`).join('');
  document.getElementById('main').innerHTML=`<div class="lgwrap"><div class="colhead"><h2>לוח אמת משותף</h2><span class="lab">${given.length?`${live} מתוך ${rows.length} שורות מתיישבות עם הנתונים`:`${rows.length} שורות`}</span></div>
    ${given.length&&!live?'<div class="qwarn" role="alert"><b>הנתונים סותרים זה את זה:</b> אין שורה בלוח שמקיימת את כולם, ולכן מהם נובע כל דבר.</div>':''}
    <div class="lgscroll"><table class="lgtab" dir="ltr"><thead><tr><th class="rn"></th>${head}</tr></thead><tbody>${body}</tbody></table></div>
    <p class="hint">שורה מחוקה היא שורה שלא מתיישבת עם הנתונים: בתא המסומן הערך שונה ממה שנתון. מה שנשאר זהה בכל השורות שלא נמחקו נובע בהכרח מהנתונים.</p></div>`;
  /* conclusions */
  const gtxt=given.map(x=>`${esc(x.given==='T'?'':'¬')}${esc(x.name)}`).join(', '),C=[];
  if(given.length&&live){const yes=[],no=[];L.forEach((x,i)=>{if(x.given!=='u')return;const f=F[i];if(f.forced)yes.push([x,f]);else no.push([x,f])});
    C.push(`<h3>נובע בהכרח מהנתונים</h3>`+(yes.length?yes.map(([x,f])=>`<div class="lgc ${f.forced}"><div class="fx">${gtxt} ⊨ ${f.forced==='T'?'':'¬'}${esc(x.name)}</div><div class="lgw">${esc(x.name)} ${f.forced==='T'?'אמת':'שקר'} ${f.nL===1?'בשורה היחידה שנשארה':`בכל ${f.nL} השורות שנשארו`}${x.t==='f'?`: <span class="fx">${esc(text(x))}</span>`:''}</div></div>`).join(''):'<p class="hint">אף פסוק שאינו נתון לא נקבע על ידי הנתונים.</p>'));
    C.push(`<h3>לא נובע בהכרח</h3>`+(no.length?no.map(([x,f])=>`<div class="lgc"><div class="fx">${gtxt} ⊭ ${esc(x.name)},   ${gtxt} ⊭ ¬${esc(x.name)}</div><div class="lgw">${esc(x.name)} אמת ב־${f.tL} מהשורות שנשארו ושקר ב־${f.nL-f.tL}</div></div>`).join(''):'<p class="hint">כל הפסוקים נקבעו.</p>'))}
  else if(!given.length)C.push('<p class="hint">בחר "נתון" ליד פסוק אחד או יותר, אמת או שקר, כדי לראות אילו שורות נמחקות ומה נובע.</p>');
  /* each proposition by itself */
  C.push(`<h3>כל פסוק בפני עצמו</h3>`+L.filter(x=>x.t==='f').map(x=>{const f=F[L.indexOf(x)];return `<div class="lgc"><div class="fx">${esc(x.name)} = ${esc(text(x))}</div><div class="lgw">${f.kind==='taut'?'<b>טאוטולוגיה</b>: אמת בכל השורות':f.kind==='contra'?'<b>סתירה</b>: שקר בכל השורות':`אמת ב־${f.tA} שורות מתוך ${f.nA}`}</div></div>`}).join('')||'<p class="hint">אין עדיין פסוקים מורכבים.</p>');
  /* propositions with the same column */
  const grp=key=>{const M=new Map();L.forEach((x,i)=>{const k=key(i);(M.get(k)||M.set(k,[]).get(k)).push(x)});return[...M.values()].filter(g=>g.length>1)};
  const eqAll=grp(i=>rows.map(r=>r.vals[i]?1:0).join('')),eqLive=live?grp(i=>F[i].forced?'const'+i:rows.filter(r=>r.ok).map(r=>r.vals[i]?1:0).join('')):[];
  const show=g=>`<div class="lgc"><div class="fx">${g.map(x=>esc(x.name)).join(' ≡ ')}</div></div>`,same=(a,b)=>a.length===b.length&&a.every((g,i)=>g.length===b[i].length&&g.every((x,j)=>x===b[i][j]));
  C.push(`<h3>שקילות</h3>`+(eqAll.length?eqAll.map(show).join(''):'<p class="hint">אין שני פסוקים עם אותה עמודה בכל הלוח.</p>')+(given.length&&live&&eqLive.length&&!same(eqAll,eqLive)?`<div class="lgsub">בהינתן הנתונים, בשורות שנשארו:</div>`+eqLive.map(show).join(''):''));
  document.getElementById('card').innerHTML=`<div class="lgcard"><div class="cardhead"><h2>מה נובע</h2></div>${C.join('')}<p class="hint">לוח האמת עובר על כל ההצבות האפשריות, ולכן מה שמופיע כאן הוא הוכחה מלאה ולא הערכה.</p></div>`}
function renderAll(){fix();renderList();renderTable()}
document.addEventListener('change',ev=>{const t=ev.target;if(!t.closest||!t.closest('.lg'))return;const i=Number(t.dataset.i),k=t.dataset.k,x=L[i];if(!x||!k)return;
  if(k==='t'){if(t.value===x.t)return;if(t.value==='v'){if(vars().length>=MAXV){renderAll();return}x.t='v';x.op=x.a=x.b=undefined;rename(x,fresh('v'))}else{x.t='f';x.op='not';x.a=L[i-1].name;x.b=null;rename(x,fresh('f'))}}
  else if(k==='op'){x.op=t.value;if(OPS[x.op][2]===2&&!x.b)x.b=x.a}
  else x[k]=t.value;
  renderAll()});
document.addEventListener('click',ev=>{if(!ev.target.closest||!ev.target.closest('.lg'))return;const a=ev.target.closest('[data-add]'),d=ev.target.closest('[data-del]');
  if(a){if(a.dataset.add==='v'){if(vars().length<MAXV)L.push({name:fresh('v'),t:'v',given:'u'})}else if(L.length){const n=L.length;L.push({name:fresh('f'),t:'f',op:n>=2?'and':'not',a:L[n>=2?n-2:n-1].name,b:n>=2?L[n-1].name:null,given:'u'})}renderAll()}
  else if(d){L.splice(Number(d.dataset.del),1);renderAll()}});
return{
/* for tests: the table and the facts for a list of propositions, without touching the page */
solve(list){const keep=L;L=list.map(x=>Object.assign({given:'u'},x));try{const rows=table();return{rows:rows.map(r=>({vals:r.vals,ok:r.ok})),facts:facts(rows),texts:L.map(x=>text(x))}}finally{L=keep}},
render(){
  document.getElementById('conds').innerHTML=`<div class="qb lg"><div class="colhead"><h2>הפסוקים</h2><span class="lab">משתנים, קשרים ונתונים</span></div><div id="lgobjs" class="qlist"></div>
    <div class="qbox"><div class="lab">הוסף</div><div class="addrow" id="lgadd"></div><p class="hint">פסוק מורכב נבנה מפסוקים שמעליו ומקשר אחד. כדי לבנות פסוק ארוך, בונים אותו בשלבים.</p></div></div>`;
  renderAll()}};
})();
