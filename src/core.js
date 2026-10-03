/* ---------- core: data, graph properties, condition pipeline ---------- */
const B64='ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_';
const B64V={};for(let i=0;i<64;i++)B64V[B64[i]]=i;
const pc=x=>{x=x-((x>>1)&0x55555555);x=(x&0x33333333)+((x>>2)&0x33333333);return(((x+(x>>4))&0x0F0F0F0F)*0x01010101)>>24};
const low=x=>31-Math.clz32(x&-x);
const fact=n=>{let r=1;for(let i=2;i<=n;i++)r*=i;return r};
const falling=(n,k)=>{let r=1;for(let i=0;i<k;i++)r*=(n-i);return r};
const choose=(n,k)=>{let r=1;for(let i=1;i<=k;i++)r=r*(n-k+i)/i;return Math.round(r)};
const UNI={};
function universe(kind,n){
  const key=kind+n;if(UNI[key])return UNI[key];
  const [str,aut]=DATA[kind][n];const nb=n*(n-1)/2,L=Math.max(1,Math.ceil(nb/6)),N=aut.length,graphs=[],degc=[];
  for(let g=0;g<N;g++){
    const a=new Array(n).fill(0);let k=0;
    for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){if((B64V[str[g*L+(k/6|0)]]>>(k%6))&1){a[i]|=1<<j;a[j]|=1<<i}k++}
    graphs.push(a);const dc=new Array(n).fill(0);for(let i=0;i<n;i++)dc[pc(a[i])]++;degc.push(dc);
  }
  return UNI[key]={n,graphs,aut,degc,cache:{},comp:[],kind};
}
const compl=(a,n)=>{const full=(1<<n)-1;return a.map((x,i)=>~x&full&~(1<<i))};
function flood(a,start,allowed){let r=1<<start,fr=r;while(fr){let nx=0,f=fr;while(f){const v=low(f);f&=f-1;nx|=a[v]}nx&=allowed&~r;r|=nx;fr=nx}return r}
function nComps(a,n){let rem=(1<<n)-1,c=0;while(rem){rem&=~flood(a,low(rem),rem);c++}return c}
const nEdges=(a)=>{let s=0;for(const x of a)s+=pc(x);return s/2};
const degs=a=>a.map(pc);
function isBip(a,n){const col=new Int8Array(n).fill(-1);for(let s=0;s<n;s++){if(col[s]>=0)continue;col[s]=0;const st=[s];while(st.length){const v=st.pop();let nb=a[v];while(nb){const u=low(nb);nb&=nb-1;if(col[u]<0){col[u]=1-col[v];st.push(u)}else if(col[u]===col[v])return 0}}}return 1}
function diam(a,n){const full=(1<<n)-1;let best=0;for(let s=0;s<n;s++){let seen=1<<s,fr=seen,d=0;for(;;){let nx=0,f=fr;while(f){const v=low(f);f&=f-1;nx|=a[v]}nx&=~seen;if(!nx)break;d++;seen|=nx;fr=nx}if(seen!==full)return Infinity;if(d>best)best=d}return best}
function girth(a,n){let best=Infinity;for(let s=0;s<n;s++){const dist=new Int8Array(n).fill(-1),par=new Int8Array(n).fill(-1);dist[s]=0;const q=[s];for(let h=0;h<q.length;h++){const v=q[h];let nb=a[v];while(nb){const u=low(nb);nb&=nb-1;if(dist[u]<0){dist[u]=dist[v]+1;par[u]=v;q.push(u)}else if(par[v]!==u){const c=dist[u]+dist[v]+1;if(c<best)best=c}}}}return best}
function nTri(a,n){let t=0;for(let i=0;i<n;i++){let nb=a[i]>>>(i+1)<<(i+1);while(nb){const j=low(nb);nb&=nb-1;t+=pc(a[i]&a[j]&~((1<<(j+1))-1))}}return t}
function maxMatch(a,n){const memo=new Int8Array(1<<n).fill(-1);const f=m=>{if(!m)return 0;if(memo[m]>=0)return memo[m];const v=low(m),r=m&~(1<<v);let best=f(r),nb=a[v]&r;while(nb){const u=low(nb);nb&=nb-1;const t=1+f(r&~(1<<u));if(t>best)best=t}return memo[m]=best};return f((1<<n)-1)}
function maxMatchEdges(a,n){const memo=new Int8Array(1<<n).fill(-1);const f=m=>{if(!m)return 0;if(memo[m]>=0)return memo[m];const v=low(m),r=m&~(1<<v);let best=f(r),nb=a[v]&r;while(nb){const u=low(nb);nb&=nb-1;const t=1+f(r&~(1<<u));if(t>best)best=t}return memo[m]=best};
  const res=[];let m=(1<<n)-1;while(m){const v=low(m),r=m&~(1<<v);const tot=f(m);if(f(r)===tot){m=r;continue}let nb=a[v]&r;while(nb){const u=low(nb);nb&=nb-1;if(1+f(r&~(1<<u))===tot){res.push([v,u]);m=r&~(1<<u);break}}}return res}
function pmCount(a,n){if(n%2)return 0;const memo=new Int32Array(1<<n).fill(-1);const g=m=>{if(!m)return 1;if(memo[m]>=0)return memo[m];const v=low(m),r=m&~(1<<v);let s=0,nb=a[v]&r;while(nb){const u=low(nb);nb&=nb-1;s+=g(r&~(1<<u))}return memo[m]=s};return g((1<<n)-1)}
function minMaximal(a,n){const memo=new Int8Array(1<<n).fill(-1);const h=S=>{if(memo[S]>=0)return memo[S];let v=-1,t=S;while(t){const x=low(t);t&=t-1;if(a[x]&S){v=x;break}}if(v<0)return memo[S]=0;const u=low(a[v]&S);let best=99,nb=a[v]&S;while(nb){const w=low(nb);nb&=nb-1;best=Math.min(best,1+h(S&~(1<<v)&~(1<<w)))}nb=a[u]&S&~(1<<v);while(nb){const w=low(nb);nb&=nb-1;best=Math.min(best,1+h(S&~(1<<u)&~(1<<w)))}return memo[S]=best};return h((1<<n)-1)}
function alpha(a,n){const memo=new Int8Array(1<<n).fill(-1);const f=m=>{if(!m)return 0;if(memo[m]>=0)return memo[m];const v=low(m),r=m&~(1<<v);return memo[m]=Math.max(f(r),1+f(r&~a[v]))};return f((1<<n)-1)}
function chi(a,n){if(isBip(a,n))return nEdges(a)?2:1;for(let k=3;;k++){const col=new Int8Array(n).fill(-1);const go=(i,mx)=>{if(i===n)return true;let used=0,nb=a[i];while(nb){const u=low(nb);nb&=nb-1;if(col[u]>=0)used|=1<<col[u]}for(let c=0;c<k&&c<=mx+1;c++)if(!(used>>c&1)){col[i]=c;if(go(i+1,Math.max(mx,c)))return true;col[i]=-1}return false};if(go(0,-1))return k}}
function isHam(a,n){if(n<3)return 0;const reach=new Uint16Array(1<<n);reach[1]=1;const full=(1<<n)-1;for(let m=1;m<=full;m+=2){let e=reach[m];while(e){const v=low(e);e&=e-1;let nb=a[v]&~m;while(nb){const u=low(nb);nb&=nb-1;reach[m|(1<<u)]|=1<<u}}}return (reach[full]&a[0])?1:0}
function isEuler(a,n){if(nComps(a,n)!==1)return 0;for(const x of a)if(pc(x)&1)return 0;return 1}
function isoCount(a,b,n,stopAtOne){const da=degs(a),db=degs(b);const sa=[...da].sort(),sb=[...db].sort();for(let i=0;i<n;i++)if(sa[i]!==sb[i])return 0;const map=new Int8Array(n).fill(-1);let used=0,cnt=0;const go=i=>{if(i===n){cnt++;return}for(let v=0;v<n;v++){if(used>>v&1||db[v]!==da[i])continue;let ok=true;for(let j=0;j<i;j++){if(((a[i]>>j)&1)!==((b[v]>>map[j])&1)){ok=false;break}}if(!ok)continue;map[i]=v;used|=1<<v;go(i+1);used&=~(1<<v);map[i]=-1;if(stopAtOne&&cnt)return}};go(0);return cnt}
const PROP={
  edges:(a,n)=>nEdges(a),
  maxdeg:(a,n)=>Math.max(0,...degs(a)),
  mindeg:(a,n)=>Math.min(...degs(a)),
  comps:(a,n)=>nComps(a,n),
  conn:(a,n)=>nComps(a,n)===1?1:0,
  forest:(a,n)=>nEdges(a)===n-nComps(a,n)?1:0,
  tree:(a,n)=>(nComps(a,n)===1&&nEdges(a)===n-1)?1:0,
  bip:isBip,
  regular:(a,n)=>{const d=degs(a);return Math.max(...d)===Math.min(...d)?1:0},
  euler:isEuler,ham:isHam,diam,girth,tri:nTri,mm:maxMatch,
  pmc:pmCount,pm:(a,n)=>pmCount(a,n)>0?1:0,
  minmax:minMaximal,stuck:(a,n)=>minMaximal(a,n)<maxMatch(a,n)?1:0,
  alpha,omega:(a,n)=>alpha(compl(a,n),n),chi,
  leaves:(a,n)=>degs(a).filter(d=>d===1).length,
  degcount:(a,n,d)=>degs(a).filter(x=>x===d).length,
  selfc:(a,n)=>isoCount(a,compl(a,n),n,true)?1:0
};
const IND={
  indep:(a,S,k)=>{let t=S;while(t){const v=low(t);t&=t-1;if(a[v]&S)return false}return true},
  clique:(a,S,k)=>{let t=S;while(t){const v=low(t);t&=t-1;if((a[v]&S)!==(S&~(1<<v)))return false}return true},
  conn:(a,S,k)=>flood(a,low(S),S)===S,
  tree:(a,S,k)=>{let e=0,t=S;while(t){const v=low(t);t&=t-1;e+=pc(a[v]&S)}return e/2===k-1&&flood(a,low(S),S)===S},
  cycle:(a,S,k)=>{if(k<3)return false;let t=S;while(t){const v=low(t);t&=t-1;if(pc(a[v]&S)!==2)return false}return flood(a,low(S),S)===S},
  path:(a,S,k)=>{let e=0,t=S;while(t){const v=low(t);t&=t-1;const d=pc(a[v]&S);if(d>2)return false;e+=d}return e/2===k-1&&flood(a,low(S),S)===S}
};
function indCount(a,n,prop,k){const full=(1<<n)-1,f=IND[prop];let c=0;for(let S=1;S<full;S++){const sz=pc(S);if(k&&sz!==k)continue;if(f(a,S,sz))c++}return c}
function condValue(a,n,c){
  if(c.kind==='ind')return indCount(a,n,c.prop,c.k);
  const K=KIND[c.kind];const g=c.target==='C'?compl(a,n):a;return PROP[K.prop](g,n,c.extra);
}
function values(U,c){
  const key=c.kind==='ind'?`ind|${c.prop}|${c.k}`:`${c.target}|${c.kind}|${c.extra}`;
  if(U.cache[key])return U.cache[key];
  const arr=new Array(U.graphs.length);for(let i=0;i<arr.length;i++)arr[i]=condValue(U.graphs[i],U.n,c);
  return U.cache[key]=arr;
}
const cmp=(x,op,v)=>op==='eq'?x===v:op==='le'?x<=v:x>=v;
function tuples(dc,dem){if(!dem.size)return 1;const need={};for(const d of dem.values())need[d]=(need[d]||0)+1;let r=1;for(const d in need)r*=falling(dc[d]||0,need[d]);return r}
/* run the ordered list of enabled conditions; returns survivors and per-step counts */
function run(U,type,conds){
  const N=U.graphs.length,n=U.n,alive=new Uint8Array(N).fill(1);
  if(U.kind==='G'&&type!=='general'){const arr=values(U,{kind:type==='tree'?'tree':'bip',target:'G'});for(let i=0;i<N;i++)if(!arr[i])alive[i]=0}
  const dem=new Map();let dead=false;const nf=fact(n);
  const count=()=>{let u=0,l=0;if(!dead){const den=falling(n,dem.size);for(let i=0;i<N;i++)if(alive[i]){u++;l+=nf/U.aut[i]*tuples(U.degc[i],dem)/den}}return{u,l:Math.round(l)}};
  const base=count(),steps=[];
  for(const c of conds){
    if(c.kind==='vdeg'){
      if(dem.has(c.v)&&dem.get(c.v)!==c.d)dead=true;else dem.set(c.v,c.d);
      if(!dead)for(let i=0;i<N;i++)if(alive[i]&&!tuples(U.degc[i],dem))alive[i]=0;
    }else{const arr=values(U,c);for(let i=0;i<N;i++)if(alive[i]&&!cmp(arr[i],c.op,c.value))alive[i]=0}
    steps.push(count());
  }
  if(dead)alive.fill(0);
  const fin=steps.length?steps[steps.length-1]:base;
  const den=falling(n,dem.size);
  const weight=i=>Math.round(nf/U.aut[i]*tuples(U.degc[i],dem)/den);
  return{alive,base,steps,fin,dem,weight};
}
/* condition kinds */
const KIND={
  conn:{cat:'מבנה',label:'קשיר',type:'bool',prop:'conn'},
  tree:{cat:'מבנה',label:'עץ',type:'bool',prop:'tree'},
  forest:{cat:'מבנה',label:'חסר מעגלים',type:'bool',prop:'forest'},
  bip:{cat:'מבנה',label:'דו-צדדי',type:'bool',prop:'bip'},
  edges:{cat:'מבנה',label:'מספר צלעות',type:'num',prop:'edges',max:n=>n*(n-1)/2,def:n=>n-1,op:'eq'},
  comps:{cat:'מבנה',label:'מספר רכיבי קשירות',type:'num',prop:'comps',min:1,max:n=>n,def:n=>1,op:'eq'},
  diam:{cat:'מבנה',label:'קוטר',type:'num',prop:'diam',max:n=>n-1,def:n=>2,op:'le'},
  girth:{cat:'מבנה',label:'אורך המעגל הקצר ביותר',type:'num',prop:'girth',min:3,max:n=>Math.max(3,n),def:n=>3,op:'eq'},
  tri:{cat:'מבנה',label:'מספר משולשים',type:'num',prop:'tri',max:n=>choose(n,3),def:n=>0,op:'eq'},
  euler:{cat:'מבנה',label:'יש מעגל אוילר',type:'bool',prop:'euler'},
  ham:{cat:'מבנה',label:'יש מעגל המילטון',type:'bool',prop:'ham'},
  chi:{cat:'מבנה',label:'מספר צביעה',type:'num',prop:'chi',min:1,max:n=>n,def:n=>2,op:'eq'},
  alpha:{cat:'מבנה',label:'גודל קבוצה בלתי תלויה מקסימלית',type:'num',prop:'alpha',min:1,max:n=>n,def:n=>2,op:'eq'},
  omega:{cat:'מבנה',label:'גודל קליקה מקסימלית',type:'num',prop:'omega',min:1,max:n=>n,def:n=>2,op:'eq'},
  maxdeg:{cat:'דרגות',label:'דרגה מקסימלית',type:'num',prop:'maxdeg',max:n=>n-1,def:n=>Math.min(3,n-1),op:'le'},
  mindeg:{cat:'דרגות',label:'דרגה מינימלית',type:'num',prop:'mindeg',max:n=>n-1,def:n=>1,op:'ge'},
  regular:{cat:'דרגות',label:'רגולרי',type:'bool',prop:'regular'},
  leaves:{cat:'דרגות',label:'מספר עלים',type:'num',prop:'leaves',max:n=>n,def:n=>2,op:'eq'},
  degcount:{cat:'דרגות',label:'מספר צמתים בדרגה נתונה',type:'num',prop:'degcount',max:n=>n,def:n=>1,op:'eq',extra:{label:'דרגה',max:n=>n-1,def:n=>Math.min(2,n-1)}},
  vdeg:{cat:'דרגות',label:'דרגת צומת מסוים',type:'vdeg',noTarget:true},
  mm:{cat:'זיווגים',label:'גודל זיווג מקסימלי',type:'num',prop:'mm',max:n=>n>>1,def:n=>n>>1,op:'eq'},
  pm:{cat:'זיווגים',label:'קיים זיווג מושלם',type:'bool',prop:'pm'},
  pmc:{cat:'זיווגים',label:'מספר זיווגים מושלמים',type:'num',prop:'pmc',max:n=>n%2?0:[1,1,3,15,105,945,10395][n/2],def:n=>1,op:'eq'},
  stuck:{cat:'זיווגים',label:'קיים זיווג תקוע עם מסלול שיפור',type:'bool',prop:'stuck',hint:'זיווג שאי אפשר להוסיף לו צלע, אבל הוא לא מקסימלי'},
  selfc:{cat:'משלים',label:'איזומורפי למשלים שלו',type:'bool',prop:'selfc',noTarget:true},
  ind:{cat:'תת-גרפים מושרים',label:'תת-קבוצות צמתים עם תכונה',type:'ind',noTarget:true}
};
const IND_LABEL={indep:'בלתי תלויה',clique:'קליקה',conn:'קשירה',tree:'עץ',cycle:'מעגל',path:'מסלול'};
if(typeof module!=='undefined')module.exports={universe,run,KIND,PROP,compl,isoCount,maxMatchEdges,indCount};
