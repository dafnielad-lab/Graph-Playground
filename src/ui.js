/* ---------- UI ---------- */
const SHOWS=[20,50,100,200,500,1000],LIVE=50;
const $=s=>document.querySelector(s);
const fmt=x=>x===Infinity?'∞':Number(x).toLocaleString('en-US');
const esc=s=>String(s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const S={type:'general',labeled:false,n:6,mode:'explore',nextId:1,conds:[],sel:null,showComp:false,showMatch:true,showLabels:false,layout:'auto',sample:false,show:50,
  guess:{val:'',revealed:false},target:null,tool:'subset',subset:0,matching:[],augPath:null,manual:null,manualPick:-1,menuOpen:false,condsOpen:true};
function mkCond(kind,over){
  const K=KIND[kind],n=nHi(),c={id:S.nextId++,kind,on:true,target:'G'};
  if(K.type==='bool'){c.op='eq';c.value=1}
  else if(K.type==='num'){c.op=K.op;c.value=K.def(n);if(K.extra)c.extra=K.extra.def(n)}
  else if(K.type==='vdeg'){c.v=1;c.d=1}
  else if(K.type==='cut'){c.what='e';c.k=1;c.q='ex'}
  else if(K.type==='ind'){c.prop='indep';c.k=Math.min(2,n-1);c.op='ge';c.value=1}
  return Object.assign(c,over||{});
}
const single=()=>S.mode==='manual'||S.mode==='prufer';const sheetMode=()=>S.mode==='sheet';
const ranged=()=>!!S.rng&&!single(),nHi=()=>ranged()?Math.max(S.n,S.n2||S.n):S.n,Ns=()=>{const r=[];for(let n=S.n;n<=nHi();n++)r.push(n);return r};
S.conds=[mkCond('conn'),mkCond('edges',{value:5}),mkCond('maxdeg',{value:3}),mkCond('pm',{on:false})];
const maxN=()=>S.mode==='prufer'?12:S.mode==='manual'?8:(S.type==='tree'?12:8);
const curU=n=>S.type==='tree'&&n>8?universe('T',n):universe('G',n);
const numMin=c=>c.kind==='cut'?1:KIND[c.kind].min||0;
const numMax=c=>{const n=nHi();return c.kind==='cut'?Math.max(1,c.what==='e'?n*(n-1)/2:n-1):c.kind==='ind'?(c.k?choose(n,c.k):(1<<n)-2):KIND[c.kind].max(n)};
function clampConds(){const n=nHi();for(const c of S.conds){const K=KIND[c.kind];
  if(K.type==='num'){c.value=Math.max(numMin(c),Math.min(numMax(c),c.value));if(K.extra)c.extra=Math.min(K.extra.max(n),c.extra)}
  if(K.type==='vdeg'){c.v=Math.min(n,c.v);c.d=Math.min(n-1,c.d)}
  if(K.type==='cut')c.k=Math.max(1,Math.min(numMax(c),c.k));
  if(K.type==='ind'){c.k=Math.min(Math.max(n-1,0),c.k);c.value=Math.min(numMax(c),c.value)}}}

/* ----- layout & drawing ----- */
const LAY={};
function layout(a,n,mode){
  const key=mode+n+':'+a.join(',');if(LAY[key])return LAY[key];
  const P=[];for(let i=0;i<n;i++){const t=-Math.PI/2+2*Math.PI*i/n;P.push([Math.cos(t),Math.sin(t)])}
  if(n===1)P[0]=[0,0];
  if(mode==='auto'&&n>2){
    // order the start circle by BFS so neighbours begin close together
    const ord=[];let seen=0;for(let s=0;s<n;s++){if(seen>>s&1)continue;const q=[s];seen|=1<<s;for(let h=0;h<q.length;h++){ord.push(q[h]);let nb=a[q[h]]&~seen;while(nb){const u=low(nb);nb&=nb-1;seen|=1<<u;q.push(u)}}}
    const Q=new Array(n);ord.forEach((v,i)=>{const t=2*Math.PI*i/n;Q[v]=[Math.cos(t)+0.01*i,Math.sin(t)]});
    const k=1.1;let T=0.35;
    for(let it=0;it<260;it++){
      const D=Q.map(()=>[0,0]);
      for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){let dx=Q[i][0]-Q[j][0],dy=Q[i][1]-Q[j][1],d=Math.hypot(dx,dy)||0.01;let f=k*k/d;if(a[i]>>j&1)f-=d*d/k;const fx=dx/d*f,fy=dy/d*f;D[i][0]+=fx;D[i][1]+=fy;D[j][0]-=fx;D[j][1]-=fy}
      for(let i=0;i<n;i++){D[i][0]-=Q[i][0]*0.35;D[i][1]-=Q[i][1]*0.35;const d=Math.hypot(D[i][0],D[i][1])||0.01,s=Math.min(d,T)/d;Q[i][0]+=D[i][0]*s;Q[i][1]+=D[i][1]*s}
      T*=0.985;
    }
    for(let i=0;i<n;i++)P[i]=Q[i];
  }
  return LAY[key]=fit(P);
}
function fit(P){
  let x0=Infinity,x1=-Infinity,y0=Infinity,y1=-Infinity;for(const p of P){x0=Math.min(x0,p[0]);x1=Math.max(x1,p[0]);y0=Math.min(y0,p[1]);y1=Math.max(y1,p[1])}
  const w=Math.max(x1-x0,0.001),h=Math.max(y1-y0,0.001),sc=Math.min(160/w,116/h,80);
  return P.map(p=>[100+(p[0]-(x0+x1)/2)*sc,75+(p[1]-(y0+y1)/2)*sc]);
}
/* ----- planar straight-line drawing of one component: helper vertices triangulate every face,
   Tutte barycentres give a crossing-free start, then a relaxation that never flips a triangle ----- */
function drawComp(rot,verts,faces,outer){
  const nv=verts.length;if(nv===1)return[[0,0]];if(nv===2)return[[-.5,0],[.5,0]];
  const id=new Map();verts.forEach((v,i)=>id.set(v,i));let N=nv;const nb=[],T=[],fix=new Map();
  const add=(x,y)=>{(nb[x]=nb[x]||new Set()).add(y);(nb[y]=nb[y]||new Set()).add(x)};
  for(const v of verts)for(const u of rot[v])add(id.get(v),id.get(u));
  faces.forEach((w,fi)=>{const k=w.length,L=w.map(v=>id.get(v));
    if(fi!==outer&&k===3){T.push(L);return}
    const d0=N;N+=k;
    for(let i=0;i<k;i++){const d=d0+i,d2=d0+(i+1)%k,x=L[i],y=L[(i+1)%k];add(d,x);add(d,y);add(d,d2);T.push([x,y,d],[d,y,d2])}
    if(fi===outer)for(let i=0;i<k;i++){const t=-Math.PI/2+2*Math.PI*(i+.5)/k;fix.set(d0+i,[1.35*Math.cos(t),Math.sin(t)])}
    else{const c=N++;for(let i=0;i<k;i++){add(c,d0+i);T.push([d0+i,d0+(i+1)%k,c])}}
  });
  const free=[],at=new Int16Array(N).fill(-1);for(let i=0;i<N;i++)if(!fix.has(i)){at[i]=free.length;free.push(i)}
  const U=free.length,M=free.map(()=>new Float64Array(U+2));
  free.forEach((i,r)=>{M[r][r]=nb[i].size;for(const j of nb[i]){if(at[j]>=0)M[r][at[j]]-=1;else{const f=fix.get(j);M[r][U]+=f[0];M[r][U+1]+=f[1]}}});
  for(let c=0;c<U;c++){const pv=M[c][c];for(let r=c+1;r<U;r++){const f=M[r][c]/pv;if(f){const Mr=M[r],Mc=M[c];for(let k=c;k<U+2;k++)Mr[k]-=f*Mc[k]}}}
  const P=new Array(N);for(const [i,f] of fix)P[i]=f;
  for(let r=U-1;r>=0;r--){let x=M[r][U],y=M[r][U+1];for(let k=r+1;k<U;k++){x-=M[r][k]*P[free[k]][0];y-=M[r][k]*P[free[k]][1]}P[free[r]]=[x/M[r][r],y/M[r][r]]}
  /* spread the vertices: forces move one vertex at a time, and a move is kept only if it creates
     no crossing and leaves the cyclic order of neighbours unchanged, so the embedding is preserved */
  const Q=P.slice(0,nv),R=verts.map(v=>rot[v].map(u=>id.get(u))),E=[];for(let i=0;i<nv;i++)for(const j of R[i])if(i<j)E.push([i,j]);
  let x0=Infinity,x1=-Infinity,y0=Infinity,y1=-Infinity;for(const q of Q){x0=Math.min(x0,q[0]);x1=Math.max(x1,q[0]);y0=Math.min(y0,q[1]);y1=Math.max(y1,q[1])}
  const sc=Math.sqrt(nv)/Math.max(x1-x0,y1-y0,1e-9);for(const q of Q){q[0]=(q[0]-x0)*sc;q[1]=(q[1]-y0)*sc}
  const o=(a,b,c)=>(b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0]);
  const order=x=>{const r=R[x],k=r.length;if(k<3)return 0;const s=r.map(u=>[Math.atan2(Q[u][1]-Q[x][1],Q[u][0]-Q[x][0]),u]).sort((a,b)=>a[0]-b[0]).map(t=>t[1]),i0=s.indexOf(r[0]);
    let f=1,b=1;for(let j=1;j<k;j++){if(s[(i0+j)%k]!==r[j])f=0;if(s[(i0-j+k)%k]!==r[j])b=0}return f?1:b?-1:2};
  let hand=0;for(let i=0;i<nv&&!hand;i++){const h=order(i);if(h===1||h===-1)hand=h}
  const okAt=x=>R[x].length<3||order(x)===hand;
  const valid=v=>{for(const u of R[v])for(const e of E){const c=e[0],d=e[1];if(c===v||d===v)continue;
      if(c===u||d===u){const w=c===u?d:c;if(Math.abs(o(Q[u],Q[v],Q[w]))<1e-9&&(Q[v][0]-Q[u][0])*(Q[w][0]-Q[u][0])+(Q[v][1]-Q[u][1])*(Q[w][1]-Q[u][1])>0)return false;continue}
      if(o(Q[v],Q[u],Q[c])*o(Q[v],Q[u],Q[d])<=0&&o(Q[c],Q[d],Q[v])*o(Q[c],Q[d],Q[u])<=0)return false}
    if(!okAt(v))return false;for(const u of R[v])if(!okAt(u))return false;return true};
  const D=Q.map(()=>[0,0]);let temp=.3;
  for(let it=0;it<140;it++){
    for(const d of D){d[0]=0;d[1]=0}
    for(let i=0;i<nv;i++)for(let j=i+1;j<nv;j++){const ex=Q[i][0]-Q[j][0],ey=Q[i][1]-Q[j][1],d=Math.hypot(ex,ey)||1e-4;let f=.6/d;if(R[i].includes(j))f-=d*d;const fx=ex/d*f,fy=ey/d*f;D[i][0]+=fx;D[i][1]+=fy;D[j][0]-=fx;D[j][1]-=fy}
    for(let v=0;v<nv;v++)for(const e of E){const c=e[0],b=e[1];if(c===v||b===v)continue;const A=Q[c],dx=Q[b][0]-A[0],dy=Q[b][1]-A[1];let t=((Q[v][0]-A[0])*dx+(Q[v][1]-A[1])*dy)/(dx*dx+dy*dy||1e-9);t=Math.max(0,Math.min(1,t));
      const ex=Q[v][0]-A[0]-t*dx,ey=Q[v][1]-A[1]-t*dy,d=Math.hypot(ex,ey)||1e-4;if(d<.9){const f=(.9-d)*(.9-d)/d*1.6,fx=ex/d*f,fy=ey/d*f;D[v][0]+=fx;D[v][1]+=fy;D[c][0]-=fx*(1-t);D[c][1]-=fy*(1-t);D[b][0]-=fx*t;D[b][1]-=fy*t}}
    for(let v=0;v<nv;v++){const d=Math.hypot(D[v][0],D[v][1]);if(d<1e-7)continue;let s=Math.min(d,temp)/d;const ox=Q[v][0],oy=Q[v][1];
      let done=false;for(let tr=0;tr<5&&!done;tr++,s/=2){Q[v][0]=ox+D[v][0]*s;Q[v][1]=oy+D[v][1]*s;if(valid(v))done=true;else{Q[v][0]=ox;Q[v][1]=oy}}
      for(let tr=0;tr<4&&!done;tr++){const g=(tr&1?-1:1)*temp/d/(tr<2?2:8);Q[v][0]=ox-D[v][1]*g;Q[v][1]=oy+D[v][0]*g;if(valid(v))done=true;else{Q[v][0]=ox;Q[v][1]=oy}}}
    temp=Math.max(.02,temp*.975);
  }
  return Q;
}
/* rot: rotation system; outerSel: index of the outer face in faceWalks (connected graphs only) */
function planarLayout(a,n,rot,outerSel){
  const F=faceWalks(rot,n),comps=[];let rem=(1<<n)-1;while(rem){const c=flood(a,low(rem),rem);rem&=~c;comps.push(c)}
  const boxes=comps.map(c=>{const verts=[];for(let i=0;i<n;i++)if(c>>i&1)verts.push(i);
    const fs=F.filter(w=>c>>w[0]&1);let outer=0;fs.forEach((w,i)=>{if(w.length>fs[outer].length)outer=i});
    if(comps.length===1&&outerSel!==undefined)outer=outerSel;
    const Q=drawComp(rot,verts,fs,outer);let x0=Infinity,x1=-Infinity,y0=Infinity,y1=-Infinity;for(const q of Q){x0=Math.min(x0,q[0]);x1=Math.max(x1,q[0]);y0=Math.min(y0,q[1]);y1=Math.max(y1,q[1])}
    const s=verts.length===1?.5:Math.sqrt(verts.length),sc=Math.min(1.35*s/Math.max(x1-x0,.01),s/Math.max(y1-y0,.01));
    return{verts,Q:Q.map(q=>[(q[0]-x0)*sc,(q[1]-y0)*sc]),w:Math.max((x1-x0)*sc,.3),h:Math.max((y1-y0)*sc,.3)}});
  const P=new Array(n);
  if(boxes.length===1){boxes[0].verts.forEach((v,i)=>P[v]=boxes[0].Q[i])}
  else{boxes.sort((x,y)=>y.h-x.h||y.w-x.w);let A=0;for(const b of boxes)A+=(b.w+.5)*(b.h+.5);const W=Math.max(Math.sqrt(A*1.5),boxes[0].w+.5);
    let x=0,y=0,rowH=0;for(const b of boxes){if(x>0&&x+b.w>W){x=0;y+=rowH+.6;rowH=0}b.verts.forEach((v,i)=>P[v]=[x+b.Q[i][0],y+(b.h<rowH?(rowH-b.h)/2:0)+b.Q[i][1]]);x+=b.w+.6;rowH=Math.max(rowH,b.h)}}
  return fit(P);
}
const EMB=new Map();
function embInfo(a,n){const key=n+':'+a.join(',');let e=EMB.get(key);if(e===undefined){if(EMB.size>300)EMB.clear();e=isPlanar(a,n)?embeddings(a,n):null;EMB.set(key,e)}return e}
/* default planar picture for the gallery: first embedding, longest face outside; falls back when not planar */
function planarPos(a,n){
  const key='planar'+n+':'+a.join(',');if(key in LAY)return LAY[key];
  let rot=null;if(isPlanar(a,n))embedAll(a,n,1,r=>{rot=r.map(x=>x.slice())});
  return LAY[key]=rot?planarLayout(a,n,rot):null;
}
const ekey=(i,j)=>i<j?i+'-'+j:j+'-'+i;
/* o: {cls, pos, match:Set, path:Set, subset:mask, labels, hit, r} */
function svgGraph(a,n,o){const kb=o.kur?o.kur.b:null;
  const P=o.pos,r=o.r||7;let e='',hit='',v='';
  for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)if(a[i]>>j&1){
    const k=ekey(i,j);let cls='e';
    if(o.match&&o.match.has(k))cls+=' m';
    if(o.path&&o.path.has(k))cls+=' p';
    if(o.subset&&(o.subset>>i&1)&&(o.subset>>j&1))cls+=' s';
    if(kb&&kb[i]>>j&1)cls+=' k';
    const L=`x1="${P[i][0].toFixed(1)}" y1="${P[i][1].toFixed(1)}" x2="${P[j][0].toFixed(1)}" y2="${P[j][1].toFixed(1)}"`;
    e+=`<line class="${cls}" ${L}/>`;if(o.hit==='edge')hit+=`<line class="hit" data-act="edge" data-e="${k}" ${L}/>`;
  }
  for(let i=0;i<n;i++){
    const sel=o.subset&&(o.subset>>i&1)||o.pick===i;
    v+=`<g ${o.hit==='vertex'?`class="vh" data-act="vertex" data-v="${i}" tabindex="0" role="button" aria-label="צומת ${i+1}"`:''}><circle class="v${sel?' sel':''}${o.kur&&o.kur.branch>>i&1?' kb':''}" cx="${P[i][0].toFixed(1)}" cy="${P[i][1].toFixed(1)}" r="${r}"/>${o.labels?`<text class="vl${sel?' sel':''}" x="${P[i][0].toFixed(1)}" y="${(P[i][1]+3.2).toFixed(1)}">${i+1}</text>`:''}</g>`;
  }
  return `<svg class="g ${o.cls||''}" viewBox="0 0 200 150" role="img" aria-label="${esc(o.aria||'גרף')}">${e}${hit}${v}</svg>`;
}

/* ----- pipeline state ----- */
let R=null,ITEMS=[];
function pruferTree(seq,n){const deg=new Array(n).fill(1),a=new Array(n).fill(0);for(const v of seq)deg[v-1]++;
  const link=(i,j)=>{a[i]|=1<<j;a[j]|=1<<i};
  for(const v of seq){let leaf=0;while(deg[leaf]!==1)leaf++;link(leaf,v-1);deg[leaf]--;deg[v-1]--}
  const rest=[];for(let i=0;i<n;i++)if(deg[i]===1)rest.push(i);if(rest.length===2)link(rest[0],rest[1]);return a}
function syncPrufer(){const n=S.n,L=Math.max(0,n-2);if(!S.prufer){S.prufer=Array.from({length:L},(_,i)=>(i*2)%n+1);if(L>=3)S.prufer[2]='x'}
  S.prufer=Array.from({length:L},(_,i)=>{const t=S.prufer[i];return t===undefined?1:typeof t==='number'?Math.min(n,t):t})}
function runAll(conds){const parts=Ns().map(n=>{const U=curU(n);return{U,r:run(U,S.type,conds)}}),z={u:0,l:0},add=(x,y)=>({u:x.u+y.u,l:x.l+y.l});
  return{parts,base:parts.reduce((t,p)=>add(t,p.r.base),z),steps:conds.map((_,i)=>parts.reduce((t,p)=>add(t,p.r.steps[i]),z)),fin:parts.reduce((t,p)=>add(t,p.r.fin),z)}}
const cutOf=list=>list.find(c=>c.kind==='cut'),isBelow=(c,list)=>{const k=cutOf(list);return !!k&&list.indexOf(c)>list.indexOf(k)};
function compute(){
  if(S.mode==='prufer'){const n=S.n,vars=['x','y'].filter(v=>S.prufer.includes(v));ITEMS=[];
    const rg=k=>vars.length>k?Array.from({length:n},(_,i)=>i+1):[0];
    for(const x of rg(0))for(const y of rg(1)){const val={};if(vars[0])val[vars[0]]=x;if(vars[1])val[vars[1]]=y;const seq=S.prufer.map(t=>typeof t==='number'?t:val[t]);
      ITEMS.push({a:pruferTree(seq,n),idx:-1,w:1,n,seq,cap:vars.map(v=>v+' = '+val[v]).join(',  ')})}
    R={r:null,info:{},galleryKind:'prufer'};if(S.sel===null||S.sel>=ITEMS.length)S.sel=0;return}
  const on=S.conds.filter(c=>c.on),r=runAll(on);
  const stepOf={};on.forEach((c,i)=>stepOf[c.id]=r.steps[i]);
  const info={};const key=x=>x.u+'/'+x.l;
  for(const c of S.conds){
    if(c.on){const w=runAll(on.filter(x=>x!==c)),wo=w.fin;info[c.id]={step:stepOf[c.id],redundant:key(wo)===key(r.fin),woN:wo.u,ok:okValues(c,w,on)}}
    else info[c.id]={ifOn:runAll(S.conds.filter(y=>y.on||y===c)).fin};
  }
  if(r.fin.u===0&&on.length>1&&!on.some(c=>info[c.id].woN>0)){
    for(let i=0;i<on.length;i++)for(let j=i+1;j<on.length;j++)if(runAll(on.filter(x=>x!==on[i]&&x!==on[j])).fin.u>0){
      (info[on[i].id].partners=info[on[i].id].partners||[]).push(KIND[on[j].kind].label);(info[on[j].id].partners=info[on[j].id].partners||[]).push(KIND[on[i].kind].label)}
  }
  R={r,info};
  // gallery items, over every vertex count in the range
  const idx=[];for(const p of r.parts)for(let i=0;i<p.r.alive.length;i++)if(p.r.alive[i])idx.push([p,i]);
  const item=([p,i])=>({a:p.U.graphs[i],idx:i,w:p.r.weight(i),n:p.U.n,U:p.U});
  ITEMS=[];R.galleryKind='none';
  if(S.labeled&&r.fin.l<=S.show&&r.fin.l>0){
    let tot=0;for(const [p,i] of idx)tot+=fact(p.U.n)/p.U.aut[i];
    if(tot<=60000){R.galleryKind='labeled';for(const [p,i] of idx)for(const g of orbit(p.U.graphs[i],p.U.n)){let ok=true;for(const [v,d] of p.r.dem)if(pc(g[v-1])!==d)ok=false;if(ok)ITEMS.push({a:g,idx:i,w:1,n:p.U.n,U:p.U})}}
  }
  if(R.galleryKind==='none'){
    if(idx.length<=S.show){R.galleryKind='all';ITEMS=idx.map(item)}
    else{R.galleryKind='many';if(S.sample)ITEMS=idx.slice(0,S.show).map(item)}
  }
  if(S.sel!==null&&S.sel>=ITEMS.length)S.sel=ITEMS.length?0:null;
  if(S.sel===null&&ITEMS.length)S.sel=0;
}
const runsTxt=vals=>{const out=[];for(let i=0;i<vals.length;i++){let j=i;while(j+1<vals.length&&vals[j+1]===vals[j]+1)j++;out.push(j>i?`<b class="num">${vals[i]}</b> עד <b class="num">${vals[j]}</b>`:`<b class="num">${vals[i]}</b>`);i=j}return out.length>10?out.slice(0,10).join(', ')+' ועוד':out.join(', ')};
/* values of this condition alone (others fixed) that leave at least one graph */
function okValues(c,wo,on){
  const K=KIND[c.kind],below=isBelow(c,on),alt=o=>runAll(on.map(x=>x===c?{...c,...o}:x)).fin.u>0;
  if(K.type==='bool')return null;
  if(K.type==='vdeg'){if(below)return null;const r=[];for(let d=0;d<nHi();d++)if(alt({d}))r.push(d);return r}
  const lo=K.type==='ind'?0:numMin(c),hi=numMax(c);
  if(K.type==='cut'){const r=[];for(let k=lo;k<=hi;k++)if(alt({k}))r.push(k);return r}
  if(below){if(hi-lo>40)return null;const r=[];for(let v=lo;v<=hi;v++)if(alt({value:v}))r.push(v);return r}
  let mn=Infinity,mx=-Infinity;const set=new Set();
  for(const p of wo.parts){const arr=values(p.U,c);for(let i=0;i<arr.length;i++)if(p.r.alive[i]){const v=arr[i];set.add(v);if(v<mn)mn=v;if(v>mx)mx=v}}
  const r=[];for(let v=lo;v<=hi;v++)if(c.op==='eq'?set.has(v):c.op==='le'?v>=mn:v<=mx)r.push(v);return r;
}
function orbit(a,n){const seen=new Map(),q=[a];seen.set(a.join(','),a);for(let h=0;h<q.length;h++){const g=q[h];for(let i=0;i<n-1;i++){const j=i+1,sw=x=>{const bi=x>>i&1,bj=x>>j&1;return (x&~(1<<i)&~(1<<j))|(bj<<i)|(bi<<j)};const b=g.map(sw);const t=b[i];b[i]=b[j];b[j]=t;const k=b.join(',');if(!seen.has(k)){seen.set(k,b);q.push(b)}}}return q}
function evalSingle(a,n,c){
  if(c.kind==='cut'){if(n>8)return null;const U=universe('G',n),need=new Uint8Array(U.graphs.length),i=gIndex(a,n);need[i]=1;return !!cutEval(U,c,belowOf(c),need)[i]}
  if(isBelow(c,S.conds))return null;
  if(c.kind==='vdeg')return pc(a[c.v-1])===c.d;
  return cmp(condValue(a,n,c),c.op,c.value);
}
const belowOf=cut=>S.conds.slice(S.conds.indexOf(cut)+1).filter(c=>c.on&&c.kind!=='vdeg'&&c.kind!=='cut');
function manualGraph(){if(!S.manual||S.manual.length!==S.n)S.manual=new Array(S.n).fill(0);return S.manual}
function selGraph(){if(S.mode==='manual')return{a:manualGraph(),idx:-1,n:S.n};if(S.sel===null||!ITEMS[S.sel])return null;return ITEMS[S.sel]}

/* ----- render: top bar ----- */
const seg=(act,opts,cur)=>`<div class="seg">${opts.map(([v,l])=>`<button data-act="${act}" data-v="${v}" aria-pressed="${v===cur}">${l}</button>`).join('')}</div>`;
const nStep=(w,val,lo,hi)=>`<div class="seg step"><button data-act="n" data-w="${w}" data-v="-1" aria-label="הפחת צומת" ${val<=lo?'disabled':''}>−</button><b class="num" aria-live="polite">${val}</b><button data-act="n" data-w="${w}" data-v="1" aria-label="הוסף צומת" ${val>=hi?'disabled':''}>+</button></div>`;
function renderTop(){
  $('.cols').classList.toggle('sheet',sheetMode());
  $('#top').innerHTML=`<div class="grp"><div class="brand">מגרש גרפים</div><button class="btn sm" data-act="conds" aria-pressed="${S.condsOpen}" aria-controls="conds">תנאים</button></div>
  ${sheetMode()?'':`<div class="grp"><span class="lab">סוג</span>${seg('type',[['general','גרף כללי'],['tree','עץ'],['bip','דו-צדדי']],S.type)}</div>
  <div class="grp"><span class="lab">ספירה</span>${seg('lab',[['0','לא מתויג'],['1','מתויג']],S.labeled?'1':'0')}</div>
  <div class="grp"><span class="lab">צמתים</span>${nStep('lo',S.n,1,ranged()?S.n2:maxN())}${ranged()?`<span class="lab">עד</span>${nStep('hi',S.n2,S.n,maxN())}`:''}${single()?'':`<button class="btn sm" data-act="rng" aria-pressed="${!!S.rng}">טווח</button>`}<span class="lab">לכל היותר <span class="num">${maxN()}</span></span></div>`}
  <div class="grp end"><span class="lab">מצב</span>${seg('mode',[['explore','חקירה חופשית'],['guess','ניחוש'],['target','יעד'],['manual','גרף ידני'],['prufer','סדרת פרופר'],['sheet','דף נוסחאות']],S.mode)}<button class="btn" data-act="help" aria-expanded="${!$('#help').hidden}" aria-controls="help">הוראות</button></div>`;
}

/* ----- render: conditions ----- */
const opSel=(c)=>`<select id="c${c.id}-op" data-inp="op" data-id="${c.id}" aria-label="יחס">${[['eq','בדיוק'],['le','לכל היותר'],['ge','לפחות']].map(([v,l])=>`<option value="${v}" ${c.op===v?'selected':''}>${l}</option>`).join('')}</select>`;
const rng=(c,f,min,max,val)=>`<input type="range" id="c${c.id}-${f}" data-inp="${f}" data-id="${c.id}" min="${min}" max="${Math.max(min,max)}" step="1" value="${val}" aria-label="ערך"><b class="num val" id="c${c.id}-${f}-o">${val}</b>`;
function condBody(c){
  const K=KIND[c.kind],n=nHi();let h='';
  if(K.type==='cut'){const sel=(f,opts)=>`<select id="c${c.id}-${f}" data-inp="${f}" data-id="${c.id}" aria-label="${f==='q'?'כמת':'מה מסירים'}">${opts.map(([v,l])=>`<option value="${v}" ${c[f]===v?'selected':''}>${l}</option>`).join('')}</select>`;
    h+=`<div class="row">${sel('q',[['ex','קיימת הסרה של'],['all','לכל הסרה של']])}${rng(c,'k',1,numMax(c),c.k)}${sel('what',[['e','צלעות'],['v','צמתים']])}</div><div class="hint">התנאים שמעל נבדקים על הגרף עצמו. התנאים שמתחת נבדקים על מה שנשאר אחרי ההסרה.</div>`}
  if(K.type==='bool')h+=`<div class="row">${seg('bool',[['1','מתקיים'],['0','לא מתקיים']],String(c.value)).replace(/data-act="bool"/g,`data-act="bool" data-id="${c.id}"`)}</div>`;
  if(K.type==='num'){
    if(K.extra)h+=`<div class="row"><label for="c${c.id}-extra">${K.extra.label}</label>${rng(c,'extra',0,K.extra.max(n),c.extra)}</div>`;
    h+=`<div class="row">${opSel(c)}${rng(c,'value',numMin(c),numMax(c),c.value)}</div>`;
  }
  if(K.type==='vdeg'){
    h+=`<div class="row"><label for="c${c.id}-v">צומת</label><select id="c${c.id}-v" data-inp="v" data-id="${c.id}">${Array.from({length:n},(_,i)=>`<option value="${i+1}" ${c.v===i+1?'selected':''}>${i+1}</option>`).join('')}</select><label for="c${c.id}-d">דרגה</label>${rng(c,'d',0,n-1,c.d)}</div>`;
    if(!S.labeled)h+=`<div class="hint">במצב לא מתויג: קיים צומת בדרגה הזו</div>`;
  }
  if(K.type==='ind'){
    h+=`<div class="row"><label for="c${c.id}-prop">תכונה</label><select id="c${c.id}-prop" data-inp="prop" data-id="${c.id}">${Object.entries(IND_LABEL).map(([v,l])=>`<option value="${v}" ${c.prop===v?'selected':''}>${l}</option>`).join('')}</select>
    <label for="c${c.id}-k">גודל</label><select id="c${c.id}-k" data-inp="k" data-id="${c.id}"><option value="0" ${c.k===0?'selected':''}>כל גודל</option>${Array.from({length:Math.max(0,n-1)},(_,i)=>`<option value="${i+1}" ${c.k===i+1?'selected':''}>${i+1}</option>`).join('')}</select></div>
    <div class="row"><span class="lab">מספר התת-קבוצות</span></div><div class="row">${opSel(c)}${rng(c,'value',0,numMax(c),c.value)}</div>`;
  }
  if(!K.noTarget&&K.type!=='vdeg'&&K.type!=='ind')h+=`<div class="row"><label for="c${c.id}-t">חל על</label><select id="c${c.id}-t" data-inp="target" data-id="${c.id}"><option value="G" ${c.target==='G'?'selected':''}>הגרף</option><option value="C" ${c.target==='C'?'selected':''}>המשלים</option></select></div>`;
  if(K.hint)h+=`<div class="hint">${K.hint}</div>`;
  return h;
}
function renderConds(){
  const cats={};for(const [k,K] of Object.entries(KIND))if(k!=='cut'||!cutOf(S.conds))(cats[K.cat]=cats[K.cat]||[]).push([k,K.label]);
  $('#conds').innerHTML=`<div class="colhead"><h2>תנאים</h2><span class="lab" id="condsub"></span></div>
  <div class="basec"><span id="baselabel"></span><b class="num" id="basecount"></b></div>
  ${S.conds.map((c,i)=>`<div class="cond${c.on?'':' off'}${c.kind==='cut'?' cut':isBelow(c,S.conds)?' below':''}" id="cond${c.id}">
    <div class="chead"><button class="tog" data-act="toggle" data-id="${c.id}" role="switch" aria-checked="${c.on}" aria-label="הפעל או כבה את התנאי"><span></span></button>
    <div class="cname">${KIND[c.kind].label}</div><b class="num ccount" id="cnt${c.id}"></b></div>
    ${condBody(c)}
    <div class="hint rngl" id="rng${c.id}"></div>
    <div class="cfoot"><span class="note" id="note${c.id}"></span><span class="tools"><button class="ib" data-act="up" data-id="${c.id}" aria-label="הזז למעלה" ${i===0?'disabled':''}>↑</button><button class="ib" data-act="down" data-id="${c.id}" aria-label="הזז למטה" ${i===S.conds.length-1?'disabled':''}>↓</button><button class="ib" data-act="del" data-id="${c.id}" aria-label="הסר תנאי">×</button></span></div>
  </div>`).join('')}
  <button class="add" data-act="menu" aria-expanded="${S.menuOpen}">+ הוסף תנאי</button>
  <div class="menu" ${S.menuOpen?'':'hidden'}>${Object.entries(cats).map(([cat,list])=>`<div class="mcat"><div class="lab">${cat}</div><div class="chips">${list.map(([k,l])=>`<button class="chip" data-act="add" data-v="${k}">${l}</button>`).join('')}</div></div>`).join('')}</div>`;
}
const hidden=()=>S.mode==='guess'&&!S.guess.revealed;
function updateCounts(){
  const lab=S.labeled,pick=x=>fmt(lab?x.l:x.u),man=single();
  $('#condsub').textContent=S.mode==='prufer'?'האם העץ הנבחר מקיים':man?'האם הגרף שלך מקיים':'כמה נשארו אחרי כל תנאי';
  $('#baselabel').textContent=(S.type==='tree'?'כל העצים':S.type==='bip'?'כל הגרפים הדו-צדדיים':'כל הגרפים')+(lab?' המתויגים':'');
  $('#basecount').textContent=man?'':pick(R.r.base);
  const g=man?selGraph().a:null;let prev=man?0:lab?R.r.base.l:R.r.base.u;
  for(const c of S.conds){
    const cn=$('#cnt'+c.id),nt=$('#note'+c.id),inf=R.info[c.id];if(!cn)continue;
    const rg=$('#rng'+c.id);rg.className='hint rngl';rg.innerHTML='';cn.className='num ccount';nt.className='note';nt.textContent='';
    if(man){const ok=evalSingle(g,S.n,c);cn.textContent=ok===null?'—':ok?'✓':'✗';if(ok!==null)cn.classList.add(ok?'ok':'no');if(ok===null)nt.textContent=c.kind==='cut'?'תנאי ההסרה פועל רק עד שמונה צמתים':'נבדק על מה שנשאר אחרי ההסרה';continue}
    if(hidden()){cn.textContent=c.on?'?':'';continue}
    if(c.on){const now=lab?inf.step.l:inf.step.u;cn.textContent=pick(inf.step);
      if(prev===0){nt.textContent='הרשימה כבר התרוקנה בתנאי קודם';cn.classList.add('dim')}
      else if(now===0){nt.textContent='התנאי הזה מרוקן את הרשימה: אין גרף שמקיים אותו יחד עם הקודמים';nt.classList.add('warn');cn.classList.add('no')}
      else if(c.kind==='vdeg'&&isBelow(c,S.conds.filter(x=>x.on)))nt.textContent='לא נבדק מתחת לתנאי ההסרה: אחרי הסרה אין משמעות למספור הצמתים';
      else if(c.kind==='cut'&&R.r.parts.some(p=>p.U.kind!=='G'))nt.textContent='תנאי ההסרה פועל רק עד שמונה צמתים, מעל זה הוא לא מסנן';
      else if(inf.redundant&&R.r.fin.u>0)nt.textContent='לא משפיע כרגע: נובע משאר התנאים';
      prev=now;
      const empty=R.r.fin.u===0,ok=inf.ok;
      if(empty&&inf.woN>0){rg.classList.add('fix');rg.innerHTML=!ok?'שינוי התנאי הזה לבדו מחזיר תוצאות':ok.length?'שינוי כאן לבדו מספיק. יש תוצאות עבור '+runsTxt(ok):'שינוי הערך לא מספיק, אבל כיבוי התנאי הזה מחזיר תוצאות'}
      else if(empty&&inf.partners){rg.classList.add('fix');const ps=[...new Set(inf.partners)];rg.textContent=(ps.length>1?'צריך לשנות יחד עם אחד מאלה: ':'צריך לשנות יחד עם: ')+ps.join(', ')}
      else if(!empty&&ok&&ok.length)rg.innerHTML='יש תוצאות עבור '+runsTxt(ok);
    }
    else{cn.textContent='';nt.innerHTML=`כבוי. אם יודלק, יישארו <b class="num">${pick(inf.ifOn)}</b>`}
  }
}

/* ----- render: main ----- */
function renderMain(){
  const m=$('#main');
  if(S.mode==='manual'){
    const a=manualGraph(),n=S.n;const pos=layout(new Array(n).fill(0),n,'circle');
    m.innerHTML=`<div class="hero"><div class="big"><span class="t">גרף ידני</span></div><div class="pill">לחץ על שני צמתים כדי להוסיף או להסיר צלע ביניהם</div></div>
    <div class="bar"><button class="btn" data-act="mclear">נקה צלעות</button><button class="btn" data-act="mcompl">הפוך למשלים</button></div>
    <div class="editor">${svgGraph(a,n,{pos,labels:true,hit:'vertex',pick:S.manualPick,r:10,cls:'big',aria:'עורך גרף'})}</div>`;
    return;
  }
  if(S.mode==='prufer'){
    const n=S.n,opts=t=>Array.from({length:n},(_,i)=>`<option value="${i+1}" ${t===i+1?'selected':''}>${i+1}</option>`).join('')+['x','y'].map(v=>`<option value="${v}" ${t===v?'selected':''}>${v}</option>`).join('');
    m.innerHTML=`<div class="hero"><div class="big"><b class="num n1">${fmt(ITEMS.length)}</b><span class="t">${ITEMS.length===1?'עץ מתויג מתאים לסדרה':'עצים מתויגים מתאימים לסדרה'}</span></div><div class="pill">בכל מקום בסדרה בוחרים מספר צומת או משתנה</div></div>
    <div class="game"><span class="lab">סדרת פרופר</span><div class="prseq" dir="ltr">${S.prufer.length?S.prufer.map((t,i)=>`<select id="pr${i}" data-inp="pr" data-i="${i}" aria-label="מקום ${i+1} בסדרה">${opts(t)}</select>`).join(''):'<span class="hint">סדרה ריקה</span>'}</div>
    <button class="btn sm" data-act="prand">סדרה אקראית</button></div>
    <div class="bar"><button class="btn" data-act="lay" data-v="circle" aria-pressed="${S.layout==='circle'}">פריסה במעגל</button><button class="btn" data-act="lay" data-v="planar" aria-pressed="${S.layout==='planar'}">ציור מישורי</button><button class="btn" data-act="opt" data-v="showComp" aria-pressed="${S.showComp}">משלים לצד כל עץ</button><button class="btn hi" data-act="opt" data-v="showMatch" aria-pressed="${S.showMatch}">זיווג מקסימלי מסומן</button></div>
    <div class="gal"></div>`;
    fillGal();return;
  }
  const f=R.r.fin,hid=hidden();
  let top='';
  if(S.mode==='guess'){
    top=`<div class="game"><label for="guess">כמה גרפים ${S.labeled?'מתויגים':'לא מתויגים'} מקיימים את התנאים?</label>
    <input id="guess" type="number" min="0" inputmode="numeric" data-inp="guess" value="${esc(S.guess.val)}">
    <button class="btn pri" data-act="reveal">חשוף</button>
    ${S.guess.revealed?`<span class="res ${Number(S.guess.val)===(S.labeled?f.l:f.u)?'ok':'no'}">${S.guess.val===''?'':Number(S.guess.val)===(S.labeled?f.l:f.u)?'בול':'לא מדויק'}</span>`:''}</div>`;
  }
  if(S.mode==='target'){
    const hit=S.target!==null&&f.u===S.target;
    top=`<div class="game ${hit?'won':''}"><span>יעד: להשאיר בדיוק</span><b class="num tnum">${S.target===null?'—':fmt(S.target)}</b><span>גרפים לא מתויגים</span>
    <button class="btn" data-act="newtarget">יעד חדש</button>${hit?'<span class="res ok">הגעת ליעד</span>':''}</div>`;
  }
  const gk=R.galleryKind;
  const pill=hid?'':gk==='labeled'?'כל הגרפים המתויגים מוצגים':gk==='all'?(ITEMS.length?'מוצגים כל הגרפים':'אין גרף שמקיים את כל התנאים'):`יותר מ־<b class="num">${S.show}</b> גרפים, אין ציור מלא`;
  m.innerHTML=`${top}<div class="hero">
    <div class="big"><b class="num n1">${hid?'?':fmt(f.u)}</b><span class="t">לא מתויגים</span></div>
    <div class="big"><b class="num n2">${hid?'?':fmt(f.l)}</b><span class="t">מתויגים</span></div>
    <div class="pill" ${pill?'':'hidden'}>${pill}</div></div>
  <div class="bar">
    <button class="btn" data-act="opt" data-v="showComp" aria-pressed="${S.showComp}">משלים לצד כל גרף</button>
    <button class="btn hi" data-act="opt" data-v="showMatch" aria-pressed="${S.showMatch}">זיווג מקסימלי מסומן</button>
    <button class="btn" data-act="opt" data-v="showLabels" aria-pressed="${S.showLabels}">תוויות צמתים</button>
    <button class="btn" data-act="lay" data-v="circle" aria-pressed="${S.layout==='circle'}">פריסה במעגל</button>
    <button class="btn" data-act="lay" data-v="planar" aria-pressed="${S.layout==='planar'}">ציור מישורי</button>
    ${gk==='many'&&!hid?`<button class="btn" data-act="opt" data-v="sample" aria-pressed="${S.sample}">הצג <b class="num">${S.show}</b> לדוגמה</button>`:''}
    ${showSel()}
  </div>
  ${S.show>LIVE?'<p class="hint slow">בבחירה של יותר מחמישים גרפים להצגה, הציורים נטענים בהשהיה קצרה ולא מתעדכנים תוך כדי גרירת מחוון.</p>':''}
  <div class="gal" ${hid?'hidden':''}></div>`;
  fillGal();
}
const showSel=()=>`<span class="grp showsel"><label class="lab" for="showsel">גרפים להצגה</label><select id="showsel" data-inp="show">${SHOWS.map(v=>`<option value="${v}" ${S.show===v?'selected':''}>${v}</option>`).join('')}</select></span>`;
/* small galleries are drawn at once; large ones wait for input to settle, then load in chunks with a progress line */
let GALTOK=0;
function fillGal(){
  const el=$('.gal'),tok=++GALTOK,N=ITEMS.length;if(!el||el.hidden)return;
  if(N<=LIVE){el.innerHTML=ITEMS.map((it,i)=>galItem(it,i)).join('');return}
  el.innerHTML=`<div class="galload" role="status"><span class="spin"></span><span>טוען <b class="num" id="galn">0</b> מתוך <b class="num">${N}</b> גרפים</span></div>`;
  let i=0;const step=()=>{if(tok!==GALTOK||!el.isConnected)return;const t=performance.now();let h='';
    while(i<N&&performance.now()-t<30){h+=galItem(ITEMS[i],i);i++}
    el.insertAdjacentHTML('beforeend',h);const g=$('#galn');if(g)g.textContent=i;
    if(i<N)setTimeout(step,0);else{const l=el.querySelector('.galload');if(l)l.remove()}};
  setTimeout(step,300);
}
function galItem(it,i){
  const n=it.n,pr=R.galleryKind==='prufer',lab=R.galleryKind==='labeled',mode=lab||S.layout==='circle'?'circle':'auto';
  const pos=lab?layout(new Array(n).fill(0),n,'circle'):(S.layout==='planar'&&planarPos(it.a,n))||layout(it.a,n,mode);
  const match=S.showMatch?new Set(maxMatchEdges(it.a,n).map(([x,y])=>ekey(x,y))):null;
  const g=svgGraph(it.a,n,{pos,match,labels:lab||pr||S.showLabels,aria:'גרף '+(i+1)});
  const c=S.showComp?svgGraph(compl(it.a,n),n,{pos,labels:lab||pr||S.showLabels,cls:'comp',aria:'המשלים של גרף '+(i+1)}):'';
  return `<button class="gi${S.showComp?' two':''}" data-act="sel" data-v="${i}" aria-pressed="${S.sel===i}"><span class="pair">${g}${c}</span>
  ${pr?`<span class="meta pr"><span class="num">(${it.seq.join(', ')})</span><b class="num">${it.cap}</b></span>`:lab?'':`<span class="meta"><span>עותקים מתויגים</span><b class="num">${fmt(it.w)}</b></span>`}</button>`;
}

/* ----- render: graph card ----- */
function augmenting(a,n,M){
  const mate=new Int8Array(n).fill(-1);for(const k of M){const [x,y]=k.split('-').map(Number);mate[x]=y;mate[y]=x}
  let found=null;
  const dfs=(v,vis,path)=>{ // v reached by matched edge (or start, free); leave by unmatched edge
    let nb=a[v]&~vis;while(nb&&!found){const u=low(nb);nb&=nb-1;if(mate[v]===u)continue;
      if(mate[u]<0){found=[...path,u];return}
      const w=mate[u];if(vis>>w&1)continue;dfs(w,vis|(1<<u)|(1<<w),[...path,u,w])}
  };
  for(let s=0;s<n&&!found;s++)if(mate[s]<0)dfs(s,1<<s,[s]);
  return found;
}
function census(a,n){const reps=[];const full=(1<<n)-1;
  for(let Sx=1;Sx<full;Sx++){const vs=[];for(let i=0;i<n;i++)if(Sx>>i&1)vs.push(i);const k=vs.length;const b=vs.map(v=>{let m=0;vs.forEach((u,j)=>{if(a[v]>>u&1)m|=1<<j});return m});
    const sig=k+':'+b.map(pc).sort().join('');let ok=false;for(const r of reps)if(r.sig===sig&&isoCount(r.b,b,k,true)){ok=true;break}if(!ok)reps.push({sig,b})}
  return reps.length}
function cardHead(){return `<div class="cardhead"><h2>כרטיס הגרף</h2><button class="btn sm" data-act="wide" aria-pressed="${!!S.wide}">${S.wide?'החזר לצד':'הרחב למרכז'}</button></div>`}
const yn=b=>b?'כן':'לא';
function propRows(a,n,aut){
  const co=compl(a,n),d=degs(a).sort((x,y)=>y-x),nc=nComps(a,n),pl=isPlanar(a,n),gi=girth(a,n);
  const rows=[['צמתים',n],['צלעות',fmt(nEdges(a))],['צלעות במשלים',fmt(nEdges(co))],['סדרת דרגות',`<span dir="ltr">${d.join(', ')}</span>`],['רכיבי קשירות',nc],['קוטר',fmt(diam(a,n))],['מעגל קצר ביותר',gi===Infinity?'אין':gi],['משולשים',nTri(a,n)],['דו-צדדי',yn(isBip(a,n))],
    ['זיווג מקסימלי',maxMatch(a,n)],['זיווגים מושלמים',fmt(pmCount(a,n))],['קבוצה בלתי תלויה מקסימלית',alpha(a,n)],['קליקה מקסימלית',alpha(co,n)],['מספר צביעה',chi(a,n)],['מעגל אוילר',yn(isEuler(a,n))],['מעגל המילטון',yn(isHam(a,n))],
    ['צמתים מפרידים',nCutV(a,n)],['מעגלים',n<=8?fmt(nCycles(a,n)):nEdges(a)===n-nc?0:'—'],['מישורי',yn(pl)],['פאות בשיכון מישורי',pl?nEdges(a)-n+nc+1:'—'],['המשלים קשיר',yn(nComps(co,n)===1)],['איזומורפי למשלים',yn(PROP.selfc(a,n))]];
  if(aut)rows.push(['אוטומורפיזמים',fmt(aut)],['עותקים מתויגים',fmt(fact(n)/aut)]);
  if(n<=8)rows.push(['תת-גרפים מושרים שונים',fmt(census(a,n))]);
  return rows}
function renderCard(){
  const el=$('#card'),sg=selGraph();
  if(!sg||hidden()){el.innerHTML=`${cardHead()}<p class="hint">${hidden()?'הכרטיס ייפתח אחרי החשיפה.':'בחר גרף מהגלריה כדי לראות את התכונות שלו.'}</p>`;return}
  const a=sg.a,n=sg.n,man=S.mode==='manual',lab=man||R.galleryKind==='labeled';
  let pos=lab||S.layout==='circle'?layout(new Array(n).fill(0),n,'circle'):layout(a,n,'auto');
  const E=embInfo(a,n),kur=!E&&S.kur?kuratowski(a,n):null,nc=nComps(a,n),stepper=(act,i,L)=>`<span class="stp"><button class="ib" data-act="${act}" data-v="-1" aria-label="הקודם" ${L>1?'':'disabled'}>›</button><b class="num">${i+1} / ${L}</b><button class="ib" data-act="${act}" data-v="1" aria-label="הבא" ${L>1?'':'disabled'}>‹</button></span>`;
  let pl=`<button class="btn sm" data-act="lay" data-v="planar" aria-pressed="${S.layout==='planar'}">ציור מישורי</button>`;
  if(!E)pl=`<div class="chips"><span class="tag no">הגרף לא מישורי</span></div><button class="btn sm" data-act="kur" aria-pressed="${!!S.kur}">הראה תת-גרף שמונע שיכון</button>${kur?`<p class="hint">הצלעות המסומנות הן חלוקה של <b class="num">${kur.type==='K5'?'K₅':'K₃,₃'}</b>, ולפי משפט קורטובסקי גרף שמכיל חלוקה כזו אינו מישורי.</p>`:''}`;
  else if(S.layout==='planar'){
    const L=E.list.length,ei=Math.min(S.emb||0,L-1),rot=E.list[ei],oc=outerChoices(rot,n,E.auts),oi=nc===1?(S.outer||0)%oc.reps.length:0,of=oc.reps[oi];
    pos=planarLayout(a,n,rot,nc===1?of:undefined);
    let lens;
    if(nc===1)lens=oc.F.map((w,i)=>[w.length,i===of]);
    else{lens=[];let out=0,rem=(1<<n)-1;while(rem){const c=flood(a,low(rem),rem);rem&=~c;const fs=oc.F.filter(w=>c>>w[0]&1).map(w=>w.length).sort((x,y)=>y-x);if(fs.length){out+=fs[0];for(const x of fs.slice(1))lens.push([x,false])}}lens.push([out,true])}
    lens.sort((x,y)=>y[1]-x[1]||y[0]-x[0]);
    pl+=`<div class="kv"><span>שיכון</span>${E.capped?'<b>לא נספרו</b>':stepper('emb',ei,L)}</div>
    ${nc===1?`<div class="kv"><span>פאה חיצונית</span>${stepper('outer',oi,oc.reps.length)}</div>`:''}
    <div class="kv"><span>אורכי הפאות, החיצונית ראשונה</span><b class="num">${lens.map(x=>x[0]).join(', ')}</b></div>
    <p class="hint">${E.capped?'יש יותר מדי שיכונים כדי לעבור על כולם, מוצג אחד.':L>1?'שיכונים שנבדלים רק בסימטריה של הגרף או בשיקוף נספרים פעם אחת.':'לגרף הזה שיכון אחד בלבד, עד כדי סימטריה ושיקוף.'+(nc===1&&oc.reps.length>1?' בחירת הפאה החיצונית משנה רק את הציור במישור.':'')}</p>`;
  }
  const cut=S.mode==='prufer'?null:S.conds.find(c=>c.kind==='cut'&&(man||c.on));let cw='',mark=kur;
  if(cut&&n<=8){const w=cutWitness(a,n,cut,belowOf(cut)),ex=cut.q!=='all';
    if(w){if(!mark){mark={b:new Array(n).fill(0),branch:0};for(const x of w){if(cut.what==='e'){mark.b[x[0]]|=1<<x[1];mark.b[x[1]]|=1<<x[0]}else mark.branch|=1<<x}}
      cw=`<div class="toolbox"><p class="hint">${ex?'מסומנת באדום הסרה לדוגמה שאחריה מתקיימים התנאים שמתחת לתנאי ההסרה':'מסומנת באדום הסרה שאחריה התנאים שמתחת לתנאי ההסרה לא מתקיימים'}: <b class="num">${w.map(x=>cut.what==='e'?(x[0]+1)+'–'+(x[1]+1):x+1).join(', ')}</b></p></div>`}
    else if(man)cw=`<div class="toolbox"><p class="hint">${ex?'אין הסרה שאחריה מתקיימים התנאים שמתחת לתנאי ההסרה.':'כל הסרה משאירה גרף שמקיים את התנאים שמתחת לתנאי ההסרה.'}</p></div>`}
  const co=compl(a,n),M=new Set(S.matching),path=S.augPath?new Set(S.augPath.slice(1).map((v,i)=>ekey(v,S.augPath[i]))):null;
  const subset=S.tool==='subset'?S.subset:0;
  const g=svgGraph(a,n,{pos,labels:true,match:S.tool==='match'?M:null,path,subset,hit:S.tool==='match'?'edge':'vertex',r:9,kur:mark,aria:'הגרף הנבחר'});
  const c=svgGraph(co,n,{pos,labels:true,subset,cls:'comp',r:9,aria:'המשלים'});
  const aut=sg.idx>=0?sg.U.aut[sg.idx]:(n<=8?isoCount(a,a,n,false):null),mm=maxMatch(a,n);
  const rows=propRows(a,n,aut);
  if(subset){const vs=[];for(let i=0;i<n;i++)if(subset>>i&1)vs.push(i);const k=vs.length,b=vs.map(v=>{let m=0;vs.forEach((u,j)=>{if(a[v]>>u&1)m|=1<<j});return m});
    const sub=new Map(propRows(b,k,k<=8?isoCount(b,b,k,false):null));for(const r of rows)r.push(sub.has(r[0])?sub.get(r[0]):'—')}
  let tool='';
  if(S.tool==='subset'){
    const k=pc(S.subset);
    if(!k)tool=`<p class="hint">לחץ על צמתים בציור כדי לבחור תת-קבוצה ולראות את התת-גרף המושרה.</p>`;
    else{let e=0;for(let i=0;i<n;i++)if(S.subset>>i&1)e+=pc(a[i]&S.subset);e/=2;const props=Object.keys(IND).filter(p=>IND[p](a,S.subset,k)).map(p=>IND_LABEL[p]);
      tool=`<div class="kv"><span>צמתים שנבחרו</span><b class="num">${k}</b></div><div class="kv"><span>צלעות בתת-גרף המושרה</span><b class="num">${e}</b></div><div class="kv"><span>צלעות במושרה של המשלים</span><b class="num">${k*(k-1)/2-e}</b></div>
      <div class="chips">${props.map(p=>`<span class="tag">${p}</span>`).join('')||'<span class="hint">לא קליקה, לא בלתי תלויה, לא קשירה</span>'}</div><button class="btn sm" data-act="clrsub">נקה בחירה</button>`}
  }else{
    const isMax=M.size===mm,ap=isMax?null:augmenting(a,n,M);
    tool=`<p class="hint">לחץ על צלעות בציור כדי לבנות זיווג.</p><div class="kv"><span>גודל הזיווג שסימנת</span><b class="num">${M.size}</b></div><div class="kv"><span>גודל זיווג מקסימלי</span><b class="num">${mm}</b></div>
    <div class="chips"><span class="tag ${isMax?'ok':''}">${isMax?'הזיווג מקסימלי, אין מסלול שיפור':'קיים מסלול שיפור'}</span></div>
    <div class="bar"><button class="btn sm" data-act="showaug" ${ap?'':'disabled'}>הראה מסלול שיפור</button><button class="btn sm" data-act="applyaug" ${S.augPath?'':'disabled'}>בצע שיפור</button><button class="btn sm" data-act="clrmatch">נקה</button></div>`;
  }
  el.innerHTML=`${cardHead()}
  <div class="duo"><figure>${g}<figcaption>הגרף</figcaption></figure><figure>${c}<figcaption class="cc">המשלים</figcaption></figure></div>
  ${cw}<div class="toolbox">${pl}</div>
  <div class="grp"><span class="lab">כלי</span>${seg('tool',[['subset','תת-קבוצת צמתים'],['match','זיווג ומסלול שיפור']],S.tool)}</div>
  <div class="toolbox">${tool}</div>
  ${subset?'<p class="hint subhint">בכל שורה: הערך של הגרף, ולצידו בכחול הערך של התת-גרף המושרה על הצמתים שנבחרו.</p>':''}
  <div class="props">${rows.map(([k,v,w])=>`<div class="kv"><span>${k}</span><b class="num">${v}</b>${w===undefined?'':`<b class="num sub">${w}</b>`}</div>`).join('')}</div>`;
}

/* ----- game: target ----- */
function newTarget(){
  const pool=Object.keys(KIND).filter(k=>['bool','num'].includes(KIND[k].type)&&k!=='ham');
  const base=runAll([]).base.u;let t=1;
  for(let tries=0;tries<60;tries++){
    const cs=[];const m=2+(Math.random()*2|0);
    for(let i=0;i<m;i++){const k=pool[Math.random()*pool.length|0],c=mkCond(k);if(KIND[k].type==='num'){const lo=numMin(c),hi=numMax(c);c.value=lo+(Math.random()*(hi-lo+1)|0);c.op=['eq','le','ge'][Math.random()*3|0]}cs.push(c)}
    const u=runAll(cs).fin.u;if(u>=1&&u<base&&u<=40){t=u;break}
  }
  S.target=t;
}

/* ----- wiring ----- */
function resetSel(){S.subset=0;S.matching=[];S.augPath=null;S.emb=0;S.outer=0;S.kur=false}
function refresh(full){
  if(S.n>maxN())S.n=maxN();S.n2=Math.max(S.n,Math.min(maxN(),S.n2||S.n));if(S.mode==='prufer'){if(S.n<2)S.n=2;syncPrufer()}
  if(sheetMode()){renderTop();SHEET.render();return}
  if(full){clampConds();renderTop();renderConds()}
  compute();updateCounts();renderMain();renderCard();
}
function changed(){S.guess.revealed=false;S.sel=null;resetSel()}
document.addEventListener('click',ev=>{
  const t=ev.target.closest('[data-act]');if(!t)return;const act=t.dataset.act,v=t.dataset.v,id=Number(t.dataset.id),c=S.conds.find(x=>x.id===id);
  switch(act){
    case'type':S.type=v;changed();S.target=null;refresh(true);if(S.mode==='target'){newTarget();renderMain()}break;
    case'lab':S.labeled=v==='1';changed();refresh(true);break;
    case'rng':S.rng=!S.rng;changed();refresh(true);if(S.mode==='target'){newTarget();renderMain()}break;
    case'n':if(t.dataset.w==='hi')S.n2=Math.max(S.n,Math.min(maxN(),S.n2+Number(v)));else{S.n=Math.max(1,Math.min(ranged()?S.n2:maxN(),S.n+Number(v)))}changed();S.manual=null;S.manualPick=-1;refresh(true);if(S.mode==='target'){newTarget();renderMain()}break;
    case'mode':S.mode=v;if(v==='prufer'){S.type='tree';S.labeled=true}changed();S.manualPick=-1;if(v==='target')newTarget();refresh(true);break;
    case'toggle':c.on=!c.on;changed();refresh(true);break;
    case'bool':c.value=Number(v);changed();refresh(true);break;
    case'up':case'down':{const i=S.conds.indexOf(c),j=act==='up'?i-1:i+1;if(j>=0&&j<S.conds.length){S.conds[i]=S.conds[j];S.conds[j]=c}changed();refresh(true);break}
    case'del':S.conds=S.conds.filter(x=>x!==c);changed();refresh(true);break;
    case'menu':S.menuOpen=!S.menuOpen;renderConds();updateCounts();break;
    case'add':S.conds.push(mkCond(v));S.menuOpen=false;changed();refresh(true);break;
    case'opt':S[v]=!S[v];if(v==='sample'){compute()}renderMain();renderCard();break;
    case'lay':S.layout=S.layout===v?'auto':v;renderMain();renderCard();break;
    case'emb':{const sg=selGraph(),e=embInfo(sg.a,sg.n),L=e.list.length;S.emb=((S.emb||0)+Number(v)+L)%L;S.outer=0;renderCard();break}
    case'outer':S.outer=Math.max(0,(S.outer||0)+Number(v));renderCard();break;
    case'kur':S.kur=!S.kur;renderCard();break;
    case'sel':S.sel=Number(v);resetSel();document.querySelectorAll('.gi').forEach(b=>b.setAttribute('aria-pressed',String(Number(b.dataset.v)===S.sel)));renderCard();break;
    case'reveal':S.guess.revealed=true;updateCounts();renderMain();renderCard();break;
    case'prand':S.prufer=S.prufer.map(()=>1+(Math.random()*S.n|0));changed();refresh(false);break;
    case'wide':S.wide=!S.wide;$('.cols').classList.toggle('wide',S.wide);renderCard();break;
    case'conds':S.condsOpen=!S.condsOpen;$('.cols').classList.toggle('noconds',!S.condsOpen);t.setAttribute('aria-pressed',String(S.condsOpen));break;
    case'help':{const h=$('#help');h.hidden=!h.hidden;t.setAttribute('aria-expanded',String(!h.hidden));break}
    case'newtarget':newTarget();renderMain();break;
    case'tool':S.tool=v;S.augPath=null;renderCard();break;
    case'clrsub':S.subset=0;renderCard();break;
    case'clrmatch':S.matching=[];S.augPath=null;renderCard();break;
    case'showaug':{const sg=selGraph();S.augPath=augmenting(sg.a,sg.n,new Set(S.matching));renderCard();break}
    case'applyaug':{const M=new Set(S.matching),p=S.augPath;for(let i=1;i<p.length;i++){const k=ekey(p[i-1],p[i]);if(M.has(k))M.delete(k);else M.add(k)}S.matching=[...M];S.augPath=null;renderCard();break}
    case'edge':{const k=t.dataset.e,[x,y]=k.split('-').map(Number);let M=S.matching;if(M.includes(k))M=M.filter(e=>e!==k);else{M=M.filter(e=>{const [p,q]=e.split('-').map(Number);return p!==x&&p!==y&&q!==x&&q!==y});M.push(k)}S.matching=M;S.augPath=null;renderCard();break}
    case'vertex':{const i=Number(v);
      if(t.closest('#main')){const a=manualGraph();if(S.manualPick<0)S.manualPick=i;else{if(S.manualPick!==i){a[i]^=1<<S.manualPick;a[S.manualPick]^=1<<i}S.manualPick=-1;resetSel()}updateCounts();renderMain();renderCard()}
      else{S.subset^=1<<i;renderCard()}break}
    case'mclear':S.manual=null;S.manualPick=-1;resetSel();updateCounts();renderMain();renderCard();break;
    case'mcompl':S.manual=compl(manualGraph(),S.n);resetSel();updateCounts();renderMain();renderCard();break;
  }
});
document.addEventListener('keydown',ev=>{if((ev.key==='Enter'||ev.key===' ')&&ev.target.matches&&ev.target.matches('.vh')){ev.preventDefault();ev.target.dispatchEvent(new MouseEvent('click',{bubbles:true}))}});
function onInput(ev,commit){
  const t=ev.target,f=t.dataset.inp;if(!f)return;
  if(f==='guess'){S.guess.val=t.value;return}
  if(f==='show'){S.show=Number(t.value);changed();refresh(false);return}
  if(f==='pr'){S.prufer[Number(t.dataset.i)]=/^\d+$/.test(t.value)?Number(t.value):t.value;changed();refresh(false);const e=$('#'+t.id);if(e)e.focus();return}
  const c=S.conds.find(x=>x.id===Number(t.dataset.id));if(!c)return;
  const isNum=['value','extra','d','v','k'].includes(f);c[f]=isNum?Number(t.value):t.value;
  const o=$('#'+t.id+'-o');if(o)o.textContent=t.value;
  changed();
  if(t.tagName==='SELECT'&&(f==='k'||f==='v'||f==='what')){refresh(true)}else{compute();updateCounts();renderMain();renderCard()}
}
document.addEventListener('input',onInput);
refresh(true);
