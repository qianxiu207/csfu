import { connect } from 'cloudflare:sockets';

// =============================================================================
// 🟢 用户配置区域 (子账号: 仅处理流量)
// =============================================================================
const UUID = ""; // 必须与主账号的 UUID 或 KEY 保持一致
const DEFAULT_PROXY_IP = ""; 
const NODE_DEFAULT_PATH = "/api/v1"; 

// =============================================================================
// ⚡️ 核心代理逻辑区
// =============================================================================
const MAX_PENDING=2097152,KEEPALIVE=15000,STALL_TO=8000,MAX_STALL=12,MAX_RECONN=24;
const buildUUID=(a,i)=>[...a.slice(i,i+16)].map(n=>n.toString(16).padStart(2,'0')).join('').replace(/^(.{8})(.{4})(.{4})(.{4})(.{12})$/,'$1-$2-$3-$4-$5');
const extractAddr=b=>{const o=18+b[17]+1,p=(b[o]<<8)|b[o+1],t=b[o+2];let l,h,O=o+3;switch(t){case 1:l=4;h=b.slice(O,O+l).join('.');break;case 2:l=b[O++];h=new TextDecoder().decode(b.slice(O,O+l));break;case 3:l=16;h=`[${[...Array(8)].map((_,i)=>((b[O+i*2]<<8)|b[O+i*2+1]).toString(16)).join(':')}]`;break;default:throw new Error('Addr type error');}return{host:h,port:p,payload:b.slice(O+l)}};

function getEnv(env, key, fallback) { return env[key] || fallback; }

async function getDynamicUUID(key, refresh = 86400) {
    const time = Math.floor(Date.now() / 1000 / refresh);
    const msg = new TextEncoder().encode(`${key}-${time}`);
    const hash = await crypto.subtle.digest('SHA-256', msg);
    const b = new Uint8Array(hash);
    return [...b.slice(0, 16)].map(n => n.toString(16).padStart(2, '0')).join('').replace(/^(.{8})(.{4})(.{4})(.{4})(.{12})$/, '$1-$2-$3-$4-$5');
}

async function parseIP(p){
    if(!p) return null;
    p=p.trim().toLowerCase();
    let a=p,o=443;
    if(p.includes('.tp')){
        const m=p.match(/\.tp(\d+)/);
        if(m)o=parseInt(m[1],10);
        return { address: a, port: o };
    }
    if(p.includes(']:')){
        const s=p.split(']:'); a=s[0]+']'; o=parseInt(s[1],10)||o
    } else if(p.includes(':')&&!p.startsWith('[')){
        const i=p.lastIndexOf(':'); a=p.slice(0,i); o=parseInt(p.slice(i+1),10)||o
    }
    return { address: a, port: o };
}

class Pool{constructor(){this.b=new ArrayBuffer(16384);this.p=0;this.l=[];this.m=8}alloc(s){if(s<=4096&&s<=16384-this.p){const v=new Uint8Array(this.b,this.p,s);this.p+=s;return v}const r=this.l.pop();return r&&r.byteLength>=s?new Uint8Array(r.buffer,0,s):new Uint8Array(s)}free(b){if(b.buffer===this.b)this.p=Math.max(0,this.p-b.length);else if(this.l.length<this.m&&b.byteLength>=1024)this.l.push(b)}reset(){this.p=0;this.l=[]}}

const handle = (ws, proxyConfig, uuid) => {
  const pool = new Pool();
  let s, w, r, inf, fst = true, rx = 0, stl = 0, cnt = 0, lact = Date.now(), con = false, rd = false, wt = false, tm = {}, pd = [], pb = 0, scr = 1.0, lck = Date.now(), lrx = 0, md = 'buf', asz = 0, tp = [], st = { t: 0, c: 0, ts: Date.now() };
  
  const upd = sz => {
    st.t += sz; st.c++; asz = asz * 0.9 + sz * 0.1; const n = Date.now();
    if (n - st.ts > 1000) { const rt = st.t; tp.push(rt); if (tp.length > 5) tp.shift(); st.t = 0; st.ts = n; const av = tp.reduce((a, b) => a + b, 0) / tp.length; if (st.c >= 20) { if (av > 2e7 && asz > 16384) md = 'dir'; else if (av < 1e7 || asz < 8192) md = 'buf'; else md = 'adp' } }
  };
  
  const rdL = async () => {
    if (rd) return; rd = true; let b = [], bz = 0, tm = null;
    const fl = () => { if (!bz) return; const m = new Uint8Array(bz); let p = 0; for (const x of b) { m.set(x, p); p += x.length } if (ws.readyState === 1) ws.send(m); b = []; bz = 0; if (tm) clearTimeout(tm); tm = null };
    try { while (1) { if (pb > MAX_PENDING) { await new Promise(r => setTimeout(r, 100)); continue } const { done, value: v } = await r.read(); if (v?.length) { rx += v.length; lact = Date.now(); stl = 0; upd(v.length); const n = Date.now(); if (n - lck > 5000) { const el = n - lck, by = rx - lrx, r = by / el; if (r > 500) scr = Math.min(1, scr + 0.05); else if (r < 50) scr = Math.max(0.1, scr - 0.05); lck = n; lrx = rx } if (md === 'buf') { if (v.length < 32768) { b.push(v); bz += v.length; if (bz >= 131072) fl(); else if (!tm) tm = setTimeout(fl, asz > 16384 ? 5 : 20) } else { fl(); if (ws.readyState === 1) ws.send(v) } } else { fl(); if (ws.readyState === 1) ws.send(v) } } if (done) { fl(); rd = false; rcn(); break } } } catch { fl(); rd = false; rcn() }
  };
  
  const wtL = async () => { if (wt) return; wt = true; try { while (wt) { if (!w) { await new Promise(r => setTimeout(r, 100)); continue } if (!pd.length) { await new Promise(r => setTimeout(r, 20)); continue } const b = pd.shift(); await w.write(b); pb -= b.length; pool.free(b) } } catch { wt = false } };
  
  const est = async () => { try { s = await cn(); w = s.writable.getWriter(); r = s.readable.getReader(); con = false; cnt = 0; scr = Math.min(1, scr + 0.15); lact = Date.now(); rdL(); wtL() } catch { con = false; scr = Math.max(0.1, scr - 0.2); rcn() } };
  
  const cn = async () => {
    try { const directPromise = connect({ hostname: inf.host, port: inf.port }); const direct = await Promise.race([ directPromise.opened.then(() => directPromise), new Promise((_, reject) => setTimeout(() => reject('Direct timeout'), 2500)) ]); return direct; } catch (e) {}
    if (proxyConfig && proxyConfig.address) { try { const proxy = connect({ hostname: proxyConfig.address, port: proxyConfig.port }); await proxy.opened; return proxy; } catch (e) {} }
    throw new Error('Connection failed');
  };
  
  const rcn = async () => { if (!inf || ws.readyState !== 1) { cln(); ws.close(1011); return } if (cnt >= MAX_RECONN) { cln(); ws.close(1011); return } if (con) return; cnt++; let d = Math.min(50 * Math.pow(1.5, cnt - 1), 3000) * (1.5 - scr * 0.5); d = Math.max(50, Math.floor(d)); try { csk(); if (pb > MAX_PENDING * 2) while (pb > MAX_PENDING && pd.length > 5) { const k = pd.shift(); pb -= k.length; pool.free(k) } await new Promise(r => setTimeout(r, d)); con = true; s = await cn(); w = s.writable.getWriter(); r = s.readable.getReader(); con = false; cnt = 0; scr = Math.min(1, scr + 0.15); stl = 0; lact = Date.now(); rdL(); wtL() } catch { con = false; scr = Math.max(0.1, scr - 0.2); if (cnt < MAX_RECONN && ws.readyState === 1) setTimeout(rcn, 500); else { cln(); ws.close(1011) } } };
  
  const stT = () => { tm.ka = setInterval(async () => { if (!con && w && Date.now() - lact > KEEPALIVE) try { await w.write(new Uint8Array(0)); lact = Date.now() } catch { rcn() } }, KEEPALIVE / 3); tm.hc = setInterval(() => { if (!con && st.t > 0 && Date.now() - lact > STALL_TO) { stl++; if (stl >= MAX_STALL) { if (cnt < MAX_RECONN) { stl = 0; rcn() } else { cln(); ws.close(1011) } } } }, STALL_TO / 2) };
  
  const csk = () => { rd = false; wt = false; try { w?.releaseLock(); r?.releaseLock(); s?.close() } catch { } }; 
  const cln = () => { Object.values(tm).forEach(clearInterval); csk(); while (pd.length) pool.free(pd.shift()); pb = 0; st = { t: 0, c: 0, ts: Date.now() }; md = 'buf'; asz = 0; tp = []; pool.reset() };
  
  ws.addEventListener('message', async e => { try { if (fst) { fst = false; const b = new Uint8Array(e.data); if (buildUUID(b, 1).toLowerCase() !== uuid.toLowerCase()) throw 0; ws.send(new Uint8Array([0, 0])); const { host, port, payload } = extractAddr(b); inf = { host, port }; con = true; if (payload.length) { const z = pool.alloc(payload.length); z.set(payload); pd.push(z); pb += z.length } stT(); est() } else { lact = Date.now(); if (pb > MAX_PENDING * 2) return; const z = pool.alloc(e.data.byteLength); z.set(new Uint8Array(e.data)); pd.push(z); pb += z.length } } catch { cln(); ws.close(1006) } });
  ws.addEventListener('close', cln); ws.addEventListener('error', cln)
};

// =============================================================================
// 🟢 主入口 (仅限 WebSocket)
// =============================================================================
export default {
  async fetch(r, env, ctx) {
    try {
      const url = new URL(r.url);
      
      // 非 WebSocket 请求伪装处理
      if (r.headers.get('Upgrade') !== 'websocket') {
          if (url.pathname === NODE_DEFAULT_PATH) {
              return new Response(JSON.stringify({ status: "ok", version: "1.0.0" }), { status: 200, headers: { 'Content-Type': 'application/json' } });
          }
          return new Response('Not Found', { status: 404 });
      }

      const _UUID = env.KEY ? await getDynamicUUID(env.KEY) : getEnv(env, 'UUID', UUID);
      const _PROXY_IP_RAW = env.PROXYIP || env.DEFAULT_PROXY_IP || DEFAULT_PROXY_IP;
      const _PROXY_IP = _PROXY_IP_RAW ? _PROXY_IP_RAW.split(/[,\n]/)[0].trim() : "";

      // 提取客户端传递的 ProxyIP
      let finalProxyConfig = null;
      const remoteProxyIP = url.searchParams.get('proxyip'); 

      if (remoteProxyIP) {
          try { finalProxyConfig = await parseIP(remoteProxyIP); } catch (e) {}
      } else if (url.pathname.includes('/proxyip=')) {
          try { const proxyParam = url.pathname.split('/proxyip=')[1].split('/')[0]; finalProxyConfig = await parseIP(proxyParam); } catch (e) {}
      } else if (_PROXY_IP) {
          try { finalProxyConfig = await parseIP(_PROXY_IP); } catch (e) {}
      }

      // 建立连接
      const { 0: c, 1: s } = new WebSocketPair();
      s.accept();
      handle(s, finalProxyConfig, _UUID);
      return new Response(null, { status: 101, webSocket: c });

    } catch (err) {
      return new Response(err.toString(), { status: 500 });
    }
  }
};
