// 血月鐘塔 — 連線伺服器（只用 Node.js 內建模組，不需要 npm install）
// 啟動：node server.js   預設埠 3000，可用環境變數 PORT 改
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = process.env.PORT || 3000;
const PUBLIC = path.join(__dirname, 'public');
const ROOM_IDLE_MS = 12 * 60 * 60 * 1000; // 房間 12 小時沒人動就刪掉
const MAX_ROOMS = 200;
const MAX_PLAYERS = 20;

/* ---------------- 房間資料 ---------------- */
const rooms = new Map(); // code -> room

function newCode() {
  for (let i = 0; i < 1000; i++) {
    const c = String(crypto.randomInt(1000, 10000));
    if (!rooms.has(c)) return c;
  }
  throw new Error('no code');
}
const tok = () => crypto.randomBytes(18).toString('hex');
const pidGen = () => 'p' + crypto.randomBytes(5).toString('hex');
function hashPw(pw, salt) { return crypto.scryptSync(String(pw), salt, 32).toString('hex'); }
function checkPw(room, pw) {
  const h = Buffer.from(hashPw(pw, room.salt), 'hex');
  const r = Buffer.from(room.pwHash, 'hex');
  return h.length === r.length && crypto.timingSafeEqual(h, r);
}

function makeRoom(password) {
  const code = newCode();
  const salt = crypto.randomBytes(16).toString('hex');
  const room = {
    code, salt, pwHash: hashPw(password, salt),
    stToken: tok(), stPid: 'st',
    players: new Map(),      // pid -> {name, seat, token, nom}
    tokens: new Map(),       // token -> pid
    game: { status: 'lobby', phase: 'setup', round: 0, seats: [], noms: [], vote: null, gid: null, tableSize: null,
            log: [{ t: Date.now(), text: '房間已建立，等待玩家入座。' }] },
    secrets: {},             // pid -> {gid, role, msgs, wake}
    actions: {},             // pid -> {k, picks, at}
    votes: {},               // pid -> {vid, up}
    notes: {},               // 說書人備註
    conns: new Set(),        // SSE 連線 {res, pid}
    fails: [],               // 密碼錯誤時間
    touched: Date.now(),
  };
  room.tokens.set(room.stToken, 'st');
  rooms.set(code, room);
  return room;
}

/* 座位：候場時由玩家自選 */
function tableSize(room) { return room.game.tableSize || Math.max(5, room.players.size); }
function claims(room) {
  const n = tableSize(room); const slot = Array(n).fill(null);
  for (const [pid, p] of room.players) if (Number.isInteger(p.seat) && p.seat >= 0 && p.seat < n && !slot[p.seat]) slot[p.seat] = pid;
  return slot;
}

/* 每個人看到的畫面資料 */
function viewFor(room, pid) {
  const isST = pid === 'st';
  const online = new Set([...room.conns].map(c => c.pid));
  const players = {};
  for (const [id, p] of room.players) players[id] = { name: p.name, seat: Number.isInteger(p.seat) ? p.seat : null, nom: p.nom || null, on: online.has(id) };
  const v = {
    code: room.code, me: pid, isST, stOnline: online.has('st'),
    game: room.game, players, votes: room.votes,
  };
  if (isST) { v.secrets = room.secrets; v.actions = room.actions; v.notes = room.notes; }
  else { v.secrets = room.secrets[pid] ? { [pid]: room.secrets[pid] } : {}; v.myAction = room.actions[pid] || null; }
  return v;
}

const pending = new Set();
function broadcast(room) {
  room.touched = Date.now();
  if (pending.has(room)) return;
  pending.add(room);
  setImmediate(() => {
    pending.delete(room);
    for (const c of room.conns) send(c.res, 'state', viewFor(room, c.pid));
  });
}
function send(res, ev, data) { try { res.write(`event: ${ev}\ndata: ${JSON.stringify(data)}\n\n`); } catch (e) {} }

/* ---------------- 動作 ---------------- */
const isObj = o => o && typeof o === 'object' && !Array.isArray(o);
const cleanName = s => String(s || '').replace(/[\u0000-\u001f]/g, '').trim().slice(0, 12);
const str = (s, n) => String(s == null ? '' : s).slice(0, n);

function act(room, pid, type, d) {
  const isST = pid === 'st';
  const g = room.game;
  const me = room.players.get(pid);
  switch (type) {
    /* ---- 玩家 ---- */
    case 'rename': {
      if (isST) throw '說書人不需要暱稱';
      const name = cleanName(d.name); if (!name) throw '請輸入暱稱';
      me.name = name; return;
    }
    case 'sit': {
      if (isST || g.status !== 'lobby') throw '現在不能換座位';
      const i = d.i | 0; if (i < 0 || i >= tableSize(room)) throw '沒有這個座位';
      const cur = claims(room)[i]; if (cur && cur !== pid) throw '這個位子有人了，換一個吧';
      me.seat = i; return;
    }
    case 'stand': { if (isST || g.status !== 'lobby') throw '現在不能起身'; me.seat = null; return; }
    case 'nominate': {
      if (isST || g.status !== 'playing' || g.phase !== 'day') throw '現在不能提名';
      const s = g.seats.find(x => x.id === pid); if (!s || !s.alive) throw '只有存活玩家可以提名';
      if (!g.seats.some(x => x.id === d.target)) throw '沒有這名玩家';
      me.nom = { gid: g.gid, day: g.round, target: d.target, at: Date.now() }; return;
    }
    case 'vote': {
      if (isST || !g.vote) throw '目前沒有投票';
      const s = g.seats.find(x => x.id === pid); if (!s) throw '你不在這局';
      if (!s.alive && s.ghost) throw '你的殘魂票已經用過了';
      room.votes[pid] = { vid: g.vote.id, up: !!d.up, at: Date.now() }; return;
    }
    case 'pick': {
      if (isST) throw '說書人不用選';
      const sec = room.secrets[pid]; if (!sec || !sec.wake || sec.wake.k !== d.k) throw '說書人沒有喚醒你';
      const picks = Array.isArray(d.picks) ? d.picks.filter(x => g.seats.some(s => s.id === x)).slice(0, sec.wake.picks) : [];
      room.actions[pid] = { k: d.k, picks, at: Date.now() }; return;
    }
    /* ---- 說書人 ---- */
    default: if (!isST) throw '只有說書人可以這麼做';
  }
  switch (type) {
    case 'setGame': {
      if (!isObj(d.game)) throw 'bad game';
      const ng = d.game;
      ng.seats = (Array.isArray(ng.seats) ? ng.seats : []).filter(s => isObj(s) && room.players.has(s.id)).slice(0, MAX_PLAYERS)
        .map(s => ({ id: s.id, alive: !!s.alive, ghost: !!s.ghost }));
      ng.log = (Array.isArray(ng.log) ? ng.log : []).slice(-80).map(l => ({ t: +l.t || Date.now(), text: str(l.text, 300) }));
      if (ng.tableSize != null) ng.tableSize = Math.max(5, Math.min(MAX_PLAYERS, ng.tableSize | 0));
      room.game = ng;
      if (!ng.vote) room.votes = {};
      return;
    }
    case 'setSecret': {
      if (!room.players.has(d.pid) || !isObj(d.secret)) throw '沒有這名玩家';
      const s = d.secret;
      s.msgs = (Array.isArray(s.msgs) ? s.msgs : []).slice(-60).map(m => ({ t: +m.t || Date.now(), tag: str(m.tag, 20), text: str(m.text, 800) }));
      room.secrets[d.pid] = s; return;
    }
    case 'setNotes': { if (!isObj(d.notes)) throw 'bad'; room.notes = d.notes; return; }
    case 'clearSeat': { const p = room.players.get(d.pid); if (p) p.seat = null; return; }
    case 'setSeat': {
      const p = room.players.get(d.pid); const i = d.i | 0;
      if (!p || g.status !== 'lobby' || i < 0 || i >= tableSize(room) || claims(room)[i]) throw '無法入座';
      p.seat = i; return;
    }
    case 'kick': {
      const p = room.players.get(d.pid); if (!p) return;
      room.tokens.delete(p.token); room.players.delete(d.pid);
      delete room.secrets[d.pid]; delete room.actions[d.pid]; delete room.votes[d.pid];
      g.seats = g.seats.filter(s => s.id !== d.pid);
      for (const c of [...room.conns]) if (c.pid === d.pid) { send(c.res, 'kicked', {}); c.res.end(); room.conns.delete(c); }
      return;
    }
    case 'closeRoom': {
      for (const c of room.conns) { send(c.res, 'closed', {}); c.res.end(); }
      rooms.delete(room.code); return 'closed';
    }
    default: throw '未知的動作';
  }
}

/* ---------------- HTTP ---------------- */
function json(res, code, obj) {
  res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
  res.end(JSON.stringify(obj));
}
function readBody(req) {
  return new Promise((resolve, reject) => {
    let size = 0; const chunks = [];
    req.on('data', c => { size += c.length; if (size > 300000) { reject(new Error('too big')); req.destroy(); } else chunks.push(c); });
    req.on('end', () => { try { resolve(JSON.parse(Buffer.concat(chunks).toString('utf8') || '{}')); } catch (e) { reject(e); } });
    req.on('error', reject);
  });
}
function auth(code, token) {
  const room = rooms.get(String(code || ''));
  if (!room) return {};
  const pid = room.tokens.get(String(token || ''));
  return { room, pid };
}
const MIME = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8', '.svg': 'image/svg+xml', '.png': 'image/png', '.ico': 'image/x-icon' };

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, 'http://x');
  try {
    if (req.method === 'POST' && url.pathname === '/api/create') {
      const b = await readBody(req);
      const pw = String(b.password || '');
      if (pw.length < 1 || pw.length > 32) return json(res, 400, { error: '密碼請設 1 到 32 個字' });
      if (rooms.size >= MAX_ROOMS) return json(res, 503, { error: '伺服器房間已滿，請稍後再試' });
      const room = makeRoom(pw);
      return json(res, 200, { code: room.code, token: room.stToken, pid: 'st' });
    }
    if (req.method === 'POST' && url.pathname === '/api/join') {
      const b = await readBody(req);
      const room = rooms.get(String(b.code || '').trim());
      if (!room) return json(res, 404, { error: '找不到這個房號' });
      const now = Date.now(); room.fails = room.fails.filter(t => now - t < 10 * 60 * 1000);
      if (room.fails.length >= 10) return json(res, 429, { error: '密碼錯太多次，請 10 分鐘後再試' });
      if (!checkPw(room, b.password)) { room.fails.push(now); return json(res, 403, { error: '密碼不對' }); }
      const name = cleanName(b.name); if (!name) return json(res, 400, { error: '請輸入暱稱' });
      if (room.players.size >= MAX_PLAYERS) return json(res, 403, { error: '房間已滿' });
      const pid = pidGen(); const token = tok();
      room.players.set(pid, { name, seat: null, token, nom: null });
      room.tokens.set(token, pid);
      room.game.log = room.game.log.concat({ t: now, text: `${name} 進入房間。` }).slice(-80);
      broadcast(room);
      return json(res, 200, { code: room.code, token, pid });
    }
    if (req.method === 'GET' && url.pathname === '/api/events') {
      const { room, pid } = auth(url.searchParams.get('code'), url.searchParams.get('token'));
      if (!room || !pid) return json(res, 401, { error: '房間不存在或已失效' });
      res.writeHead(200, { 'Content-Type': 'text/event-stream; charset=utf-8', 'Cache-Control': 'no-store', 'Connection': 'keep-alive', 'X-Accel-Buffering': 'no' });
      res.write('retry: 3000\n\n');
      const conn = { res, pid };
      room.conns.add(conn);
      broadcast(room);
      req.on('close', () => { room.conns.delete(conn); broadcast(room); });
      return;
    }
    if (req.method === 'POST' && url.pathname === '/api/act') {
      const b = await readBody(req);
      const { room, pid } = auth(b.code, b.token);
      if (!room || !pid) return json(res, 401, { error: '房間不存在或已失效' });
      try {
        const r = act(room, pid, String(b.type || ''), isObj(b.data) ? b.data : {});
        if (r !== 'closed') broadcast(room);
        return json(res, 200, { ok: true });
      } catch (e) {
        return json(res, 400, { error: typeof e === 'string' ? e : '操作失敗' });
      }
    }
    if (req.method === 'GET' && url.pathname === '/healthz') return json(res, 200, { ok: true, rooms: rooms.size });
    if (req.method === 'GET') {
      let p = decodeURIComponent(url.pathname); if (p === '/') p = '/index.html';
      const f = path.normalize(path.join(PUBLIC, p));
      if (!f.startsWith(PUBLIC)) { res.writeHead(403); return res.end(); }
      fs.readFile(f, (err, data) => {
        if (err) { res.writeHead(404); return res.end('Not found'); }
        res.writeHead(200, { 'Content-Type': MIME[path.extname(f)] || 'application/octet-stream', 'Cache-Control': 'no-cache' });
        res.end(data);
      });
      return;
    }
    res.writeHead(405); res.end();
  } catch (e) {
    json(res, 400, { error: '請求格式錯誤' });
  }
});

/* 保持連線、清理閒置房間 */
setInterval(() => {
  const now = Date.now();
  for (const room of rooms.values()) {
    for (const c of room.conns) { try { c.res.write(': ping\n\n'); } catch (e) {} }
    if (room.conns.size === 0 && now - room.touched > ROOM_IDLE_MS) rooms.delete(room.code);
  }
}, 25000);

server.listen(PORT, () => console.log(`血月鐘塔已啟動：http://localhost:${PORT}`));
