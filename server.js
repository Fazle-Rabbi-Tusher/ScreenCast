#!/usr/bin/env node
'use strict';
/*
 * Screen Cast (formerly TV Board) - free, self-hosted signage for any TV that has a web browser.
 *
 *   Run:      node server.js            (Node 18 or newer, nothing to install)
 *   Control:  http://<this-pc-ip>:8712/         (from your laptop or phone)
 *   TVs:      http://<this-pc-ip>:8712/tv       (pick the TV with the remote)
 *             http://<this-pc-ip>:8712/tv3      (or go straight to TV 3)
 *
 *   TV pairing: switched on from the control page ("Set up a TV"). Until then anyone on
 *               the network can open the TV pages. With it on, a TV shows a 6-digit code
 *               at /tv and only works once someone signed in has typed that code in.
 *
 *   First run:  node server.js set-password     creates the first admin account, "admin".
 *               node server.js set-password jane  makes or repairs another admin account.
 *               Everyone else is added from the Users page. Only salted hashes are stored.
 *
 *   Updating:   replace this one file (server.js) and restart. Everything you have set up
 *               (screens, playlists, uploads, accounts) lives in the tvboard-data folder
 *               beside it. Never replace or delete that folder, and if you move the server
 *               to another folder or PC, move tvboard-data along with it.
 *
 *   HTTPS:      node server.js make-cert        makes a certificate for this machine and
 *               keeps it in tvboard-data/tls. From the next start the control page is on
 *               https://<this-pc-ip>:8443/ and refuses plain HTTP, so passwords no longer
 *               cross the network unencrypted. The TVs keep using plain HTTP on port 8712.
 *               Run it again when the machine's address changes or the certificate runs
 *               out (about two years). To go back to plain HTTP, remove the tls folder.
 *
 *   Optional environment variables:
 *     PORT=8712             plain-HTTP port. With HTTPS on, it serves the TV pages only.
 *     TLS_CERT, TLS_KEY     paths to a certificate and key of your own, used instead of
 *                           the one made by make-cert.
 *     HTTPS_PORT=8443       HTTPS port
 *     ADMIN_ALLOW=...       only these addresses may reach the control page,
 *                           e.g. 10.20.5.0/24,10.20.9.14
 *     TV_ALLOW=...          only these addresses may load the TV pages
 *     BIND=...              listen on this one address of the machine only, e.g. 10.20.5.7.
 *                           Without it the server answers on every network the machine is on.
 *     IDLE_MINUTES=60       sign people out after this long without touching the control
 *                           page (viewers are left signed in). 0 switches it off.
 *     DATA_DIR=...          where playlists, uploads, the password hash and audit.log live
 *     MAX_UPLOAD_MB=1024    largest single upload
 *     MIN_FREE_MB=2048      refuse uploads that would leave less free disk space than this
 *     MAX_LIBRARY_MB=...    largest total size of the media library (no limit if not set)
 *     TV_KEEP_MB=64         how much of its playlist's pictures a TV holds on to, so that they
 *                           keep going round while this server cannot be reached. 0 = none.
 *     SOFFICE_PATH=...      where LibreOffice's soffice program is, if not in the usual place
 *
 *   Optional, for PDF / PowerPoint / Excel uploads (each page becomes a picture):
 *     PDF:                 run "npm install mupdf" in this folder
 *     PowerPoint, Excel:   the above, plus install LibreOffice on this machine
 */
const http = require('http');
const https = require('https');
const fs = require('fs');
const path = require('path');
const os = require('os');
const crypto = require('crypto');
const execFile = require('child_process').execFile;
const pathToFileURL = require('url').pathToFileURL;

const PORT = parseInt(process.env.PORT, 10) || 8712;
const HTTPS_PORT = parseInt(process.env.HTTPS_PORT, 10) || 8443;
const DATA_DIR = path.resolve(process.env.DATA_DIR || path.join(__dirname, 'tvboard-data'));
// HTTPS uses the certificate named in TLS_CERT and TLS_KEY, or else the one that
// "node server.js make-cert" keeps in the data folder.
const TLS_DIR = path.join(DATA_DIR, 'tls');
const TLS_MADE = !process.env.TLS_CERT && !process.env.TLS_KEY &&
  fs.existsSync(path.join(TLS_DIR, 'cert.pem')) && fs.existsSync(path.join(TLS_DIR, 'key.pem'));
const TLS_CERT = process.env.TLS_CERT || (TLS_MADE ? path.join(TLS_DIR, 'cert.pem') : '');
const TLS_KEY = process.env.TLS_KEY || (TLS_MADE ? path.join(TLS_DIR, 'key.pem') : '');
const TLS_ON = !!(TLS_CERT && TLS_KEY);
const CERT_DAYS = 820; // phones refuse certificates that last longer than 825 days
const MEDIA_DIR = path.join(DATA_DIR, 'media');
const STATE_FILE = path.join(DATA_DIR, 'state.json');
const AUTH_FILE = path.join(DATA_DIR, 'admin.json'); // older single-password file, migrated on first run
const USERS_FILE = path.join(DATA_DIR, 'users.json');
const SESSIONS_FILE = path.join(DATA_DIR, 'sessions.json');
const AUDIT_FILE = path.join(DATA_DIR, 'audit.log');
const MAX_UPLOAD = (parseInt(process.env.MAX_UPLOAD_MB, 10) || 1024) * 1024 * 1024;
const MIN_FREE = envNumber('MIN_FREE_MB', 2048) * 1024 * 1024;   // 0 = do not check
const MAX_LIBRARY = envNumber('MAX_LIBRARY_MB', 0) * 1024 * 1024; // 0 = no limit
const MAX_CONVERTING = 2;          // documents being turned into pictures at the same time
const TV_KEEP = envNumber('TV_KEEP_MB', 64) * 1024 * 1024;        // 0 = TVs hold no pictures
const ADMIN_ALLOW = parseAllow(process.env.ADMIN_ALLOW, 'ADMIN_ALLOW');
const TV_ALLOW = parseAllow(process.env.TV_ALLOW, 'TV_ALLOW');
const BIND = String(process.env.BIND || '').trim();
const SESSION_MS = 12 * 3600 * 1000;
const IDLE_MS = envNumber('IDLE_MINUTES', 60) * 60 * 1000;        // 0 = never
const MAX_SIGNING_IN = 8;          // passwords being checked at the same time, over all addresses
const ROOM_STEP = 8 * 1024 * 1024; // while an upload arrives, disk room is checked again after every this many bytes
const PAIR_MS = 15 * 60 * 1000;    // how long the code on an unpaired TV stays good
const ADOPT_MS = 2 * 60 * 1000;    // after pairing is switched on, connected TVs have this long to collect their key
const MAX_FAILS = 5;               // wrong passwords from one address...
const LOCK_MS = 15 * 60 * 1000;    // ...lock that address out for this long
const MIN_PASSWORD = 12;
const ROLES = { admin: 3, editor: 2, viewer: 1 };
const USERNAME_RE = /^[a-z0-9][a-z0-9._-]{1,31}$/;
// Documents are turned into one picture per page, because TV browsers cannot open them.
const DOC_EXT = { '.pdf': 1, '.pptx': 1, '.ppt': 1, '.xlsx': 1, '.xls': 1 };
const PAGE_RE = /^(.+)\.page-(\d{3})\.jpg$/;
const MAX_PAGES = 150;
const HAS_PDF = fs.existsSync(path.join(__dirname, 'node_modules', 'mupdf', 'package.json'));
const SOFFICE = findSoffice();
const DEFAULT_SCREENS = 7;
const ONLINE_WINDOW_MS = 12000; // two missed 5-second polls and the TV counts as offline
const IDENTIFY_MS = 20000;

const MIME = {
  '.jpg': 'image/jpeg', '.jpeg': 'image/jpeg', '.png': 'image/png',
  '.gif': 'image/gif', '.webp': 'image/webp',
  '.mp4': 'video/mp4', '.m4v': 'video/mp4', '.webm': 'video/webm'
};

fs.mkdirSync(MEDIA_DIR, { recursive: true });

// ---------------------------------------------------------------- state

function newScreen(id, name) {
  return { id: id, name: name, version: 1, items: [] };
}

let freshState = false; // no state.json was found: this is a blank start

function loadState() {
  let raw;
  try {
    raw = fs.readFileSync(STATE_FILE, 'utf8');
  } catch (e) {
    if (e.code !== 'ENOENT') throw e;
    freshState = true;
    const screens = [];
    for (let i = 1; i <= DEFAULT_SCREENS; i++) screens.push(newScreen(String(i), 'TV ' + i));
    return { screens: screens };
  }
  const parsed = JSON.parse(raw); // a corrupt file stops startup rather than being overwritten
  if (!parsed || !Array.isArray(parsed.screens)) throw new Error('state.json has no "screens" list');
  return parsed;
}

let state = loadState();
const seen = {};      // screen id -> last time its TV polled
const seenFrom = {};  // screen id -> { address: last time a TV polled from it }
const identify = {};  // screen id -> show the name badge until this time
const playing = {};   // screen id -> what its TV last reported: { v: playlist version, i: item on screen }

// ---- TV pairing
// With pairing on (state.pairing), a TV may only load a screen with that screen's key. A
// TV gets the key when someone signed in types the code the TV is showing, and keeps it
// in its own browser. The key never leaves the server any other way: it is not sent to
// the control page.
const pairs = new Map(); // pairing id -> { code, ip, created, go }: TVs showing a code
let adopt = null;        // { until, ips: { screen id: [addresses] } }: TVs that were connected when pairing was switched on

function newKey() { return crypto.randomBytes(16).toString('hex'); }

function keyOf(s) {
  if (!s.key) { s.key = newKey(); saveState(); }
  return s.key;
}

function sameText(a, b) { // compared in a way that does not reveal how much of it was right
  const x = Buffer.from(String(a));
  const y = Buffer.from(String(b));
  return x.length === y.length && crypto.timingSafeEqual(x, y);
}

function keyFits(s, key) { return !!s && !!s.key && !!key && sameText(s.key, key); }

function anyKeyFits(key) {
  return !!key && state.screens.some(function (s) { return keyFits(s, key); });
}

// what the control page is told about a screen: everything except its key
function publicScreen(s) {
  return { id: s.id, name: s.name, version: s.version, items: s.items };
}

function saveState() {
  const tmp = STATE_FILE + '.tmp';
  fs.writeFileSync(tmp, JSON.stringify(state, null, 2));
  fs.renameSync(tmp, STATE_FILE);
}

function findScreen(id) {
  return state.screens.find(function (s) { return s.id === id; });
}

function listMedia() {
  return fs.readdirSync(MEDIA_DIR)
    .filter(function (n) { return n[0] !== '.' && MIME[path.extname(n).toLowerCase()]; })
    .map(function (n) {
      const st = fs.statSync(path.join(MEDIA_DIR, n));
      const type = MIME[path.extname(n).toLowerCase()];
      const pg = PAGE_RE.exec(n);
      return {
        name: n, size: st.size, kind: type.split('/')[0], mtime: st.mtimeMs,
        doc: pg ? pg[1] : undefined, page: pg ? Number(pg[2]) : undefined,
        owner: (state.owners || {})[pg ? 'doc:' + pg[1] : n]
      };
    })
    .sort(function (a, b) { return b.mtime - a.mtime; });
}

function mediaExists(name) {
  return !!name && name === path.basename(name) && name[0] !== '.' &&
    !!MIME[path.extname(name).toLowerCase()] && fs.existsSync(path.join(MEDIA_DIR, name));
}

// A playlist item as a TV gets it when it takes a playlist: a picture from the media
// folder also carries its size, which the TV uses to decide which pictures it can hold.
function withSize(item) {
  if (item.type !== 'image' || !mediaExists(item.src)) return item;
  try { return Object.assign({}, item, { size: fs.statSync(path.join(MEDIA_DIR, item.src)).size }); }
  catch (e) { return item; }
}

// ---------------------------------------------------------------- helpers

function envNumber(name, fallback) {
  const n = parseInt(process.env[name], 10);
  return isFinite(n) && n >= 0 ? n : fallback;
}

function httpError(code, message) {
  const e = new Error(message);
  e.statusCode = code;
  return e;
}

function sendJson(res, code, obj) {
  const body = Buffer.from(JSON.stringify(obj));
  res.writeHead(code, {
    'Content-Type': 'application/json; charset=utf-8',
    'Content-Length': body.length,
    'Cache-Control': 'no-store',
    'X-Content-Type-Options': 'nosniff'
  });
  res.end(body);
}

// csp is given for the control-side pages; the TV page is left without one so
// that very old TV browsers are not tripped up by it.
function sendHtml(res, text, csp) {
  const body = Buffer.from(text);
  const headers = {
    'Content-Type': 'text/html; charset=utf-8',
    'Content-Length': body.length,
    'Cache-Control': 'no-store',
    'X-Content-Type-Options': 'nosniff',
    'Referrer-Policy': 'no-referrer'
  };
  if (csp) {
    headers['Content-Security-Policy'] = csp;
    headers['X-Frame-Options'] = 'DENY';
  }
  res.writeHead(200, headers);
  res.end(body);
}

function cspFor(page) {
  const script = page.split('<script>')[1].split('</script>')[0];
  const hash = crypto.createHash('sha256').update(script).digest('base64');
  return "default-src 'self'; script-src 'sha256-" + hash + "'; style-src 'unsafe-inline'; " +
    "img-src 'self' data:; media-src 'self'; object-src 'none'; base-uri 'none'; " +
    "form-action 'self'; frame-ancestors 'none'";
}

// ---------------------------------------------------------------- access control

function ipToInt(ip) {
  const m = /^(\d{1,3})\.(\d{1,3})\.(\d{1,3})\.(\d{1,3})$/.exec(ip);
  if (!m) return null;
  const p = m.slice(1).map(Number);
  if (p.some(function (n) { return n > 255; })) return null;
  return ((p[0] * 16777216) + (p[1] << 16) + (p[2] << 8) + p[3]) >>> 0;
}

function parseAllow(raw, label) {
  if (!raw || !raw.trim()) return null;
  return raw.split(',').map(function (s) { return s.trim(); }).filter(Boolean).map(function (entry) {
    const parts = entry.split('/');
    const base = ipToInt(parts[0]);
    const bits = parts.length > 1 ? (/^\d{1,2}$/.test(parts[1]) ? Number(parts[1]) : NaN) : 32;
    if (base === null || parts.length > 2 || !Number.isInteger(bits) || bits < 0 || bits > 32) {
      console.error(label + ': cannot understand "' + entry + '". Use addresses like 10.1.2.3 or 10.1.2.0/24.');
      process.exit(1);
    }
    const mask = bits === 0 ? 0 : (0xFFFFFFFF << (32 - bits)) >>> 0;
    return { base: (base & mask) >>> 0, mask: mask };
  });
}

function clientIp(req) {
  let ip = req.socket.remoteAddress || '';
  if (ip.indexOf('::ffff:') === 0) ip = ip.slice(7);
  if (ip === '::1') ip = '127.0.0.1';
  return ip;
}

function ipAllowed(list, ip) {
  if (!list) return true;
  if (ip === '127.0.0.1') return true; // the server's own console
  const n = ipToInt(ip);
  if (n === null) return false;
  return list.some(function (r) { return ((n & r.mask) >>> 0) === r.base; });
}

function hostName(req) {
  const h = String(req.headers.host || '').replace(/:\d+$/, '');
  return /^[A-Za-z0-9.\-\[\]:]+$/.test(h) ? h : 'localhost';
}

function audit(req, action, detail) {
  const line = JSON.stringify({
    time: new Date().toISOString(), ip: req ? clientIp(req) : '-',
    user: req && req.user ? req.user.username : undefined, action: action, detail: detail
  }) + '\n';
  fs.appendFile(AUDIT_FILE, line, function () {});
}

// ---- accounts: only salted scrypt hashes are ever stored

function makeRecord(password) {
  const salt = crypto.randomBytes(16);
  return { salt: salt.toString('hex'), hash: crypto.scryptSync(password, salt, 64).toString('hex') };
}

function checkPassword(password, rec) {
  return new Promise(function (resolve, reject) {
    crypto.scrypt(password, Buffer.from(rec.salt, 'hex'), 64, function (err, key) {
      if (err) return reject(err);
      const want = Buffer.from(rec.hash, 'hex');
      resolve(key.length === want.length && crypto.timingSafeEqual(key, want));
    });
  });
}

function saveUsers() {
  const tmp = USERS_FILE + '.tmp';
  fs.writeFileSync(tmp, JSON.stringify(users, null, 2), { mode: 0o600 });
  fs.renameSync(tmp, USERS_FILE);
}

function loadUsers() {
  try {
    const list = JSON.parse(fs.readFileSync(USERS_FILE, 'utf8'));
    if (!Array.isArray(list)) throw new Error('users.json is not a list');
    return list;
  } catch (e) {
    if (e.code !== 'ENOENT') throw e;
  }
  const first = function (rec) {
    return { username: 'admin', role: 'admin', screens: null, salt: rec.salt, hash: rec.hash, created: new Date().toISOString() };
  };
  // carry over the password from the earlier single-password version
  let old = null;
  try { old = JSON.parse(fs.readFileSync(AUTH_FILE, 'utf8')); } catch (e) { if (e.code !== 'ENOENT') throw e; }
  if (old && old.salt && old.hash) {
    const list = [first(old)];
    fs.writeFileSync(USERS_FILE, JSON.stringify(list, null, 2), { mode: 0o600 });
    return list;
  }
  // Fallback for quick tests only; set-password is the proper way.
  if (process.env.ADMIN_PASSWORD) return [first(makeRecord(process.env.ADMIN_PASSWORD))];
  return [];
}

let users = loadUsers();
const DUMMY_RECORD = makeRecord(crypto.randomBytes(16).toString('hex')); // keeps timing equal for unknown usernames

function findUser(name) {
  return users.find(function (u) { return u.username === name; });
}

function publicUser(u) {
  return {
    username: u.username, role: u.role, screens: u.screens || null, disabled: !!u.disabled,
    mustChange: !!u.mustChange, created: u.created, lastLogin: u.lastLogin
  };
}

function setPassword(u, password) {
  const rec = makeRecord(password);
  u.salt = rec.salt;
  u.hash = rec.hash;
}

function checkNewPassword(p) {
  if (typeof p !== 'string' || p.length < MIN_PASSWORD || p.length > 200) {
    throw httpError(400, 'Passwords need at least ' + MIN_PASSWORD + ' characters');
  }
  return p;
}

// Admins reach every screen. Others reach all screens (screens: null) or a chosen list.
function canScreen(user, id) {
  return user.role === 'admin' || !user.screens || user.screens.indexOf(id) >= 0;
}

function cleanScreens(v) {
  if (v === null || v === undefined) return null;
  if (!Array.isArray(v)) throw httpError(400, 'screens must be a list or null');
  return state.screens.map(function (s) { return s.id; }).filter(function (id) { return v.indexOf(id) >= 0; });
}

function setOwner(key, user) {
  if (!state.owners) state.owners = {};
  if (user) state.owners[key] = user.username;
  saveState();
}

// ---- sessions and lockout
// Sessions are written to sessions.json, so restarting the server (after replacing
// server.js, say) does not sign everyone out and lose what they were editing. Only a hash
// of each sign-in token is stored, so the file cannot be used to sign in.

function sha(text) { return crypto.createHash('sha256').update(text).digest('hex'); }

// Changes whenever the account's password changes, by any route. A session only counts
// while it matches, so a new password always ends the sessions made with the old one.
function pwTag(u) { return sha(String(u.salt)).slice(0, 16); }
function accessTag(u) { return [u.role, JSON.stringify(u.screens || null), u.disabled ? 1 : 0, pwTag(u)].join('|'); }

function loadSessions() {
  const map = new Map();
  let saved = {};
  try { saved = JSON.parse(fs.readFileSync(SESSIONS_FILE, 'utf8')) || {}; }
  catch (e) { /* missing or damaged: people simply sign in again */ }
  const now = Date.now();
  Object.keys(saved).forEach(function (key) {
    const s = saved[key];
    if (s && typeof s.username === 'string' && s.expires > now) {
      map.set(key, { username: s.username, expires: s.expires, pw: s.pw, active: s.active || now, idle: !!s.idle, secure: !!s.secure });
    }
  });
  return map;
}

function saveSessions() {
  const out = {};
  sessions.forEach(function (s, key) { out[key] = s; });
  try {
    const tmp = SESSIONS_FILE + '.tmp';
    fs.writeFileSync(tmp, JSON.stringify(out), { mode: 0o600 });
    fs.renameSync(tmp, SESSIONS_FILE);
  } catch (e) {
    console.error('Could not save sessions.json: ' + e.message); // not fatal: people sign in again after a restart
  }
}

const sessions = loadSessions(); // sha256(token) -> { username, expires, pw, active, idle }
const fails = new Map();         // address -> { count, first, until, logged }
const signingIn = new Set();     // addresses (IPv6: their /64) whose password is being checked right now
let checking = 0;                // passwords being checked right now, over all addresses

// The lockout and the one-check-at-a-time rule count an IPv6 client by its /64 network,
// because one device can give itself any number of addresses inside it.
function failKey(ip) {
  if (ip.indexOf(':') < 0) return ip;
  const halves = ip.split('%')[0].split('::');
  const head = halves[0] ? halves[0].split(':') : [];
  const tail = halves.length > 1 && halves[1] ? halves[1].split(':') : [];
  const groups = halves.length > 1 ? head.concat(new Array(Math.max(0, 8 - head.length - tail.length)).fill('0'), tail) : head;
  return groups.slice(0, 4).map(function (g) { return (parseInt(g, 16) || 0).toString(16); }).join(':') + '::/64';
}

// One password check. Its slot is held only while scrypt runs, not through the delay after
// a wrong guess, so a few clients sending wrong passwords cannot keep everyone else out.
async function checkGuarded(key, password, rec) {
  if (signingIn.has(key) || checking >= MAX_SIGNING_IN) {
    throw httpError(429, 'Another sign-in is being checked. Try again in a moment.');
  }
  signingIn.add(key);
  checking++;
  try {
    return typeof password === 'string' && password.length <= 200 && await checkPassword(password, rec);
  } finally {
    checking--;
    signingIn.delete(key);
  }
}

function cookieValue(req, name) {
  const parts = String(req.headers.cookie || '').split(';');
  for (let i = 0; i < parts.length; i++) {
    const eq = parts[i].indexOf('=');
    if (eq > 0 && parts[i].slice(0, eq).trim() === name) return parts[i].slice(eq + 1).trim();
  }
  return '';
}

function sessionUser(req) {
  const token = cookieValue(req, 'tvb_session');
  if (!token) return null;
  const key = sha(token);
  const s = sessions.get(key);
  if (!s) return null;
  const now = Date.now();
  if (s.expires < now) { sessions.delete(key); return null; }
  const u = findUser(s.username);
  if (!u || u.disabled || s.pw !== pwTag(u)) { sessions.delete(key); return null; }
  // A sign-in made over plain HTTP, before HTTPS was switched on, left a cookie that
  // browsers also send unencrypted. It stops counting: sign in once more over HTTPS.
  if (TLS_ON && !s.secure) { sessions.delete(key); return null; }
  // Left open and untouched for too long: signed out, for good. The page's own 3-second
  // refresh does not count as being used. Viewers can change nothing, so a status board
  // left up on a wall stays signed in.
  if (s.idle || (IDLE_MS && u.role !== 'viewer' && now - s.active > IDLE_MS)) {
    if (!s.idle) {
      s.idle = true;
      saveSessions();
      audit(req, 'session.idle', { username: u.username });
    }
    req.idleOut = true;
    return null;
  }
  req.session = s;
  return u;
}

function hasSession(req) { return !!sessionUser(req); }

function dropSessions(username, exceptKey) {
  sessions.forEach(function (s, key) { if (s.username === username && key !== exceptKey) sessions.delete(key); });
  saveSessions();
}

function sessionCookie(req, token, maxAgeSeconds) {
  return 'tvb_session=' + token + '; Path=/; HttpOnly; SameSite=Strict; Max-Age=' + maxAgeSeconds +
    (req.socket.encrypted ? '; Secure' : '');
}

function lockedFor(ip) {
  const f = fails.get(ip);
  return f && f.until > Date.now() ? f.until - Date.now() : 0;
}

function noteFail(ip, name) {
  const now = Date.now();
  let f = fails.get(ip);
  if (!f || now - f.first > LOCK_MS) f = { count: 0, first: now, until: 0, names: [] };
  f.count++;
  if (f.names.indexOf(name) < 0 && f.names.length < 50) f.names.push(name);
  if (f.count >= MAX_FAILS) { f.until = now + LOCK_MS; f.count = 0; f.first = now; f.logged = false; f.names = []; }
  fails.set(ip, f);
}

// A correct password clears earlier wrong guesses only when they were all for that same
// account. Signing in to one's own account must not wipe guesses at someone else's.
function clearFails(ip, name) {
  const f = fails.get(ip);
  if (f && !(f.until > Date.now()) && f.names.every(function (n) { return n === name; })) fails.delete(ip);
}

setInterval(function () {
  const now = Date.now();
  let changed = sessions.size > 0; // "last used" moves all the time; keep it on disk for the idle sign-out
  sessions.forEach(function (s, key) { if (s.expires < now) { sessions.delete(key); changed = true; } });
  if (changed) saveSessions();
  pairs.forEach(function (p, pid) { if (now - p.created > PAIR_MS) pairs.delete(pid); });
  fails.forEach(function (f, ip) { if (f.until < now && now - f.first > LOCK_MS) fails.delete(ip); });
}, 10 * 60 * 1000).unref();

// newest first, read from the end of the file
function readAudit(limit) {
  let text = '';
  let partial = false;
  try {
    const st = fs.statSync(AUDIT_FILE);
    const start = Math.max(0, st.size - 1024 * 1024);
    const buf = Buffer.alloc(st.size - start);
    const fd = fs.openSync(AUDIT_FILE, 'r');
    try { fs.readSync(fd, buf, 0, buf.length, start); } finally { fs.closeSync(fd); }
    text = buf.toString('utf8');
    partial = start > 0;
  } catch (e) {
    if (e.code !== 'ENOENT') throw e;
  }
  const lines = text.split('\n');
  if (partial) lines.shift();
  const out = [];
  for (let i = lines.length - 1; i >= 0 && out.length < limit; i--) {
    if (!lines[i]) continue;
    try { out.push(JSON.parse(lines[i])); } catch (e) { /* skip a damaged line */ }
  }
  return out;
}

function sleep(ms) { return new Promise(function (r) { setTimeout(r, ms); }); }

function readJson(req) {
  return new Promise(function (resolve, reject) {
    let size = 0;
    const chunks = [];
    req.on('data', function (c) {
      size += c.length;
      if (size > 1e6) { reject(httpError(413, 'Request too large')); req.destroy(); return; }
      chunks.push(c);
    });
    req.on('end', function () {
      try { resolve(JSON.parse(Buffer.concat(chunks).toString('utf8') || '{}')); }
      catch (e) { reject(httpError(400, 'Invalid JSON')); }
    });
    req.on('error', reject);
  });
}

function isHttpUrl(s) {
  return typeof s === 'string' && /^https?:\/\/[^\s]+$/i.test(s) && s.length < 2000;
}

function clamp(n, lo, hi) { return Math.max(lo, Math.min(hi, n)); }

function cleanItems(items) {
  if (!Array.isArray(items)) throw httpError(400, 'items must be a list');
  if (items.length > 200) throw httpError(400, 'Too many items (max 200)');
  return items.map(function (it) {
    const type = String(it && it.type);
    let d = Number(it.duration);
    if (!isFinite(d)) d = type === 'video' ? 0 : 10;
    const out = { type: type };
    if (type === 'image' || type === 'video') {
      const src = String(it.src || '');
      if (!isHttpUrl(src) && !mediaExists(src)) throw httpError(400, 'Unknown media file: ' + src);
      out.src = src;
      out.fit = it.fit === 'cover' ? 'cover' : 'contain';
      out.duration = type === 'video' ? (d <= 0 ? 0 : clamp(d, 3, 86400)) : clamp(d, 3, 86400);
    } else if (type === 'web') {
      if (!isHttpUrl(it.src)) throw httpError(400, 'Web pages need a full http:// or https:// address');
      out.src = it.src;
      out.duration = clamp(d, 5, 86400);
    } else if (type === 'text') {
      const text = String(it.text || '').slice(0, 500);
      if (!text.trim()) throw httpError(400, 'Text item is empty');
      out.text = text;
      out.duration = clamp(d, 3, 86400);
    } else {
      throw httpError(400, 'Unknown item type: ' + type);
    }
    return out;
  });
}

function cleanName(name, fallback) {
  const n = String(name == null ? '' : name).replace(/[\u0000-\u001f]/g, '').trim().slice(0, 60);
  return n || fallback;
}

function escapeHtml(s) {
  return String(s).replace(/[&<>"']/g, function (c) {
    return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c];
  });
}

// ---------------------------------------------------------------- media

function sendMedia(req, res, name) {
  if (!mediaExists(name)) { res.writeHead(404); res.end('Not found'); return; }
  const file = path.join(MEDIA_DIR, name);
  const st = fs.statSync(file);
  const headers = {
    'Content-Type': MIME[path.extname(name).toLowerCase()],
    'Accept-Ranges': 'bytes',
    'Cache-Control': 'public, max-age=86400',
    'X-Content-Type-Options': 'nosniff',
    'Last-Modified': st.mtime.toUTCString()
  };
  let start = 0;
  let end = st.size - 1;
  let code = 200;
  const m = /^bytes=(\d*)-(\d*)$/.exec(req.headers.range || '');
  if (m && (m[1] || m[2]) && st.size > 0) {
    if (m[1]) {
      start = parseInt(m[1], 10);
      if (m[2]) end = Math.min(parseInt(m[2], 10), st.size - 1);
    } else {
      start = Math.max(0, st.size - parseInt(m[2], 10));
    }
    if (start > end || start >= st.size) {
      res.writeHead(416, { 'Content-Range': 'bytes */' + st.size });
      res.end();
      return;
    }
    code = 206;
    headers['Content-Range'] = 'bytes ' + start + '-' + end + '/' + st.size;
  }
  headers['Content-Length'] = st.size === 0 ? 0 : end - start + 1;
  res.writeHead(code, headers);
  if (req.method === 'HEAD' || st.size === 0) { res.end(); return; }
  const stream = fs.createReadStream(file, { start: start, end: end });
  stream.on('error', function () { res.destroy(); });
  stream.pipe(res);
}

const converting = new Set(); // document names being converted right now
const reserved = new Set();   // names (and 'doc:'+stem) of uploads still arriving or converting
let inflight = 0;             // bytes of uploads already on disk but not yet in the library

function uploadTarget(raw) {
  const base = path.basename(String(raw || '').replace(/\\/g, '/'));
  const ext = path.extname(base).toLowerCase();
  const isDoc = !!DOC_EXT[ext];
  if (!MIME[ext] && !isDoc) {
    throw httpError(400, 'Unsupported file type. Use JPG, PNG, GIF, WEBP, MP4, WEBM, PDF, PowerPoint or Excel.');
  }
  if (isDoc && !HAS_PDF) {
    throw httpError(400, 'Document uploads are not set up. In the server folder run "npm install mupdf", then restart.');
  }
  if (isDoc && ext !== '.pdf' && !SOFFICE) {
    throw httpError(400, 'PowerPoint and Excel files need LibreOffice installed on the server. PDF works without it.');
  }
  let stem = base.slice(0, base.length - ext.length).replace(/[^A-Za-z0-9._-]+/g, '_').replace(/^[._]+/, '').slice(0, 80);
  if (!isDoc) stem = stem.replace(/\.page-/gi, '-page-'); // names like x.page-002 belong to documents
  if (!stem) stem = 'file';
  // A name counts as taken while another upload of it is still arriving, and a document's
  // name is taken while any of its pages exists, not just page 1.
  let pageStems = null;
  const taken = function (st) {
    if (!isDoc) return reserved.has(st + ext) || fs.existsSync(path.join(MEDIA_DIR, st + ext));
    if (converting.has(st) || reserved.has('doc:' + st)) return true;
    if (!pageStems) {
      pageStems = new Set();
      fs.readdirSync(MEDIA_DIR).forEach(function (n) { const m = PAGE_RE.exec(n); if (m) pageStems.add(m[1]); });
    }
    return pageStems.has(st);
  };
  let unique = stem;
  for (let i = 2; taken(unique); i++) unique = stem + '-' + i;
  const hold = isDoc ? 'doc:' + unique : unique + ext;
  reserved.add(hold);
  return { stem: unique, ext: ext, isDoc: isDoc, name: unique + ext, hold: hold };
}

function run(cmd, args, timeoutMs) {
  return new Promise(function (resolve, reject) {
    execFile(cmd, args, { timeout: timeoutMs, windowsHide: true, maxBuffer: 4 * 1024 * 1024 }, function (err, stdout) {
      if (err) reject(err); else resolve(stdout);
    });
  });
}

function findSoffice() {
  const places = [
    process.env.SOFFICE_PATH,
    'C:\\Program Files\\LibreOffice\\program\\soffice.com',
    'C:\\Program Files\\LibreOffice\\program\\soffice.exe',
    'C:\\Program Files (x86)\\LibreOffice\\program\\soffice.exe',
    '/Applications/LibreOffice.app/Contents/MacOS/soffice',
    '/usr/bin/soffice', '/usr/local/bin/soffice', '/usr/bin/libreoffice', '/snap/bin/libreoffice'
  ];
  for (let i = 0; i < places.length; i++) if (places[i] && fs.existsSync(places[i])) return places[i];
  return null;
}

// PowerPoint/Excel -> PDF (LibreOffice) -> one JPEG per page (MuPDF, in a child
// process so a slow or broken file cannot stall or crash the server).
async function convertDocument(file, ext, stem) {
  const work = fs.mkdtempSync(path.join(os.tmpdir(), 'tvboard-'));
  try {
    let pdf = file;
    if (ext !== '.pdf') {
      const src = path.join(work, 'input' + ext);
      fs.copyFileSync(file, src);
      try {
        await run(SOFFICE, [
          '--headless', '--norestore', '--nolockcheck', '--nodefault',
          '-env:UserInstallation=' + pathToFileURL(path.join(work, 'profile')).href,
          '--convert-to', 'pdf', '--outdir', work, src
        ], 180000);
      } catch (e) {
        throw httpError(400, e.killed ? 'Converting that file took too long.' : 'LibreOffice could not convert that file.');
      }
      pdf = path.join(work, 'input.pdf');
      for (let i = 0; i < 20 && !fs.existsSync(pdf); i++) await sleep(500);
      if (!fs.existsSync(pdf)) throw httpError(400, 'LibreOffice could not convert that file.');
    }
    let pages;
    try {
      pages = JSON.parse(await run(process.execPath, [__filename, 'render-pdf', pdf, path.join(work, 'page')], 180000)).pages;
    } catch (e) {
      const why = {
        3: 'Document uploads are not set up. In the server folder run "npm install mupdf", then restart.',
        4: 'That PDF is password-protected. Remove the password and upload it again.',
        5: 'That document has more than ' + MAX_PAGES + ' pages.',
        6: 'That file could not be opened as a document.'
      }[e.code];
      throw httpError(400, why || (e.killed ? 'Converting that file took too long.' : 'That document could not be converted.'));
    }
    let bytes = 0;
    for (let n = 1; n <= pages; n++) bytes += fs.statSync(path.join(work, 'page-' + ('00' + n).slice(-3) + '.jpg')).size;
    checkRoom(bytes); // the pictures count against the disk limits too
    for (let n = 1; n <= pages; n++) {
      const num = ('00' + n).slice(-3);
      const page = stem + '.page-' + num + '.jpg';
      // never over an existing file; a page belongs to its document, never to one uploader
      fs.copyFileSync(path.join(work, 'page-' + num + '.jpg'), path.join(MEDIA_DIR, page), fs.constants.COPYFILE_EXCL);
      if (state.owners) delete state.owners[page];
    }
    return pages;
  } finally {
    fs.rm(work, { recursive: true, force: true }, function () {});
  }
}

async function renderPdfCli(pdfPath, outPrefix) {
  let mupdf;
  try { mupdf = await import('mupdf'); } catch (e) { process.exit(3); }
  let doc;
  try { doc = mupdf.Document.openDocument(fs.readFileSync(pdfPath), 'application/pdf'); } catch (e) { process.exit(6); }
  if (doc.needsPassword()) process.exit(4);
  const count = doc.countPages();
  if (count < 1) process.exit(6);
  if (count > MAX_PAGES) process.exit(5);
  for (let i = 0; i < count; i++) {
    const page = doc.loadPage(i);
    const b = page.getBounds();
    // longest side 1920px: a 16:9 slide comes out at exactly 1920x1080
    const scale = Math.min(4, 1920 / Math.max(b[2] - b[0], b[3] - b[1], 1));
    const pix = page.toPixmap(mupdf.Matrix.scale(scale, scale), mupdf.ColorSpace.DeviceRGB, false, true);
    fs.writeFileSync(outPrefix + '-' + ('00' + (i + 1)).slice(-3) + '.jpg', pix.asJPEG(90));
    pix.destroy();
    page.destroy();
  }
  process.stdout.write(JSON.stringify({ pages: count }));
}

// The file's first bytes must match what its extension claims to be.
function looksLike(file, ext) {
  const b = Buffer.alloc(16);
  const fd = fs.openSync(file, 'r');
  try { fs.readSync(fd, b, 0, 16, 0); } finally { fs.closeSync(fd); }
  switch (ext) {
    case '.jpg': case '.jpeg': return b[0] === 0xFF && b[1] === 0xD8 && b[2] === 0xFF;
    case '.png': return b.slice(0, 8).equals(Buffer.from([0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]));
    case '.gif': return /^GIF8[79]a$/.test(b.toString('latin1', 0, 6));
    case '.webp': return b.toString('latin1', 0, 4) === 'RIFF' && b.toString('latin1', 8, 12) === 'WEBP';
    case '.mp4': case '.m4v': return b.toString('latin1', 4, 8) === 'ftyp';
    case '.webm': return b[0] === 0x1A && b[1] === 0x45 && b[2] === 0xDF && b[3] === 0xA3;
    case '.pdf': return b.toString('latin1', 0, 5) === '%PDF-';
    case '.pptx': case '.xlsx': return b[0] === 0x50 && b[1] === 0x4B && b[2] === 0x03 && b[3] === 0x04;
    case '.ppt': case '.xls': return b.slice(0, 8).equals(Buffer.from([0xD0, 0xCF, 0x11, 0xE0, 0xA1, 0xB1, 0x1A, 0xE1]));
  }
  return false;
}

// Uploads are refused before they can fill the disk the server itself needs.
function checkRoom(bytes) {
  if (MAX_LIBRARY) {
    const used = listMedia().reduce(function (n, m) { return n + m.size; }, 0);
    if (used + inflight + bytes > MAX_LIBRARY) {
      throw httpError(507, 'The media library is full (its limit is ' + Math.round(MAX_LIBRARY / 1048576) + ' MB). Delete some files first.');
    }
  }
  if (MIN_FREE && fs.statfsSync) { // statfsSync: Node 18.15 and newer
    let free = null;
    try { const st = fs.statfsSync(MEDIA_DIR); free = st.bavail * st.bsize; } catch (e) { /* cannot tell: let it through */ }
    if (free !== null && free - bytes < MIN_FREE) {
      throw httpError(507, 'The server is almost out of disk space. Delete some files first.');
    }
  }
}

function upload(req, res, url, still) {
  const target = uploadTarget(url.searchParams.get('name'));
  const name = target.name;
  try {
    if (Number(req.headers['content-length']) > MAX_UPLOAD) throw httpError(413, 'File is too large');
    checkRoom(Number(req.headers['content-length']) || 0);
  } catch (e) {
    reserved.delete(target.hold);
    throw e;
  }
  const tmp = path.join(MEDIA_DIR, '.upload-' + crypto.randomBytes(6).toString('hex'));
  const out = fs.createWriteStream(tmp);
  let size = 0;
  let counted = 0; // this upload's share of inflight
  let nextCheck = ROOM_STEP;
  let failed = false;
  function release() {
    inflight -= counted;
    counted = 0;
    reserved.delete(target.hold);
  }
  function fail(code, message) {
    if (failed) return;
    failed = true;
    release();
    req.unpipe(out);
    out.destroy();
    fs.unlink(tmp, function () {});
    if (!res.headersSent) sendJson(res, code, { error: message });
    req.resume();
  }
  req.on('data', function (c) {
    if (failed) return;
    size += c.length;
    counted += c.length;
    inflight += c.length;
    if (size > MAX_UPLOAD) return fail(413, 'File is too large');
    // The size announced at the start may be missing or wrong, so the room is checked
    // again against what has really arrived, together with the other uploads under way.
    if (size >= nextCheck) {
      nextCheck = size + ROOM_STEP;
      try { checkRoom(0); } catch (e) { fail(e.statusCode || 507, e.message); }
    }
  });
  req.on('aborted', function () { fail(400, 'Upload interrupted'); });
  req.on('error', function () { fail(400, 'Upload failed'); });
  out.on('error', function () { fail(500, 'Could not save the file'); });
  out.on('finish', function () {
    // Anything that goes wrong in here (a file locked by antivirus, a full disk) must end
    // this one upload with an error. Left uncaught it would stop the whole server.
    try { finish(); } catch (e) { console.error(e); fail(500, 'Could not save the file'); }
  });
  function finish() {
    if (failed) return;
    if (!still()) { fail(401, 'Your access changed while this was being sent. Sign in again.'); return; }
    try { checkRoom(0); } catch (e) { fail(e.statusCode || 507, e.message); return; }
    if (size === 0) { fail(400, 'Empty file'); return; }
    if (!looksLike(tmp, target.ext)) {
      fail(400, 'The file contents do not match its type');
      return;
    }
    if (target.isDoc) {
      if (converting.size >= MAX_CONVERTING) {
        fail(429, 'Other documents are being converted right now. Try again in a minute.');
        return;
      }
      converting.add(target.stem);
      convertDocument(tmp, target.ext, target.stem).then(function (pages) {
        setOwner('doc:' + target.stem, req.user);
        audit(req, 'document.upload', { name: name, pages: pages, bytes: size });
        sendJson(res, 200, { name: target.stem, pages: pages });
      }).catch(function (err) {
        if (!err.statusCode) console.error(err);
        if (!res.headersSent) sendJson(res, err.statusCode || 500, { error: err.statusCode ? err.message : 'That document could not be converted.' });
      }).then(function () {
        converting.delete(target.stem);
        release();
        fs.unlink(tmp, function () {});
      });
      return;
    }
    const dest = path.join(MEDIA_DIR, name);
    if (fs.existsSync(dest)) { fail(409, 'A file with that name appeared during the upload. Upload it again.'); return; }
    fs.renameSync(tmp, dest);
    release();
    setOwner(name, req.user);
    audit(req, 'media.upload', { name: name, bytes: size });
    sendJson(res, 200, { name: name });
  }
  req.pipe(out);
}

// ---------------------------------------------------------------- routes

function adminState(req) {
  const user = req.user;
  const now = Date.now();
  // offline: the TV page is not open.  connected: page open, nothing on screen yet.
  // live: the TV has confirmed it is showing the playlist that is published now.
  const status = {};
  const showing = {};
  const visible = state.screens.filter(function (s) { return canScreen(user, s.id); });
  visible.forEach(function (s) {
    const on = !!seen[s.id] && now - seen[s.id] < ONLINE_WINDOW_MS;
    const p = playing[s.id];
    const live = on && s.items.length > 0 && !!p && p.v === s.version && p.i >= 0 && p.i < s.items.length;
    status[s.id] = live ? 'live' : on ? 'connected' : 'offline';
    if (live) showing[s.id] = p.i;
  });
  return {
    screens: visible.map(publicScreen), media: listMedia(), status: status, showing: showing,
    pairing: !!state.pairing,
    docs: { pdf: HAS_PDF, office: HAS_PDF && !!SOFFICE },
    // with TLS on, the TVs use the plain-HTTP port, not the address the admin is on
    tvBase: TLS_ON ? 'http://' + hostName(req) + ':' + PORT : null,
    me: publicUser(user), minPassword: MIN_PASSWORD
  };
}

function userList() { return { users: users.map(publicUser) }; }

async function handle(req, res) {
  const url = new URL(req.url, 'http://localhost');
  let pathname;
  try { pathname = decodeURIComponent(url.pathname); }
  catch (e) { throw httpError(400, 'Bad address'); }
  const seg = pathname.split('/').filter(Boolean);
  const method = req.method;
  const reading = method === 'GET' || method === 'HEAD';
  const ip = clientIp(req);
  if (pathname === '/favicon.ico') { res.writeHead(204); res.end(); return; }

  // ---- TV side: read-only, no login
  const short = /^\/tv(\d+)\/?$/i.exec(pathname); // /tv3 is a shortcut for /tv/3
  const tvSide = !!short || seg[0] === 'tv' || seg[0] === 'media' ||
    (seg[0] === 'api' && (seg[1] === 'player' || seg[1] === 'pair'));
  if (tvSide) {
    if (!reading) throw httpError(405, 'Method not allowed');
    // a signed-in user may load these too (thumbnails, previews)
    if (!ipAllowed(TV_ALLOW, ip) && !hasSession(req)) throw httpError(403, 'Forbidden');
  }
  if (short) { res.writeHead(302, { Location: '/tv/' + short[1] }); res.end(); return; }
  if (seg[0] === 'tv') {
    // The player page holds nothing secret, so it is always served. What it may load is
    // decided where it asks for it: /api/player and /media below.
    if (seg.length > 1) return sendHtml(res, PLAYER_HTML);
    return sendHtml(res, state.pairing ? pairPage(ip) : pickerPage());
  }
  if (seg[0] === 'api' && seg[1] === 'pair' && seg.length === 3) { // a TV that is showing a code asks: am I paired yet?
    if (!state.pairing) return sendJson(res, 200, { go: '/tv' });
    const p = pairs.get(seg[2]);
    if (!p || Date.now() - p.created > PAIR_MS) return sendJson(res, 404, { error: 'That code has run out' });
    return sendJson(res, 200, p.go ? { go: p.go } : {});
  }
  if (seg[0] === 'api' && seg[1] === 'player' && seg.length === 3) {
    const s = findScreen(seg[2]);
    const now = Date.now();
    let give; // the key, for a TV that was already connected when pairing was switched on
    if (state.pairing) {
      if (!keyFits(s, url.searchParams.get('k'))) {
        const adopted = !!s && !!adopt && adopt.until > now && (adopt.ips[s.id] || []).indexOf(ip) >= 0;
        if (!adopted) return sendJson(res, 401, { error: 'This TV is not paired', pair: true });
        give = keyOf(s);
        delete adopt.ips[s.id]; // handed over once, and logged
        audit(req, 'screen.adopt', { id: s.id, tv: ip });
      }
    } else if (!s) {
      return sendJson(res, 404, { error: 'Unknown screen' });
    }
    seen[s.id] = now;
    const from = seenFrom[s.id] || (seenFrom[s.id] = {});
    from[ip] = now;
    if (Object.keys(from).length > 20) {
      Object.keys(from).forEach(function (a) { if (now - from[a] > ONLINE_WINDOW_MS) delete from[a]; });
    }
    const pv = parseInt(url.searchParams.get('v'), 10);
    const pi = parseInt(url.searchParams.get('i'), 10);
    playing[s.id] = { v: isNaN(pv) ? null : pv, i: isNaN(pi) ? -1 : pi };
    return sendJson(res, 200, {
      id: s.id, name: s.name, version: s.version,
      // sizes are only looked up for a TV that does not have this playlist yet
      items: pv === s.version ? s.items : s.items.map(withSize),
      keep: TV_KEEP,
      identify: (identify[s.id] || 0) > now,
      reload: PLAYER_TOKEN + ':' + (s.reloads || 0),
      key: give
    });
  }
  if (seg[0] === 'media' && seg.length === 2) {
    if (state.pairing && !anyKeyFits(url.searchParams.get('k')) && !hasSession(req)) {
      throw httpError(403, 'This TV is not paired');
    }
    return sendMedia(req, res, seg[1]);
  }
  if (tvSide) throw httpError(404, 'Not found');

  // ---- everything below is the control side
  if (!ipAllowed(ADMIN_ALLOW, ip)) throw httpError(403, 'Forbidden');
  if (TLS_ON && !req.socket.encrypted) {
    if (!reading) throw httpError(403, 'The control page is only available over HTTPS');
    res.writeHead(302, { Location: 'https://' + hostName(req) + (HTTPS_PORT === 443 ? '' : ':' + HTTPS_PORT) + req.url });
    res.end();
    return;
  }

  // The fonts of the control and sign-in pages. They are public, like the sign-in page,
  // and never change under the same name, so browsers may keep them for good.
  if (reading && seg[0] === 'fonts' && seg.length === 2) {
    const font = Object.prototype.hasOwnProperty.call(FONTS, seg[1]) ? FONTS[seg[1]] : null;
    if (!font) throw httpError(404, 'Not found');
    res.writeHead(200, {
      'Content-Type': 'font/woff2', 'Content-Length': font.length,
      'Cache-Control': 'public, max-age=31536000, immutable', 'X-Content-Type-Options': 'nosniff'
    });
    res.end(method === 'HEAD' ? undefined : font);
    return;
  }

  if (reading && pathname === '/login') {
    if (hasSession(req)) { res.writeHead(302, { Location: '/' }); res.end(); return; }
    return sendHtml(res, LOGIN_HTML, LOGIN_CSP);
  }
  if (method === 'POST' && pathname === '/api/login') {
    if (req.headers['x-tvboard'] !== '1') throw httpError(403, 'Missing X-TVBoard header');
    if (!users.length) throw httpError(503, 'No admin account exists yet. On the server, run: node server.js set-password');
    const fkey = failKey(ip);
    const locked = function () {
      const wait = lockedFor(fkey);
      if (!wait) return;
      const f = fails.get(fkey);
      if (!f.logged) { f.logged = true; audit(req, 'login.locked'); } // once per lockout: hammering cannot fill the log
      throw httpError(429, 'Too many wrong attempts. Try again in ' + Math.ceil(wait / 60000) + ' minutes.');
    };
    locked();
    const body = await readJson(req);
    locked();
    const name = String(body.username || '').trim().toLowerCase().slice(0, 40);
    const found = findUser(name);
    // One check at a time per address, and only a few at once over all addresses. A wrong
    // guess is counted as soon as its check ends, before the next one from there can start.
    const passOk = await checkGuarded(fkey, body.password, found || DUMMY_RECORD);
    if (!passOk || !found || found.disabled) {
      noteFail(fkey, name);
      audit(req, 'login.fail', { username: name });
      await sleep(500);
      throw httpError(401, 'Wrong username or password');
    }
    clearFails(fkey, found.username);
    const now = Date.now();
    const token = crypto.randomBytes(32).toString('hex');
    sessions.set(sha(token), {
      username: found.username, expires: now + SESSION_MS, pw: pwTag(found), active: now, idle: false,
      secure: !!req.socket.encrypted
    });
    saveSessions();
    res.setHeader('Set-Cookie', sessionCookie(req, token, SESSION_MS / 1000));
    found.lastLogin = new Date().toISOString();
    saveUsers();
    req.user = found;
    audit(req, 'login.ok');
    return sendJson(res, 200, { ok: true });
  }

  const user = sessionUser(req);
  if (!user) {
    const why = req.idleOut ? '?idle=1' : '';
    if (reading && seg[0] !== 'api') { res.writeHead(302, { Location: '/login' + why }); res.end(); return; }
    const e = httpError(401, req.idleOut ? 'You were signed out after a long time without activity' : 'Sign in first');
    e.idle = !!req.idleOut;
    throw e;
  }
  req.user = user;
  // Permissions are checked when a request starts, but its body can arrive much later. A
  // change is applied only if the account still has the same access once the body is in:
  // not signed out, disabled, deleted, demoted or moved to other screens in the meantime.
  const access = accessTag(user);
  const stillAllowed = function () { return sessionUser(req) === user && accessTag(user) === access; };
  const readBody = async function () {
    const body = await readJson(req);
    if (!stillAllowed()) throw httpError(401, 'Your access changed while this was being sent. Sign in again.');
    return body;
  };
  // Only real use keeps a session alive: any change, or a refresh sent after the person
  // touched the page. The page's background refreshes do not carry the header.
  if (!reading || req.headers['x-tvboard-active'] === '1') req.session.active = Date.now();
  if (reading && seg.length === 0) return sendHtml(res, ADMIN_HTML, ADMIN_CSP);
  if (seg[0] !== 'api') throw httpError(404, 'Not found');
  if (method === 'GET' && seg[1] === 'state') return sendJson(res, 200, adminState(req));

  // Changes must come from the control page itself, not from another website.
  if (!reading && req.headers['x-tvboard'] !== '1') throw httpError(403, 'Missing X-TVBoard header');

  if (method === 'POST' && seg[1] === 'logout') {
    sessions.delete(sha(cookieValue(req, 'tvb_session')));
    saveSessions();
    res.setHeader('Set-Cookie', sessionCookie(req, 'x', 0));
    audit(req, 'logout');
    return sendJson(res, 200, { ok: true });
  }
  if (method === 'POST' && seg[1] === 'password') {
    // The current password is guarded like a sign-in: same lockout, same slots. Otherwise a
    // signed-in screen left unattended would allow unlimited guesses at its password.
    const fkey = failKey(ip);
    const wait = lockedFor(fkey);
    if (wait) throw httpError(429, 'Too many wrong attempts. Try again in ' + Math.ceil(wait / 60000) + ' minutes.');
    const body = await readBody();
    if (!(await checkGuarded(fkey, body.current, user))) {
      noteFail(fkey, user.username);
      audit(req, 'password.fail');
      await sleep(500);
      throw httpError(400, 'Your current password is not right');
    }
    const next = checkNewPassword(body.next);
    if (next === body.current) throw httpError(400, 'Choose a password that is different from the current one');
    setPassword(user, next);
    user.mustChange = false;
    saveUsers();
    const curKey = sha(cookieValue(req, 'tvb_session'));
    const cur = sessions.get(curKey);
    if (cur) cur.pw = pwTag(user);          // this device stays signed in
    dropSessions(user.username, curKey);    // sign out this user's other devices
    audit(req, 'password.change');
    return sendJson(res, 200, { ok: true });
  }
  if (user.mustChange) throw httpError(403, 'Change your password before doing anything else');
  const isAdmin = user.role === 'admin';

  // ---- admin only: activity and accounts
  if (seg[1] === 'audit' && method === 'GET') {
    if (!isAdmin) throw httpError(403, 'Only an admin can see the activity log');
    const limit = clamp(parseInt(url.searchParams.get('limit'), 10) || 300, 1, 1000);
    return sendJson(res, 200, { entries: readAudit(limit) });
  }
  if (seg[1] === 'users') {
    if (!isAdmin) throw httpError(403, 'Only an admin can manage users');
    if (method === 'GET' && seg.length === 2) return sendJson(res, 200, userList());
    if (method === 'POST' && seg.length === 2) {
      const body = await readBody();
      const name = String(body.username || '').trim().toLowerCase();
      if (!USERNAME_RE.test(name)) throw httpError(400, 'Usernames are 2 to 32 characters: letters, numbers, dot, dash or underscore');
      if (findUser(name)) throw httpError(400, 'That username is already taken');
      if (!ROLES[body.role]) throw httpError(400, 'Unknown permission level');
      if (users.length >= 200) throw httpError(400, 'Too many users');
      const added = { username: name, role: body.role, screens: cleanScreens(body.screens), mustChange: true, created: new Date().toISOString() };
      setPassword(added, checkNewPassword(body.password));
      users.push(added);
      saveUsers();
      audit(req, 'user.add', { username: name, level: added.role });
      return sendJson(res, 200, userList());
    }
    const target = seg.length === 3 ? findUser(seg[2]) : null;
    if (!target) throw httpError(404, 'Unknown user');
    const self = target === user;
    if (method === 'PUT') {
      const body = await readBody();
      const changes = [];
      if (body.role !== undefined && body.role !== target.role) {
        if (!ROLES[body.role]) throw httpError(400, 'Unknown permission level');
        if (self) throw httpError(400, 'You cannot change your own permission level');
        changes.push('level ' + target.role + ' to ' + body.role);
        target.role = body.role;
      }
      if (body.screens !== undefined) {
        target.screens = cleanScreens(body.screens);
        changes.push('screens: ' + (target.screens ? (target.screens.join(', ') || 'none') : 'all'));
      }
      if (body.disabled !== undefined && !!body.disabled !== !!target.disabled) {
        if (self) throw httpError(400, 'You cannot disable your own account');
        target.disabled = !!body.disabled;
        changes.push(target.disabled ? 'disabled' : 'enabled');
      }
      if (body.password !== undefined) {
        if (self) throw httpError(400, 'Use "Change password" for your own account');
        setPassword(target, checkNewPassword(body.password));
        target.mustChange = true;
        changes.push('password reset');
      }
      if (target.disabled || body.password !== undefined) dropSessions(target.username);
      saveUsers();
      audit(req, 'user.update', { username: target.username, changes: changes });
      return sendJson(res, 200, userList());
    }
    if (method === 'DELETE') {
      if (self) throw httpError(400, 'You cannot delete your own account');
      users = users.filter(function (u) { return u !== target; });
      dropSessions(target.username);
      saveUsers();
      audit(req, 'user.delete', { username: target.username });
      return sendJson(res, 200, userList());
    }
    throw httpError(404, 'Not found');
  }
  if (seg[1] === 'settings' && method === 'PUT') {
    if (!isAdmin) throw httpError(403, 'Only an admin can change this');
    const body = await readBody();
    if (body.pairing !== undefined && !!body.pairing !== !!state.pairing) {
      state.pairing = !!body.pairing;
      adopt = null;
      if (state.pairing) {
        // TVs that are connected at this moment keep working: each is handed its key the
        // next time it asks, but only at the address it has been asking from, and only
        // for a couple of minutes. Every other TV has to be paired with a code.
        const now = Date.now();
        // A TV plays one screen from one address. So a screen is handed over only when exactly
        // one address has been playing it and that address played no other screen. A device
        // that asks for many screens gets no keys; a TV caught up in that is paired by code.
        const ips = {};
        const recent = {};
        const count = {};
        state.screens.forEach(function (s) {
          if (!s.key) s.key = newKey();
          const from = seenFrom[s.id] || {};
          recent[s.id] = Object.keys(from).filter(function (a) { return now - from[a] < ONLINE_WINDOW_MS; });
          recent[s.id].forEach(function (a) { count[a] = (count[a] || 0) + 1; });
        });
        state.screens.forEach(function (s) {
          const r = recent[s.id];
          if (r.length === 1 && count[r[0]] === 1) ips[s.id] = r;
        });
        adopt = { until: now + ADOPT_MS, ips: ips };
      }
      saveState();
      audit(req, state.pairing ? 'pairing.on' : 'pairing.off');
    }
    return sendJson(res, 200, adminState(req));
  }
  if (reading) throw httpError(404, 'Not found');

  // ---- from here on: changes to screens and files (editors and admins)
  if ((ROLES[user.role] || 0) < ROLES.editor) throw httpError(403, 'Your account can look but not change anything');

  if (seg[1] === 'screens') {
    if (method === 'POST' && seg.length === 2) {
      if (!isAdmin) throw httpError(403, 'Only an admin can add screens');
      const body = await readBody();
      let n = 1;
      while (findScreen(String(n))) n++;
      if (state.screens.length >= 100) throw httpError(400, 'Too many screens');
      state.screens.push(newScreen(String(n), cleanName(body.name, 'TV ' + n)));
      saveState();
      audit(req, 'screen.add', { id: String(n) });
      return sendJson(res, 200, adminState(req));
    }
    if (method === 'POST' && seg.length === 3 && seg[2] === 'identify-all') {
      state.screens.forEach(function (s) { if (canScreen(user, s.id)) identify[s.id] = Date.now() + IDENTIFY_MS; });
      return sendJson(res, 200, { ok: true });
    }
    const s = findScreen(seg[2]);
    if (!s) throw httpError(404, 'Unknown screen');
    if (!canScreen(user, s.id)) throw httpError(403, 'Your account cannot change that screen');
    if (method === 'PUT' && seg.length === 3) {
      const body = await readBody();
      const items = body.items === undefined ? null : cleanItems(body.items);
      const name = isAdmin ? cleanName(body.name, s.name) : s.name; // only admins rename screens
      const renamed = name !== s.name;
      s.name = name;
      // A rename is saved on its own and leaves the playlist alone. Only a new playlist
      // raises the version, which is what makes the TV start its playlist again.
      if (items) { s.items = items; s.version++; }
      saveState();
      if (items) audit(req, 'screen.publish', { id: s.id, name: s.name, items: s.items.map(function (it) { return it.src || it.text; }) });
      else if (renamed) audit(req, 'screen.rename', { id: s.id, name: s.name });
      return sendJson(res, 200, adminState(req));
    }
    if (method === 'DELETE' && seg.length === 3) {
      if (!isAdmin) throw httpError(403, 'Only an admin can delete screens');
      state.screens = state.screens.filter(function (x) { return x !== s; });
      delete seen[s.id];      // a screen added later may get this number again
      delete seenFrom[s.id];
      delete playing[s.id];
      delete identify[s.id];
      if (adopt) delete adopt.ips[s.id];
      users.forEach(function (u) { if (u.screens) u.screens = u.screens.filter(function (id) { return id !== s.id; }); });
      saveUsers();
      saveState();
      audit(req, 'screen.delete', { id: s.id, name: s.name });
      return sendJson(res, 200, adminState(req));
    }
    if (method === 'POST' && seg[3] === 'identify') {
      identify[s.id] = Date.now() + IDENTIFY_MS;
      return sendJson(res, 200, { ok: true });
    }
    if (method === 'POST' && seg[3] === 'pair') { // put this screen on the TV that is showing this code
      if (!state.pairing) throw httpError(400, 'TV pairing is switched off');
      const body = await readBody();
      const code = String(body.code == null ? '' : body.code).replace(/\D/g, '');
      const now = Date.now();
      let tv = null;
      pairs.forEach(function (p) { if (!p.go && p.code === code && now - p.created < PAIR_MS) tv = p; });
      if (!tv) throw httpError(400, 'No TV is showing that code. Check the number on the TV; it changes every 15 minutes.');
      tv.go = '/tv/' + encodeURIComponent(s.id) + '#k=' + keyOf(s);
      tv.created = now - PAIR_MS + 60000; // the TV collects it within seconds; after a minute it is gone
      audit(req, 'screen.pair', { id: s.id, name: s.name, tv: tv.ip });
      return sendJson(res, 200, { ok: true });
    }
    if (method === 'POST' && seg[3] === 'unpair') { // a new key: every TV on this screen has to be paired again
      if (!isAdmin) throw httpError(403, 'Only an admin can unpair TVs');
      s.key = newKey();
      if (adopt) delete adopt.ips[s.id];
      saveState();
      audit(req, 'screen.unpair', { id: s.id, name: s.name });
      return sendJson(res, 200, { ok: true });
    }
    if (method === 'POST' && seg[3] === 'reload') {
      s.reloads = (s.reloads || 0) + 1; // saved, so a restart does not look like another reload request
      saveState();
      return sendJson(res, 200, { ok: true });
    }
  }
  if (seg[1] === 'upload' && method === 'POST') return upload(req, res, url, stillAllowed);

  // Deleting a file removes it from every playlist, so only its uploader or an admin may do it.
  const owners = state.owners || {};
  if (seg[1] === 'docs' && method === 'DELETE' && seg.length === 3) {
    const files = listMedia().filter(function (m) { return m.doc === seg[2]; }).map(function (m) { return m.name; });
    if (!files.length) throw httpError(404, 'Unknown document');
    if (!isAdmin && owners['doc:' + seg[2]] !== user.username) throw httpError(403, 'Only the person who uploaded it, or an admin, can delete it');
    files.forEach(function (f) { fs.unlinkSync(path.join(MEDIA_DIR, f)); });
    state.screens.forEach(function (s) {
      const kept = s.items.filter(function (it) { return files.indexOf(it.src) < 0; });
      if (kept.length !== s.items.length) { s.items = kept; s.version++; }
    });
    delete owners['doc:' + seg[2]];
    saveState();
    audit(req, 'document.delete', { name: seg[2], pages: files.length });
    return sendJson(res, 200, adminState(req));
  }
  if (seg[1] === 'media' && method === 'DELETE' && seg.length === 3) {
    if (!mediaExists(seg[2])) throw httpError(404, 'Unknown file');
    if (!isAdmin && owners[seg[2]] !== user.username) throw httpError(403, 'Only the person who uploaded it, or an admin, can delete it');
    fs.unlinkSync(path.join(MEDIA_DIR, seg[2]));
    state.screens.forEach(function (s) {
      const kept = s.items.filter(function (it) { return it.src !== seg[2]; });
      if (kept.length !== s.items.length) { s.items = kept; s.version++; }
    });
    delete owners[seg[2]];
    saveState();
    audit(req, 'media.delete', { name: seg[2] });
    return sendJson(res, 200, adminState(req));
  }
  throw httpError(404, 'Not found');
}

function pickerPage() {
  const links = state.screens.map(function (s) {
    return '<a href="/tv/' + encodeURIComponent(s.id) + '">' + escapeHtml(s.name) + '</a>';
  }).join('');
  return '<!DOCTYPE html><html><head><meta charset="utf-8"><title>Choose this TV</title><style>' +
    'body{margin:0;background:#0f1216;color:#fff;font-family:Arial,Helvetica,sans-serif;text-align:center}' +
    'h1{font-size:44px;margin:50px 0 30px}' +
    'a{display:inline-block;margin:14px;padding:34px 54px;font-size:40px;color:#fff;background:#1d2733;' +
    'border:3px solid #33455c;border-radius:14px;text-decoration:none}' +
    'a:focus,a:hover{background:#2b6fd6;border-color:#fff;outline:none}' +
    '</style></head><body><h1>Which TV is this?</h1>' + (links || '<p>No screens set up yet.</p>') + '</body></html>';
}

// With pairing on, /tv shows a code instead of the list of screens. Each visit gets its
// own code; the page keeps asking /api/pair/<id> until someone signed in has typed it in.
function pairPage(ip) {
  const now = Date.now();
  let mine = 0;
  const taken = {};
  pairs.forEach(function (p, pid) {
    if (now - p.created > PAIR_MS) { pairs.delete(pid); return; }
    taken[p.code] = true;
    if (p.ip === ip) mine++;
  });
  if (pairs.size >= 200 || mine >= 20) { // someone is opening this page over and over
    return PAIR_HTML.replace('__CODE__', '&ndash;').replace('__PID__', '')
      .replace('__HELP__', 'Too many TVs are waiting for a code. This page tries again by itself in a few minutes.');
  }
  let code;
  do { code = ('00000' + crypto.randomInt(0, 1000000)).slice(-6); } while (taken[code]);
  const pid = crypto.randomBytes(16).toString('hex');
  pairs.set(pid, { code: code, ip: ip, created: now });
  return PAIR_HTML.replace('__CODE__', code.slice(0, 3) + ' ' + code.slice(3)).replace('__PID__', pid)
    .replace('__HELP__', 'On the Screen Cast control page, select a screen, press <b>Pair a TV</b> and type this code.');
}

// Plain ES5, like the player page: it runs on the TVs.
const PAIR_HTML = String.raw`<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Pair this TV</title>
<style>
html,body{margin:0;width:100%;height:100%;background:#0f1216;overflow:hidden;color:#fff;font-family:Arial,Helvetica,sans-serif}
.box{position:absolute;left:0;top:0;width:100%;height:100%;display:table}
.box>div{display:table-cell;vertical-align:middle;text-align:center;padding:5vw}
h1{font-size:4vw;font-weight:normal;color:#8d96a5;margin:0 0 3vw}
#code{font-size:17vw;font-weight:bold;letter-spacing:.04em;line-height:1}
p{font-size:2.6vw;color:#8d96a5;margin:3vw 0 0}
p b{color:#fff}
</style>
</head>
<body>
<div class="box"><div>
<h1>This TV is not paired yet</h1>
<div id="code">__CODE__</div>
<p>__HELP__</p>
</div></div>
<script>
(function () {
  var pid = '__PID__';
  // A TV that has been paired before goes straight back to its screen. "lost" means the
  // screen has just turned its key down, so it is forgotten and a code is shown.
  try {
    if (/[?&]lost=/.test(location.search)) {
      localStorage.removeItem('tvb_screen');
      localStorage.removeItem('tvb_key');
    } else {
      var sid = localStorage.getItem('tvb_screen'), key = localStorage.getItem('tvb_key');
      if (sid && key) { location.replace('/tv/' + encodeURIComponent(sid) + '#k=' + key); return; }
    }
  } catch (e) {}

  function again() { location.replace('/tv'); }
  if (!pid) { setTimeout(again, 180000); return; }

  function poll() {
    var x = new XMLHttpRequest();
    x.open('GET', '/api/pair/' + pid + '?t=' + new Date().getTime(), true);
    x.timeout = 8000;
    x.onreadystatechange = function () {
      if (x.readyState !== 4) return;
      if (x.status === 404) { again(); return; } // the code ran out, or the server restarted: show a new one
      if (x.status !== 200) return;
      var d;
      try { d = JSON.parse(x.responseText); } catch (e) { return; }
      if (d.go) location.replace(d.go);
    };
    x.send(null);
  }
  setInterval(poll, 3000);
})();
</script>
</body>
</html>`;

// ---------------------------------------------------------------- TV player page
// Written in plain ES5 on purpose: TV browsers are often years behind.

const PLAYER_HTML = String.raw`<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Screen Cast</title>
<style>
html,body{margin:0;width:100%;height:100%;background:#000;overflow:hidden;cursor:none;color:#fff;font-family:Arial,Helvetica,sans-serif}
.layer{position:absolute;left:0;top:0;width:100%;height:100%;background:#000;opacity:0;z-index:1;-webkit-transition:opacity .8s;transition:opacity .8s}
.layer.on{opacity:1;z-index:2}
.layer img,.layer video,.layer iframe{position:absolute;left:0;top:0;width:100%;height:100%;border:0;background:#000}
.layer img,.layer video{object-fit:contain}
.layer .cover{object-fit:cover}
.layer iframe{background:#fff}
.box{position:absolute;left:0;top:0;width:100%;height:100%;display:table}
.box>div{display:table-cell;vertical-align:middle;text-align:center;padding:5vw;white-space:pre-wrap;word-wrap:break-word}
#idle,#badge{display:none}
#idle{z-index:5;background:#0f1216}
#idle h1{font-size:9vw;margin:0}
#idle p{font-size:2.6vw;color:#8d96a5}
#badge{z-index:10;background:rgba(20,80,180,.93)}
#badge h1{font-size:14vw;margin:0}
#badge p{font-size:3vw;margin:2vw 0 0}
</style>
</head>
<body>
<div id="a" class="layer"></div>
<div id="b" class="layer"></div>
<div id="idle" class="box"><div><h1 id="idleName"></h1><p id="idleMsg"></p></div></div>
<div id="badge" class="box"><div><h1 id="badgeName"></h1><p id="badgeUrl"></p></div></div>
<script>
(function () {
  var id = '';
  try { id = decodeURIComponent(location.pathname.split('/')[2] || ''); } catch (e) {}
  var layers = [document.getElementById('a'), document.getElementById('b')];
  var idle = document.getElementById('idle');
  var badge = document.getElementById('badge');
  var front = 0, token = 0, timer = null;
  var items = [], idx = -1, version = null, reloadToken = null;
  var shown = -1, reportSoon = false; // which item is really on screen, told to the server
  var started = new Date().getTime();

  // Pictures this TV holds. The pictures of the playlist are fetched ahead of time and held
  // on to, so that they keep going round while the server cannot be reached (its PC is
  // asleep, switched off or away). Videos are not held, they are too big. While the server
  // is away the TV still tries everything it does not hold, as the browser may have kept a
  // copy, and leaves out whatever fails until the server is back. Nothing survives this
  // page being closed or the TV switched off.
  var pics = {};       // file name -> { el: the loaded <img>, ok: is it loaded, tried: when it was last fetched }
  var wanted = [];     // the file names to hold, in playlist order
  var ahead = null;    // the picture being fetched ahead of time: { src, el }
  var misses = 0;      // answers from the server missed in a row
  var away = false;    // the server cannot be reached
  var skip = {};       // while it is away: playlist positions that failed, left out until it is back
  var waiting = 0;     // when the item being loaded for the screen started loading (0: none)

  // With TV pairing on, the server only answers a TV that sends its screen's key. The key
  // arrives after the # in the address when the TV is paired, and is kept in this browser
  // so that an old bookmark without it still works.
  var key = '', kept = false;
  var inHash = /[#&]k=([0-9a-f]+)/.exec(location.hash || '');
  if (inHash) key = inHash[1];
  try {
    if (!key && localStorage.getItem('tvb_screen') === id) key = localStorage.getItem('tvb_key') || '';
  } catch (e) {}

  function keep(k) {
    key = k;
    kept = true;
    try { localStorage.setItem('tvb_screen', id); localStorage.setItem('tvb_key', k); } catch (e) {}
    try { if (location.hash !== '#k=' + k) location.hash = 'k=' + k; } catch (e) {}
  }

  function setText(elId, text) {
    var el = document.getElementById(elId);
    while (el.firstChild) el.removeChild(el.firstChild);
    el.appendChild(document.createTextNode(text));
  }

  function clearLayer(el) {
    var vids = el.getElementsByTagName('video');
    for (var i = 0; i < vids.length; i++) {
      try { vids[i].pause(); vids[i].removeAttribute('src'); vids[i].load(); } catch (e) {}
    }
    while (el.firstChild) el.removeChild(el.firstChild);
  }

  function swap(back) {
    var old = layers[front];
    var oldGen = old._gen;
    front = 1 - front;
    back.className = 'layer on';
    old.className = 'layer';
    setTimeout(function () {
      if (old._gen === oldGen && old !== layers[front]) clearLayer(old);
    }, 1000);
  }

  function mediaUrl(src) {
    return /^https?:\/\//i.test(src) ? src : '/media/' + encodeURIComponent(src) + (key ? '?k=' + key : '');
  }

  function showIdle(msg) {
    setText('idleMsg', msg);
    idle.style.display = 'table';
  }

  function ours(src) { return !/^https?:\/\//i.test(src || ''); } // a file on the server, not an address elsewhere

  // A new playlist: choose the pictures to hold, as many as fit in the room the server
  // allows. A picture that is held already stays held.
  function choose(room) {
    var old = pics, seen = {}, i, it;
    pics = {};
    wanted = [];
    room = room > 0 ? room : 0;
    for (i = 0; i < items.length; i++) {
      it = items[i];
      if (it.type !== 'image' || !ours(it.src) || seen[it.src]) continue;
      seen[it.src] = true;
      if (!(it.size > 0) || it.size > room) continue; // no room for it: fetched each time it is shown
      room -= it.size;
      pics[it.src] = old[it.src] || { el: null, ok: false, tried: 0 };
      wanted.push(it.src);
    }
    if (ahead && !pics[ahead.src]) dropAhead();
  }

  function hold(src, el) {
    var p = pics[src];
    if (p && !p.ok) { p.el = el; p.ok = true; }
  }

  function dropAhead() {
    if (!ahead) return;
    var el = ahead.el, p = pics[ahead.src];
    ahead = null;
    el.onload = el.onerror = null;
    try { el.removeAttribute('src'); } catch (e) {}
    if (p && !p.ok) p.tried = 0; // fetch it again as soon as the server answers
  }

  // Fetch the next picture that is not held yet. One at a time, so that a TV on slow Wi-Fi
  // is not swamped. A picture that could not be fetched is tried again a minute later.
  function fetchAhead() {
    if (ahead || away) return;
    var now = new Date().getTime(), src = null, i, p;
    for (i = 0; i < wanted.length; i++) {
      p = pics[wanted[i]];
      if (!p.ok && now - p.tried > 60000) { src = wanted[i]; break; }
    }
    if (src === null) return;
    p.tried = now;
    var el = document.createElement('img');
    ahead = { src: src, el: el };
    el.onload = function () {
      if (!ahead || ahead.el !== el) return;
      ahead = null;
      hold(src, el);
      setTimeout(fetchAhead, 200);
    };
    el.onerror = function () {
      if (!ahead || ahead.el !== el) return;
      ahead = null;
      setTimeout(fetchAhead, 200);
    };
    el.src = mediaUrl(src);
  }

  function next() {
    clearTimeout(timer);
    if (!items.length) {
      token++;
      waiting = 0;
      clearLayer(layers[0]);
      clearLayer(layers[1]);
      showIdle('Nothing assigned to this TV yet');
      return;
    }
    idle.style.display = 'none';
    var n = items.length, step, at;
    if (away) {
      // The server cannot be reached: go on to the next item that has not failed meanwhile.
      for (step = 1; step <= n; step++) {
        at = (idx + step) % n;
        if (!skip[at]) { idx = at; show(items[idx]); return; }
      }
      skip = {}; // everything failed: keep trying them all in turn
    }
    idx = (idx + 1) % n;
    show(items[idx]);
  }

  function show(item) {
    var my = ++token;
    var back = layers[1 - front];
    var single = items.length === 1;
    var done = false;
    var stay = false; // the picture asked for is the one on screen: leave the layers alone
    var el, pic;
    var at = idx;
    clearLayer(back);
    back._gen = my;
    waiting = new Date().getTime();

    function ready() {
      if (done || my !== token) return;
      done = true;
      waiting = 0;
      if (!stay) swap(back);
      shown = at;
      if (reportSoon) { reportSoon = false; setTimeout(poll, 400); } // confirm a new playlist quickly
      if (item.type === 'video') return; // videos move on when they end
      if (!single) timer = setTimeout(next, (item.duration || 10) * 1000);
    }
    function fail() {
      if (done || my !== token) return;
      done = true;
      waiting = 0;
      if (away) skip[at] = true; // not tried again until the server is back
      timer = setTimeout(next, 3000); // skip a broken item, retry on the next lap
    }

    if (item.type === 'image') {
      pic = pics[item.src];
      if (pic && pic.ok) {
        // Held by this TV: the loaded picture itself goes on screen and nothing is fetched.
        el = pic.el;
        stay = el.parentNode === layers[front];
        el.className = item.fit === 'cover' ? 'cover' : '';
        if (!stay) back.appendChild(el);
        ready();
      } else {
        el = document.createElement('img');
        if (item.fit === 'cover') el.className = 'cover';
        el.onload = function () { hold(item.src, el); ready(); };
        el.onerror = fail;
        el.src = mediaUrl(item.src);
        back.appendChild(el);
      }
    } else if (item.type === 'video') {
      el = document.createElement('video');
      if (item.fit === 'cover') el.className = 'cover';
      el.muted = true;
      el.autoplay = true;
      el.setAttribute('muted', '');
      el.setAttribute('playsinline', '');
      el.preload = 'auto';
      if (single && !item.duration) el.loop = true;
      el.oncanplay = function () {
        ready();
        try { var p = el.play(); if (p && p['catch']) p['catch'](function () {}); } catch (e) {}
      };
      el.onloadedmetadata = function () {
        if (my !== token || el.loop) return;
        var secs = item.duration > 0 ? item.duration : (isFinite(el.duration) ? el.duration + 5 : 600);
        clearTimeout(timer);
        timer = setTimeout(function () { if (my === token) next(); }, secs * 1000);
      };
      el.onended = function () { if (my === token) next(); };
      el.onerror = fail;
      el.src = mediaUrl(item.src);
      back.appendChild(el);
    } else if (item.type === 'web') {
      el = document.createElement('iframe');
      // The page shown may run its own scripts, but it cannot take over the TV: no sending
      // the whole screen to another address, no pop-ups, no message boxes that would
      // freeze the playlist. It is not told the TV's own address either.
      el.setAttribute('sandbox', 'allow-scripts allow-same-origin allow-forms');
      el.setAttribute('referrerpolicy', 'no-referrer');
      el.onload = ready;
      el.src = item.src;
      back.appendChild(el);
      setTimeout(ready, 4000);
    } else {
      var box = document.createElement('div');
      var cell = document.createElement('div');
      var text = item.text || '';
      box.className = 'box';
      cell.style.fontSize = text.length < 40 ? '8vw' : (text.length < 140 ? '5vw' : '3.4vw');
      cell.appendChild(document.createTextNode(text));
      box.appendChild(cell);
      back.appendChild(box);
      ready();
    }
  }

  // The server did not answer. After two misses in a row it counts as away: stop fetching
  // ahead, and give up on an item that has been loading for a while, as it is not coming.
  function missed() {
    misses++;
    if (misses < 2) return;
    if (!away) { away = true; skip = {}; dropAhead(); }
    if (waiting && new Date().getTime() - waiting > 5000 && idx >= 0 && idx < items.length) {
      skip[idx] = true;
      next();
    }
  }

  function poll() {
    var x = new XMLHttpRequest();
    x.open('GET', '/api/player/' + encodeURIComponent(id) + '?t=' + new Date().getTime() +
      '&v=' + (version === null ? '' : version) + '&i=' + shown + (key ? '&k=' + key : ''), true);
    x.timeout = 8000;
    x.onreadystatechange = function () {
      if (x.readyState !== 4) return;
      if (x.status === 401) { location.replace('/tv?lost=1'); return; } // not paired (any more): go and show a code
      if (x.status === 404) {
        misses = 0; away = false; skip = {};
        items = []; version = null;
        choose(0);
        setText('idleName', 'Unknown TV');
        next();
        showIdle('Open ' + location.host + '/tv and choose this TV');
        return;
      }
      if (x.status !== 200) { missed(); return; } // server unreachable: keep showing what we have
      var d;
      try { d = JSON.parse(x.responseText); } catch (e) { missed(); return; }
      misses = 0;
      if (away) { away = false; skip = {}; } // back: everything is tried again
      var wantsReload = reloadToken !== null && d.reload !== reloadToken;
      var stale = new Date().getTime() - started > 24 * 3600 * 1000;
      if (wantsReload || stale) { location.reload(); return; }
      if (d.key) keep(d.key);            // pairing was just switched on and this TV was already connected
      else if (key && !kept) keep(key);  // the key works: remember it
      reloadToken = d.reload;
      setText('idleName', d.name);
      setText('badgeName', d.name);
      setText('badgeUrl', location.host + '/tv/' + d.id);
      badge.style.display = d.identify ? 'table' : 'none';
      if (d.version !== version) {
        version = d.version;
        items = d.items || [];
        idx = -1;
        shown = -1;
        reportSoon = true;
        skip = {};
        choose(d.keep);
        next();
        setTimeout(fetchAhead, 1500); // the first item gets a head start
      } else {
        fetchAhead(); // carries on after a failed fetch or after the server was away
      }
    };
    x.send(null);
  }

  poll();
  setInterval(poll, 5000);
})();
</script>
</body>
</html>`;

// Each TV reloads its page when this changes. It is tied to the player page itself, so a
// restart only makes the TVs reload when an update really changed what they run.
const PLAYER_TOKEN = sha(PLAYER_HTML).slice(0, 12);

// ---------------------------------------------------------------- control page

const ADMIN_HTML = String.raw`<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Screen Cast</title>
<link rel="icon" type="image/svg+xml" href="data:image/svg+xml,%3Csvg%20xmlns%3D%22http%3A%2F%2Fwww.w3.org%2F2000%2Fsvg%22%20viewBox%3D%220%200%20100%20100%22%3E%3Cdefs%3E%3CradialGradient%20id%3D%22g%22%20cx%3D%22.3%22%20cy%3D%22.25%22%20r%3D%22.9%22%3E%3Cstop%20offset%3D%220%22%20stop-color%3D%22%233a3e46%22%2F%3E%3Cstop%20offset%3D%221%22%20stop-color%3D%22%2316181c%22%2F%3E%3C%2FradialGradient%3E%3C%2Fdefs%3E%3Crect%20width%3D%22100%22%20height%3D%22100%22%20rx%3D%2224%22%20fill%3D%22url(%23g)%22%2F%3E%3Cg%20transform%3D%22translate(9%209)%20scale(.82)%22%3E%3Cpath%20d%3D%22M71.13%2010.27A45%2045%200%200%201%2028.87%2089.73M17.63%2081.26A45%2045%200%200%201%2017.63%2018.74%22%20fill%3D%22none%22%20stroke-width%3D%228%22%20stroke-linecap%3D%22round%22%20stroke%3D%22%23eef0f3%22%2F%3E%3Cpath%20d%3D%22M28.87%2010.27A45%2045%200%200%201%2057.81%205.68%22%20fill%3D%22none%22%20stroke-width%3D%228%22%20stroke-linecap%3D%22round%22%20stroke%3D%22%23ff7a2e%22%2F%3E%3Cg%20fill%3D%22%23eef0f3%22%3E%3Ccircle%20cx%3D%2233%22%20cy%3D%2224.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2250%22%20cy%3D%2224.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2258.5%22%20cy%3D%2224.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2267%22%20cy%3D%2224.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2224.5%22%20cy%3D%2233%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2258.5%22%20cy%3D%2233%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2267%22%20cy%3D%2233%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2275.5%22%20cy%3D%2233%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2224.5%22%20cy%3D%2241.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2275.5%22%20cy%3D%2241.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2224.5%22%20cy%3D%2250%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2224.5%22%20cy%3D%2258.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2275.5%22%20cy%3D%2258.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2224.5%22%20cy%3D%2267%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2258.5%22%20cy%3D%2267%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2267%22%20cy%3D%2267%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2275.5%22%20cy%3D%2267%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2233%22%20cy%3D%2275.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2250%22%20cy%3D%2275.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2258.5%22%20cy%3D%2275.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2267%22%20cy%3D%2275.5%22%20r%3D%222.6%22%2F%3E%3C%2Fg%3E%3Cpath%20d%3D%22M39%2031L39%2069L71%2050Z%22%20fill%3D%22%23eef0f3%22%20stroke%3D%22%23eef0f3%22%20stroke-width%3D%228%22%20stroke-linejoin%3D%22round%22%2F%3E%3C%2Fg%3E%3C%2Fsvg%3E">
<style>
/* Neumorphic look: everything is one soft surface. Things either rise out of it (two
   shadows, light from the top left) or are pressed into it (the same two, inset). */
@font-face{font-family:"Unbounded";src:url(/fonts/unbounded-v1.woff2) format("woff2");font-weight:200 900;font-style:normal;font-display:swap}
@font-face{font-family:"Jost";src:url(/fonts/jost-v1.woff2) format("woff2");font-weight:100 900;font-style:normal;font-display:swap}
:root{color-scheme:light;--bg:#e6e7eb;--text:#24272c;--mute:#5a5f68;--line:rgba(120,128,142,.26);--hi:rgba(255,255,255,.95);--lo:rgba(163,169,184,.74);--accent:#b03f08;--glow:#ff7a2e;--ok:#0b6e3f;--warn:#7f5900;--bad:#b52a38;--link:#2a5db5;--led:#b3b8c2;--live:#22c06c;--busy:#f2b100;--veil:rgba(214,216,223,.74);--sans:"Jost","Century Gothic","Avenir Next",Avenir,Futura,"URW Gothic","Segoe UI Variable Text","Segoe UI",system-ui,-apple-system,Roboto,sans-serif;--wide:"Unbounded","Century Gothic","Avenir Next",Avenir,Futura,"Segoe UI",system-ui,sans-serif;--mono:"Cascadia Mono",Consolas,ui-monospace,"SF Mono",monospace;--up:8px 8px 18px var(--lo),-8px -8px 18px var(--hi);--up2:4px 4px 10px var(--lo),-4px -4px 10px var(--hi);--up1:2px 2px 5px var(--lo),-2px -2px 5px var(--hi);--in:inset 5px 5px 11px var(--lo),inset -5px -5px 11px var(--hi);--in2:inset 3px 3px 6px var(--lo),inset -3px -3px 6px var(--hi)}
:root[data-theme=dark]{color-scheme:dark;--bg:#282b31;--text:#e9ebef;--mute:#a3a9b3;--line:rgba(255,255,255,.09);--hi:rgba(255,255,255,.07);--lo:rgba(0,0,0,.55);--accent:#ff8a45;--glow:#ff8a45;--ok:#3ddc84;--warn:#ffd23f;--bad:#ff7b7b;--link:#8ab8ff;--led:#474c55;--live:#3ddc84;--busy:#ffd23f;--veil:rgba(22,24,28,.74)}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--text);font:16px/1.5 var(--sans)}
header{position:sticky;top:0;z-index:20;display:flex;flex-wrap:wrap;align-items:center;gap:16px;padding:14px 26px;background:var(--bg);box-shadow:0 10px 18px -10px var(--lo)}
.brand{font:600 14px/1 var(--wide);letter-spacing:.16em;display:flex;align-items:center;gap:12px;white-space:nowrap}
.brand svg{width:30px;height:30px;flex:none}
.tabs{display:inline-flex;gap:6px;padding:6px;border-radius:999px;box-shadow:var(--in2)}
.tabs button{box-shadow:none;color:var(--mute);padding:9px 16px}
.tabs button:hover{color:var(--text);box-shadow:none}
.tabs button.on{color:var(--text);box-shadow:var(--up2)}
#status{flex:1;min-width:140px;color:var(--mute);font-size:14px;text-align:right}
#status.err{color:var(--bad);font-weight:600}
#who{font:600 11px/1 var(--sans);letter-spacing:.12em;text-transform:uppercase;color:var(--mute);padding:12px 15px;border-radius:999px;box-shadow:var(--in2);white-space:nowrap}
main{display:grid;grid-template-columns:410px 1fr;gap:30px;padding:30px 26px;max-width:1400px;margin:0 auto}
main>div{min-width:0}
.page{max-width:1400px;margin:0 auto;padding:30px 26px}
.panel{background:var(--bg);border-radius:30px;padding:24px;margin-bottom:30px;box-shadow:var(--up)}
.phead{display:flex;flex-wrap:wrap;align-items:center;justify-content:space-between;gap:12px;margin:0 0 18px}
.panel h2{font:600 11px/1.3 var(--wide);text-transform:uppercase;letter-spacing:.16em;color:var(--text);margin:0 0 14px}
.phead h2{margin:0}
.badge{font:600 11px/1 var(--sans);letter-spacing:.1em;text-transform:uppercase;color:var(--mute);border-radius:999px;padding:9px 13px;white-space:nowrap;box-shadow:var(--in2)}
.badge.warn{color:var(--warn)}
button,.btn{display:inline-block;font:600 12px/1.2 var(--sans);letter-spacing:.14em;text-transform:uppercase;color:var(--text);background:var(--bg);border:0;border-radius:999px;padding:12px 18px;cursor:pointer;box-shadow:var(--up2);transition:box-shadow .15s,color .15s}
button:hover,.btn:hover{box-shadow:var(--up1)}
button:active,.btn:active{box-shadow:var(--in2)}
button:focus-visible,.btn:focus-within,input:focus-visible,select:focus-visible,.screen:focus-visible{outline:2px solid var(--accent);outline-offset:3px}
button.primary{color:var(--accent)}
button.primary:disabled{color:var(--ok);box-shadow:var(--in2);cursor:default}
button.danger:hover{color:var(--bad)}
button.go{color:var(--bad)}
button.small{padding:9px 12px}
button.icon{width:42px;height:42px;padding:0;font-size:17px;line-height:42px;text-align:center}
input,select{font:inherit;color:var(--text);background:var(--bg);border:0;border-radius:16px;padding:12px 16px;box-shadow:var(--in2)}
input::placeholder{color:var(--mute)}
input:focus,select:focus{outline:2px solid var(--accent);outline-offset:1px}
input[type=checkbox]{box-shadow:none;accent-color:var(--accent);width:17px;height:17px;padding:0}
input[readonly]{color:var(--mute)}
#editor .phead input{font:500 14px/1.3 var(--wide)}
.lcd{border-radius:26px;padding:10px;box-shadow:var(--in)}
.screen{display:flex;align-items:center;gap:12px;padding:12px 14px;border-radius:18px;cursor:pointer;transition:box-shadow .15s}
.screen+.screen{margin-top:4px}
.screen:hover{box-shadow:var(--up1)}
.screen.sel{box-shadow:var(--up2)}
.screen .who{flex:1;min-width:0}
.screen .nm{font:500 13px/1.35 var(--wide);letter-spacing:.01em;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.screen .sub{font-size:13px;color:var(--mute);overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.screen .edited{color:var(--accent);font:600 10px/1 var(--sans);letter-spacing:.14em;margin-left:8px}
.screen .rm{flex:none;padding:7px 10px;box-shadow:none;color:var(--mute)}
.screen .rm:hover,.screen .rm:focus-visible{color:var(--bad);box-shadow:var(--in2)}
.modal{position:fixed;left:0;top:0;right:0;bottom:0;z-index:50;display:flex;align-items:center;justify-content:center;padding:20px;background:var(--veil);-webkit-backdrop-filter:blur(4px);backdrop-filter:blur(4px)}
.modal .panel{width:100%;max-width:480px;margin:0;box-shadow:var(--up),0 30px 60px rgba(0,0,0,.2)}
.modal p{margin:0 0 20px;word-wrap:break-word}
.modal input{width:100%;margin-bottom:20px}
.modal .row{justify-content:flex-end}
.st{font:600 11px/1 var(--sans);letter-spacing:.16em;text-transform:uppercase;white-space:nowrap;color:var(--mute)}
.st.live{color:var(--ok)}
.st.connected{color:var(--warn)}
.led{display:inline-block;width:12px;height:12px;border-radius:50%;flex:none;background:var(--led);box-shadow:inset 1px 1px 2px rgba(0,0,0,.28)}
.led.live{background:var(--live);box-shadow:0 0 10px var(--live)}
.led.connected{background:var(--busy);box-shadow:0 0 10px var(--busy)}
.led.dirty{background:var(--glow);box-shadow:0 0 10px var(--glow)}
.legend{display:grid;gap:8px;margin-top:20px;font-size:14px;color:var(--mute)}
.legend>span{display:flex;align-items:flex-start;gap:10px}
.legend .led{margin-top:4px}
.legend b{color:var(--text);font-weight:600}
.state{display:inline-flex;align-items:center;gap:9px;font:600 11px/1 var(--sans);letter-spacing:.14em;text-transform:uppercase;color:var(--mute);border-radius:999px;padding:11px 15px;white-space:nowrap;box-shadow:var(--in2)}
.state.live{color:var(--ok)}
.state.connected{color:var(--warn)}
.state.dirty{color:var(--accent)}
.row{display:flex;gap:12px;align-items:center;flex-wrap:wrap}
.spread{justify-content:space-between}
.url{font:13px/1.4 var(--mono);color:var(--link);word-break:break-all}
.hint{color:var(--mute);font-size:14px}
.item{display:flex;align-items:center;gap:12px;padding:10px 14px;border-radius:22px;margin-bottom:14px;box-shadow:var(--up2)}
.item .no{font:500 11px/1 var(--wide);color:var(--mute);width:26px;text-align:center}
.item .th{width:78px;height:46px;border-radius:14px;flex:none;object-fit:cover;display:flex;align-items:center;justify-content:center;font:600 10px/1 var(--sans);color:var(--mute);text-transform:uppercase;letter-spacing:.14em;box-shadow:var(--in2)}
.item .lb{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.item input{width:78px}
.empty{padding:30px;text-align:center;color:var(--mute);border-radius:22px;margin-bottom:14px;box-shadow:var(--in2)}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(150px,1fr));gap:20px}
.tile{position:relative;border-radius:22px;overflow:hidden;cursor:pointer;box-shadow:var(--up2);transition:box-shadow .15s}
.tile:hover{box-shadow:var(--up)}
.tile:active{box-shadow:var(--in2)}
.tile img,.tile video{display:block;width:100%;height:90px;object-fit:cover;background:var(--led)}
.tile .cap{padding:9px 12px;font-size:13px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.tile .sz{color:var(--mute)}
.tile .del{position:absolute;top:7px;right:7px;padding:6px 9px;box-shadow:1px 1px 4px rgba(0,0,0,.3)}
.tag{position:absolute;top:8px;left:8px;font:600 10px/1 var(--sans);letter-spacing:.12em;color:var(--text);background:var(--bg);padding:6px 9px;border-radius:999px;text-transform:uppercase;box-shadow:1px 1px 4px rgba(0,0,0,.3)}
#drop.over{box-shadow:var(--in)}
.adders{margin-top:22px}
.adders input{flex:1;min-width:180px}
[hidden]{display:none!important}
#userList,#actList{overflow-x:auto}
table{width:100%;border-collapse:collapse}
th,td{text-align:left;padding:13px 10px;border-bottom:1px solid var(--line);font-size:15px;vertical-align:top}
th{font:600 11px/1.2 var(--sans);color:var(--mute);text-transform:uppercase;letter-spacing:.16em}
tr:last-child td{border-bottom:0}
.chk{display:inline-flex;align-items:center;gap:7px;margin:0 14px 8px 0;white-space:nowrap}
.field{display:block;margin-bottom:18px}
.field span{display:block;font:600 11px/1.2 var(--sans);letter-spacing:.16em;text-transform:uppercase;color:var(--mute);margin:0 0 9px 6px}
.field input{width:100%;max-width:340px}
.adminOnly{display:none!important}
body.admin .adminOnly{display:inline-block!important}
body.readonly #editor button,body.readonly #editor .adders,body.readonly #drop label.btn,body.readonly .tile .del,body.readonly #identifyAll{display:none!important}
body.readonly .tile,body.readonly #editor input,body.readonly #editor select{pointer-events:none}
@media(max-width:900px){main{grid-template-columns:1fr}}
@media(max-width:600px){header{padding:12px 14px;gap:10px}main,.page{padding:20px 14px}.panel{padding:18px;border-radius:24px;margin-bottom:24px}#status{flex-basis:100%;text-align:left;order:9}.tabs{flex-wrap:wrap;border-radius:26px}.tabs button{padding:9px 13px;white-space:nowrap}.item{flex-wrap:wrap;gap:8px}.item .lb{flex-basis:50%}.item input{width:60px}.item .hint{display:none}}
@media (prefers-reduced-motion:reduce){*{transition:none!important}}
</style>
</head>
<body>
<header>
  <div class="brand"><svg viewBox="0 0 100 100" aria-hidden="true"><path d="M71.13 10.27A45 45 0 0 1 28.87 89.73M17.63 81.26A45 45 0 0 1 17.63 18.74" fill="none" stroke-width="6" stroke-linecap="round" stroke="currentColor"/><path d="M28.87 10.27A45 45 0 0 1 57.81 5.68" fill="none" stroke-width="6" stroke-linecap="round" style="stroke:var(--glow,#ff7a2e)"/><g fill="currentColor"><circle cx="43.8" cy="19" r="1.9"/><circle cx="50" cy="19" r="1.9"/><circle cx="56.2" cy="19" r="1.9"/><circle cx="31.4" cy="25.2" r="1.9"/><circle cx="43.8" cy="25.2" r="1.9"/><circle cx="50" cy="25.2" r="1.9"/><circle cx="56.2" cy="25.2" r="1.9"/><circle cx="62.4" cy="25.2" r="1.9"/><circle cx="68.6" cy="25.2" r="1.9"/><circle cx="25.2" cy="31.4" r="1.9"/><circle cx="31.4" cy="31.4" r="1.9"/><circle cx="56.2" cy="31.4" r="1.9"/><circle cx="62.4" cy="31.4" r="1.9"/><circle cx="68.6" cy="31.4" r="1.9"/><circle cx="74.8" cy="31.4" r="1.9"/><circle cx="25.2" cy="37.6" r="1.9"/><circle cx="31.4" cy="37.6" r="1.9"/><circle cx="68.6" cy="37.6" r="1.9"/><circle cx="74.8" cy="37.6" r="1.9"/><circle cx="19" cy="43.8" r="1.9"/><circle cx="25.2" cy="43.8" r="1.9"/><circle cx="31.4" cy="43.8" r="1.9"/><circle cx="74.8" cy="43.8" r="1.9"/><circle cx="81" cy="43.8" r="1.9"/><circle cx="19" cy="50" r="1.9"/><circle cx="25.2" cy="50" r="1.9"/><circle cx="31.4" cy="50" r="1.9"/><circle cx="81" cy="50" r="1.9"/><circle cx="19" cy="56.2" r="1.9"/><circle cx="25.2" cy="56.2" r="1.9"/><circle cx="31.4" cy="56.2" r="1.9"/><circle cx="74.8" cy="56.2" r="1.9"/><circle cx="81" cy="56.2" r="1.9"/><circle cx="25.2" cy="62.4" r="1.9"/><circle cx="31.4" cy="62.4" r="1.9"/><circle cx="68.6" cy="62.4" r="1.9"/><circle cx="74.8" cy="62.4" r="1.9"/><circle cx="25.2" cy="68.6" r="1.9"/><circle cx="31.4" cy="68.6" r="1.9"/><circle cx="56.2" cy="68.6" r="1.9"/><circle cx="62.4" cy="68.6" r="1.9"/><circle cx="68.6" cy="68.6" r="1.9"/><circle cx="74.8" cy="68.6" r="1.9"/><circle cx="31.4" cy="74.8" r="1.9"/><circle cx="43.8" cy="74.8" r="1.9"/><circle cx="50" cy="74.8" r="1.9"/><circle cx="56.2" cy="74.8" r="1.9"/><circle cx="62.4" cy="74.8" r="1.9"/><circle cx="68.6" cy="74.8" r="1.9"/><circle cx="43.8" cy="81" r="1.9"/><circle cx="50" cy="81" r="1.9"/><circle cx="56.2" cy="81" r="1.9"/></g><path d="M39 31L39 69L71 50Z" fill="currentColor" stroke="currentColor" stroke-width="6" stroke-linejoin="round"/></svg>SCREEN CAST</div>
  <nav class="tabs" aria-label="Sections">
    <button id="navScreens" class="on">Screens</button>
    <button id="navUsers" class="adminOnly">Users</button>
    <button id="navActivity" class="adminOnly">Activity</button>
    <button id="changePw">My password</button>
  </nav>
  <div id="status" role="status"></div>
  <span id="who"></span>
  <button id="theme" class="icon" type="button"></button>
  <button id="signOut">Sign out</button>
</header>
<section id="viewUsers" class="page" hidden>
  <div class="panel">
    <div class="phead"><h2>Users</h2></div>
    <p class="hint">Admin: everything, including users and the activity log. Editor: upload files and publish to the screens ticked for them. Viewer: can look, cannot change anything.</p>
    <div id="userList"></div>
  </div>
  <div class="panel">
    <div class="phead"><h2>Add a user</h2></div>
    <div class="row">
      <input id="nuName" placeholder="Username" maxlength="32" autocomplete="off" aria-label="Username">
      <input id="nuPass" type="password" placeholder="Temporary password" maxlength="200" autocomplete="new-password" aria-label="Temporary password">
      <select id="nuRole" aria-label="Level"><option value="editor">Editor</option><option value="viewer">Viewer</option><option value="admin">Admin</option></select>
      <button id="nuAdd" class="primary">Add user</button>
    </div>
    <p class="hint">Give them the temporary password yourself. They must replace it with their own the first time they sign in.</p>
  </div>
</section>
<section id="viewActivity" class="page" hidden>
  <div class="panel">
    <div class="phead">
      <h2>Activity</h2>
      <div class="row"><select id="actUser" aria-label="Show activity for"></select><button id="actRefresh">Refresh</button></div>
    </div>
    <div id="actList"></div>
  </div>
</section>
<section id="viewPassword" class="page" hidden>
  <div class="panel" style="max-width:420px">
    <div class="phead"><h2>My password</h2></div>
    <p class="hint" id="pwNote"></p>
    <label class="field"><span>Current password</span><input id="pwCur" type="password" autocomplete="current-password"></label>
    <label class="field"><span>New password</span><input id="pwNew" type="password" autocomplete="new-password"></label>
    <label class="field"><span>New password again</span><input id="pwRep" type="password" autocomplete="new-password"></label>
    <div class="row"><button id="pwSave" class="primary">Save password</button><button id="pwCancel">Cancel</button></div>
  </div>
</section>
<main id="viewScreens">
  <div>
    <div class="panel">
      <div class="phead"><h2>Screens</h2><span class="badge" id="count"></span></div>
      <div class="lcd" id="screens"></div>
      <div class="legend">
        <span><i class="led live"></i><span><b>Live</b> (green): the TV is showing your content</span></span>
        <span><i class="led connected"></i><span><b>Connected</b> (yellow): TV page is open, nothing showing yet</span></span>
        <span><i class="led"></i><span><b>Offline</b> (grey): TV page is not open</span></span>
      </div>
      <div class="row" style="margin-top:16px"><button id="identifyAll" title="Show each TV's name on its screen for 20 seconds">Identify all TVs</button><button id="addScreen" class="adminOnly">+ Add screen</button></div>
    </div>
    <div class="panel hint">
      <div class="phead"><h2>Set up a TV</h2><span class="badge" id="pairBadge"></span></div>
      On each TV, open the browser and go to<br><span class="url" id="pickUrl"></span><br><span id="pairHelp"></span>
      <div class="row" style="margin-top:14px"><button id="pairToggle" class="adminOnly"></button></div>
    </div>
  </div>
  <div>
    <div class="panel" id="editor"></div>
    <div class="panel" id="drop">
      <div class="phead">
        <h2>Media library</h2>
        <label class="btn">Upload files<input id="file" type="file" multiple accept=".jpg,.jpeg,.png,.gif,.webp,.mp4,.m4v,.webm,.pdf,.pptx,.ppt,.xlsx,.xls" hidden></label>
      </div>
      <p class="hint">Click a file to add it to the selected screen's playlist. You can also drag files onto this box. MP4 (H.264) is the safest video format for TVs.</p>
      <p class="hint" id="docHint"></p>
      <div class="grid" id="library"></div>
    </div>
  </div>
</main>
<script>
(function () {
  var S = { screens: [], media: [], status: {}, showing: {} };
  var sel = null, draft = null, dirty = false, lastMedia = '';
  var me = { username: '', role: 'viewer' }, forced = false, actEntries = [];
  var LEVELS = { admin: 'Admin', editor: 'Editor', viewer: 'Viewer' };

  // ---- light / dark: light unless the person has chosen dark with the sun/moon button
  function theme() {
    var t = document.documentElement.getAttribute('data-theme');
    if (t) return t;
    return 'light';
  }
  function paintTheme() {
    var b = document.getElementById('theme'), dark = theme() === 'dark';
    b.textContent = dark ? '☀' : '☾';
    b.title = dark ? 'Switch to light mode' : 'Switch to dark mode';
    b.setAttribute('aria-label', b.title);
  }
  try {
    var savedTheme = localStorage.getItem('tvb_look');
    if (savedTheme === 'dark' || savedTheme === 'light') document.documentElement.setAttribute('data-theme', savedTheme);
  } catch (e) {}
  document.getElementById('theme').addEventListener('click', function () {
    var next = theme() === 'dark' ? 'light' : 'dark';
    document.documentElement.setAttribute('data-theme', next);
    try { localStorage.setItem('tvb_look', next); } catch (e) {}
    paintTheme();
  });
  paintTheme();

  function $(id) { return document.getElementById(id); }

  function h(tag, attrs, kids) {
    var el = document.createElement(tag);
    Object.keys(attrs || {}).forEach(function (k) {
      var v = attrs[k];
      if (k === 'class') el.className = v;
      else if (k === 'text') el.textContent = v;
      else if (k.slice(0, 2) === 'on') el.addEventListener(k.slice(2), v);
      else if (v === true) el.setAttribute(k, '');
      else if (v !== false && v != null) el.setAttribute(k, v);
    });
    (kids || []).forEach(function (c) {
      if (c) el.appendChild(typeof c === 'string' ? document.createTextNode(c) : c);
    });
    return el;
  }

  function say(msg, isError) {
    $('status').textContent = msg || '';
    $('status').className = isError ? 'err' : '';
  }

  // Questions are asked inside the page. The browser's own confirm() and prompt() boxes can
  // be switched off for a page, and some browsers block them outright; every button that
  // waited on one (Delete screen among them) then did nothing at all.
  // Gives true or false, or with o.input the typed text (null when cancelled).
  function ask(o) {
    return new Promise(function (resolve) {
      var back, last = document.activeElement;
      var field = o.input ? h('input', { type: o.secret ? 'password' : 'text', maxlength: 200, autocomplete: o.secret ? 'new-password' : 'off', placeholder: o.input, 'aria-label': o.input }) : null;
      function done(v) {
        document.removeEventListener('keydown', key, true);
        document.body.removeChild(back);
        if (last && last.focus && document.body.contains(last)) last.focus();
        resolve(v);
      }
      function yes() { done(field ? field.value : true); }
      function no() { done(field ? null : false); }
      function key(ev) {
        if (ev.key === 'Escape') { ev.preventDefault(); no(); }
        else if (ev.key === 'Enter' && ev.target === field) { ev.preventDefault(); yes(); }
        else if (ev.key === 'Tab') { // keep the keyboard inside the question
          var stops = back.querySelectorAll('input,button');
          var at = Array.prototype.indexOf.call(stops, document.activeElement);
          ev.preventDefault();
          stops[(Math.max(at, 0) + (ev.shiftKey ? stops.length - 1 : 1)) % stops.length].focus();
        }
      }
      var ok = h('button', { class: o.danger ? 'go' : 'primary', text: o.ok || 'OK', onclick: yes });
      var cancel = h('button', { text: 'Cancel', onclick: no });
      back = h('div', { class: 'modal', role: 'dialog', 'aria-modal': 'true', 'aria-label': o.text,
        onmousedown: function (ev) { if (ev.target === back) no(); } }, [
        h('div', { class: 'panel' }, [h('p', { text: o.text }), field, h('div', { class: 'row' }, [cancel, ok])])
      ]);
      document.body.appendChild(back);
      document.addEventListener('keydown', key, true);
      (field || (o.danger ? cancel : ok)).focus(); // a slip of the Enter key never deletes anything
    });
  }

  // Unpublished edits are also kept in this browser, so a reload, an expired sign-in or a
  // server restart does not throw them away.
  var stashed = false, loaded = false, pairingShown = null;

  function stashKey() { return 'tvb_draft_' + me.username; }

  function stashDraft() {
    stashed = false;
    try {
      if (dirty && draft) {
        localStorage.setItem(stashKey(), JSON.stringify({ id: sel, version: draft.version, items: draft.items }));
        stashed = true;
      } else {
        localStorage.removeItem(stashKey());
      }
    } catch (e) {}
  }

  function readStash() {
    try { return JSON.parse(localStorage.getItem(stashKey()) || 'null'); } catch (e) { return null; }
  }

  function restoreDraft(d) {
    var s = S.screens.filter(function (x) { return x.id === d.id; })[0];
    if (!s || me.role === 'viewer' || !Array.isArray(d.items)) return;
    if (s.version !== d.version) {
      say('Your unpublished changes to ' + s.name + ' were not brought back: that screen has been published again since.', true);
      return;
    }
    var names = S.media.map(function (m) { return m.name; });
    pick(s.id, true);
    draft.items = d.items.filter(function (it) { // a file may have been deleted in the meantime
      return it && (it.type === 'web' || it.type === 'text' || /^https?:/i.test(it.src) || names.indexOf(it.src) >= 0);
    });
    touch();
    renderEditor();
    say('Your unpublished changes to ' + s.name + ' are still here. Publish them, or pick another screen to discard them.');
  }

  // The server signs people out after a long time without activity. This page refreshes
  // itself every 3 seconds, which must not count, so a request only says "someone is
  // here" when the page has really been touched since the last one.
  var touched = true;
  ['mousemove', 'mousedown', 'keydown', 'touchstart', 'wheel'].forEach(function (ev) {
    document.addEventListener(ev, function () { touched = true; }, true);
  });

  function api(method, url, body) {
    var opts = { method: method, headers: { 'X-TVBoard': '1' } };
    if (touched) { opts.headers['X-TVBoard-Active'] = '1'; touched = false; }
    if (body !== undefined) {
      opts.headers['Content-Type'] = 'application/json';
      opts.body = JSON.stringify(body);
    }
    return fetch(url, opts).then(function (r) {
      return r.json().catch(function () { return {}; }).then(function (j) {
        // unpublished changes stay in this browser and come back after signing in again
        if (r.status === 401) { dirty = false; location.href = j.idle ? '/login?idle=1' : '/login'; }
        if (!r.ok) throw new Error(j.error || ('Request failed (' + r.status + ')'));
        return j;
      });
    });
  }

  function apply(d) {
    S = d;
    me = d.me || me;
    var saved = null;
    if (!loaded) { loaded = true; saved = readStash(); } // read before the first pick() clears it
    document.body.className = (me.role === 'admin' ? 'admin' : '') + (me.role === 'viewer' ? ' readonly' : '');
    $('who').textContent = me.username + ' · ' + (LEVELS[me.role] || me.role);
    if (me.mustChange && !forced) {
      forced = true;
      show('password');
    }
    if (sel && !S.screens.some(function (s) { return s.id === sel; })) { sel = null; draft = null; dirty = false; }
    if (!sel && S.screens[0]) pick(S.screens[0].id, true);
    $('pickUrl').textContent = tvBase() + '/tv';
    $('pairBadge').textContent = S.pairing ? 'Pairing on' : 'Pairing off';
    $('pairBadge').className = 'badge' + (S.pairing ? '' : ' warn');
    $('pairHelp').textContent = S.pairing
      ? 'It shows a 6-digit code. Select the screen here, press "Pair a TV" and type the code, then bookmark the page the TV lands on. Only paired TVs can load what is on the screens.'
      : 'then choose which TV it is. Bookmark the page it lands on. TV pairing is off: anyone on this network can open these pages and see what is on the screens.';
    $('pairToggle').textContent = S.pairing ? 'Turn off TV pairing' : 'Turn on TV pairing';
    if (pairingShown !== null && pairingShown !== !!S.pairing) renderEditor(); // its buttons depend on it
    pairingShown = !!S.pairing;
    var dc = S.docs || {};
    $('docHint').textContent = dc.office
      ? 'PDF, PowerPoint and Excel files are turned into one picture per page or slide. Animations and embedded videos are not kept.'
      : dc.pdf
        ? 'PDF files are turned into one picture per page. PowerPoint and Excel need LibreOffice installed on the server.'
        : 'PDF, PowerPoint and Excel uploads are switched off until "npm install mupdf" has been run on the server.';
    renderScreens();
    paintState();
    var sig = JSON.stringify(S.media);
    if (sig !== lastMedia) { lastMedia = sig; renderLibrary(); }
    if (saved) restoreDraft(saved);
  }

  function refresh() {
    return api('GET', '/api/state').then(apply).catch(function (e) { say('Cannot reach the server: ' + e.message, true); });
  }

  function current() {
    return S.screens.filter(function (s) { return s.id === sel; })[0];
  }

  function tvBase() { return S.tvBase || location.origin; }

  function pick(id, force) {
    if (!force && dirty && id !== sel) {
      ask({ text: 'Discard the unpublished changes on "' + draft.name + '"?', ok: 'Discard changes', danger: true })
        .then(function (yes) { if (yes) { say(''); pick(id, true); } });
      return;
    }
    if (!S.screens.some(function (s) { return s.id === id; })) return; // deleted while the question was open
    sel = id;
    draft = JSON.parse(JSON.stringify(current()));
    dirty = false;
    stashDraft();
    renderScreens();
    renderEditor();
  }

  function touch() {
    dirty = true;
    stashDraft();
    var b = $('publish');
    if (b) { b.disabled = false; b.textContent = 'Publish to TV'; }
    renderScreens();
    paintState();
  }

  var STATUS = { live: 'Live', connected: 'Connected', offline: 'Offline' };

  function statusOf(s) { return S.status[s.id] || 'offline'; }

  function statusLine(s) {
    var st = statusOf(s);
    if (st === 'live') {
      var i = S.showing[s.id], it = s.items[i];
      return 'Showing ' + (i + 1) + ' of ' + s.items.length + (it ? ': ' + (it.src || it.text) : '');
    }
    if (st === 'connected') return s.items.length ? 'Loading the playlist' : 'Nothing published to it yet';
    return 'TV page is not open';
  }

  function removeScreen(s) {
    ask({
      text: 'Delete "' + s.name + '"? Its playlist goes with it, and a TV that is showing it will say "Unknown TV" until it is pointed at another screen.',
      ok: 'Delete screen', danger: true
    }).then(function (yes) {
      if (!yes) return;
      api('DELETE', '/api/screens/' + encodeURIComponent(s.id)).then(function (d) {
        if (s.id === sel) { sel = null; draft = null; dirty = false; stashDraft(); }
        apply(d);
        renderEditor();
        say('Deleted ' + s.name + '.');
      }).catch(function (e) { say(e.message, true); });
    });
  }

  var rows = {}; // screen id -> { el, sig }: the row on the page and what it was drawn from

  function screenRow(s, st, edited) {
    return h('div', { class: 'screen' + (s.id === sel ? ' sel' : ''), tabindex: 0, role: 'button',
      onclick: function () { pick(s.id); },
      onkeydown: function (ev) {
        if (ev.target === ev.currentTarget && (ev.key === 'Enter' || ev.key === ' ')) { ev.preventDefault(); pick(s.id); }
      } }, [
      h('i', { class: 'led ' + st }),
      h('div', { class: 'who' }, [
        h('div', { class: 'nm' }, [s.name, edited ? h('span', { class: 'edited', text: 'EDITED' }) : null]),
        h('div', { class: 'sub', text: statusLine(s) })
      ]),
      h('span', { class: 'st ' + st, text: STATUS[st] }),
      h('button', { class: 'small rm adminOnly', text: '✕', title: 'Delete ' + s.name, 'aria-label': 'Delete ' + s.name,
        onclick: function (ev) { ev.stopPropagation(); removeScreen(s); } })
    ]);
  }

  // Only the rows that changed are redrawn. Rebuilding the whole list on every 3-second
  // refresh dropped keyboard focus and could swallow a click that was in progress.
  function renderScreens() {
    var box = $('screens');
    var tally = { live: 0, connected: 0, offline: 0 };
    var keep = {};
    var none = $('noScreens');
    if (none) box.removeChild(none);
    S.screens.forEach(function (s, n) {
      var st = statusOf(s);
      tally[st]++;
      var edited = s.id === sel && dirty;
      var sig = JSON.stringify([s.name, st, statusLine(s), s.id === sel, edited]);
      var r = rows[s.id];
      if (!r || r.sig !== sig) {
        var el = screenRow(s, st, edited);
        var focus = r && r.el.contains(document.activeElement) ? (document.activeElement === r.el ? el : el.lastChild) : null;
        if (r && r.el.parentNode === box) box.replaceChild(el, r.el);
        r = rows[s.id] = { el: el, sig: sig };
        if (focus) focus.focus();
      }
      if (box.children[n] !== r.el) box.insertBefore(r.el, box.children[n] || null);
      keep[s.id] = true;
    });
    Object.keys(rows).forEach(function (id) {
      if (keep[id]) return;
      if (rows[id].el.parentNode === box) box.removeChild(rows[id].el);
      delete rows[id];
    });
    if (!S.screens.length) box.appendChild(h('div', { id: 'noScreens', class: 'screen sub', text: 'No screens yet.' }));
    $('count').textContent = tally.live + ' live · ' + tally.connected + ' connected · ' + tally.offline + ' offline';
  }

  // the chip beside the screen name: unpublished edits win, otherwise what the TV is doing
  function paintState() {
    var el = $('state'), s = current();
    if (!el || !s) return;
    var st = dirty ? 'dirty' : statusOf(s);
    el.className = 'state ' + st;
    el.textContent = '';
    el.appendChild(h('i', { class: 'led ' + st }));
    el.appendChild(document.createTextNode(
      dirty ? 'Unpublished changes'
        : st === 'live' ? 'Live on the TV'
          : st === 'connected' ? (s.items.length ? 'TV connected, loading' : 'TV connected, nothing to show')
            : (s.items.length ? 'Published, TV is offline' : 'TV is offline')));
  }

  function label(it) {
    if (it.type === 'text') return it.text;
    return it.src;
  }

  function move(i, by) {
    var j = i + by;
    if (j < 0 || j >= draft.items.length) return;
    var t = draft.items[i];
    draft.items[i] = draft.items[j];
    draft.items[j] = t;
    touch();
    renderEditor();
  }

  function itemRow(it, i) {
    var isLib = (it.type === 'image' || it.type === 'video') && !/^https?:/i.test(it.src);
    var thumb = it.type === 'image' && isLib
      ? h('img', { class: 'th', src: '/media/' + encodeURIComponent(it.src), alt: '' })
      : h('div', { class: 'th', text: it.type });
    var secs = h('input', {
      type: 'number', min: it.type === 'video' ? 0 : 3, value: it.duration,
      title: it.type === 'video' ? 'Seconds to play. 0 plays the whole video.' : 'Seconds on screen',
      onchange: function () { it.duration = Number(secs.value) || 0; touch(); }
    });
    var fit = null;
    if (it.type === 'image' || it.type === 'video') {
      fit = h('select', { title: 'Fit shows the whole picture. Fill covers the screen and may crop.', onchange: function () { it.fit = fit.value; touch(); } }, [
        h('option', { value: 'contain', text: 'Fit', selected: it.fit !== 'cover' }),
        h('option', { value: 'cover', text: 'Fill', selected: it.fit === 'cover' })
      ]);
    }
    return h('div', { class: 'item' }, [
      h('span', { class: 'no', text: (i < 9 ? '0' : '') + (i + 1) }),
      thumb,
      h('span', { class: 'lb', text: label(it), title: label(it) }),
      fit, secs, h('span', { class: 'hint', text: 'sec' }),
      h('button', { class: 'small', text: '↑', title: 'Move up', onclick: function () { move(i, -1); } }),
      h('button', { class: 'small', text: '↓', title: 'Move down', onclick: function () { move(i, 1); } }),
      h('button', { class: 'small danger', text: '✕', title: 'Remove', onclick: function () { draft.items.splice(i, 1); touch(); renderEditor(); } })
    ]);
  }

  function publish() {
    var id = sel;
    api('PUT', '/api/screens/' + encodeURIComponent(id), { items: draft.items }).then(function (d) {
      dirty = false;
      apply(d);
      pick(id, true);
      say('Published. The screen turns green when the TV confirms it is showing the new playlist.');
    }).catch(function (e) { say(e.message, true); });
  }

  function copyToAll() {
    ask({ text: 'Replace the playlist on every screen with this one?', ok: 'Copy to all screens' }).then(function (yes) {
      if (!yes) return;
      var id = sel, items = draft.items;
      var chain = Promise.resolve();
      S.screens.forEach(function (s) {
        chain = chain.then(function () {
          return api('PUT', '/api/screens/' + encodeURIComponent(s.id), { items: items });
        });
      });
      chain.then(function (d) {
        dirty = false;
        if (d) apply(d);
        pick(id, true);
        say('Playlist copied to all ' + S.screens.length + ' screens.');
      }).catch(function (e) { say(e.message, true); refresh(); });
    });
  }

  function renderEditor() {
    var box = $('editor');
    box.textContent = '';
    if (!draft) { box.appendChild(h('div', { class: 'hint', text: me.role === 'admin' ? 'Add a screen to get started.' : 'No screens have been assigned to you yet. Ask an admin.' })); return; }
    var id = sel;
    // A new name is saved as soon as the box is left or Enter is pressed. It does not wait
    // for "Publish to TV", and it does not make the TV start its playlist again.
    var name = h('input', { value: draft.name, maxlength: 60, 'aria-label': 'Screen name', readonly: me.role !== 'admin',
      title: me.role === 'admin' ? 'Type a new name and press Enter' : 'Only an admin can rename a screen',
      onkeydown: function (ev) { if (ev.key === 'Enter') name.blur(); },
      onchange: function () {
        var v = name.value.trim();
        if (!v || v === draft.name) { name.value = draft.name; return; }
        api('PUT', '/api/screens/' + encodeURIComponent(id), { name: v }).then(function (d) {
          if (sel === id && draft) draft.name = v;
          apply(d);
          say('Renamed to ' + v + '.');
        }).catch(function (e) { if (draft) name.value = draft.name; say(e.message, true); });
      } });
    var pub = h('button', { id: 'publish', class: 'primary', text: dirty ? 'Publish to TV' : 'Published', disabled: !dirty, onclick: publish });
    box.appendChild(h('div', { class: 'phead' }, [
      h('div', { class: 'row' }, [name, h('span', { class: 'url', text: tvBase() + '/tv/' + id })]),
      h('span', { id: 'state', class: 'state' })
    ]));
    box.appendChild(h('div', { class: 'row spread' }, [
      h('h2', { text: 'Playlist', style: 'margin:0' }),
      h('div', { class: 'row' }, [
        h('button', { text: 'Identify', title: 'Show this TV’s name on its screen for 20 seconds', onclick: function () {
          api('POST', '/api/screens/' + encodeURIComponent(id) + '/identify').then(function () { say('Name is showing on that TV for 20 seconds.'); }).catch(function (e) { say(e.message, true); });
        } }),
        h('button', { text: 'Reload TV', title: 'Make this TV reload its page', onclick: function () {
          api('POST', '/api/screens/' + encodeURIComponent(id) + '/reload').then(function () { say('Reload sent.'); }).catch(function (e) { say(e.message, true); });
        } }),
        S.pairing ? h('button', { text: 'Pair a TV', title: 'Put this screen on a TV by typing the code the TV is showing', onclick: function () {
          var nm = draft.name;
          ask({ text: 'Type the 6-digit code the TV is showing to put "' + nm + '" on it.', input: 'Code on the TV', ok: 'Pair' }).then(function (code) {
            if (!code) return;
            api('POST', '/api/screens/' + encodeURIComponent(id) + '/pair', { code: code })
              .then(function () { say('Paired. The TV switches to ' + nm + ' within a few seconds.'); })
              .catch(function (e) { say(e.message, true); });
          });
        } }) : null,
        pub
      ])
    ]));
    box.appendChild(h('div', { style: 'height:14px' }));
    paintState();
    if (!draft.items.length) {
      box.appendChild(h('div', { class: 'empty', text: 'Empty. Click a file in the media library below, or add a web page or message.' }));
    } else {
      draft.items.forEach(function (it, i) { box.appendChild(itemRow(it, i)); });
      if (draft.items.length === 1) box.appendChild(h('div', { class: 'hint', text: 'With one item the TV shows it continuously.' }));
    }
    var web = h('input', { type: 'url', placeholder: 'https://example.com/dashboard', 'aria-label': 'Web page address' });
    var txt = h('input', { type: 'text', placeholder: 'Message to show in large text', maxlength: 500, 'aria-label': 'Message' });
    box.appendChild(h('div', { class: 'adders' }, [
      h('div', { class: 'row' }, [web, h('button', { text: 'Add web page', onclick: function () {
        var v = web.value.trim();
        if (!/^https?:\/\/\S+$/i.test(v)) { say('Enter a full address starting with http:// or https://', true); return; }
        draft.items.push({ type: 'web', src: v, duration: 30 }); touch(); renderEditor();
      } })]),
      h('div', { class: 'row', style: 'margin-top:8px' }, [txt, h('button', { text: 'Add message', onclick: function () {
        var v = txt.value.trim();
        if (!v) return;
        draft.items.push({ type: 'text', text: v, duration: 10 }); touch(); renderEditor();
      } })])
    ]));
    box.appendChild(h('div', { class: 'row spread', style: 'margin-top:14px' }, [
      h('button', { text: 'Copy this playlist to all screens', onclick: copyToAll }),
      h('div', { class: 'row' }, [
        S.pairing ? h('button', { class: 'danger adminOnly', text: 'Unpair its TVs', title: 'For a TV that was replaced, moved or lost', onclick: function () {
          var nm = draft.name;
          ask({ text: 'Unpair every TV showing "' + nm + '"? Each of them goes back to showing a code and has to be paired again.', ok: 'Unpair', danger: true }).then(function (yes) {
            if (!yes) return;
            api('POST', '/api/screens/' + encodeURIComponent(id) + '/unpair')
              .then(function () { say('Unpaired. TVs that were showing ' + nm + ' now show a code.'); })
              .catch(function (e) { say(e.message, true); });
          });
        } }) : null,
        h('button', { class: 'danger adminOnly', text: 'Delete screen', onclick: function () { removeScreen({ id: id, name: draft.name }); } })
      ])
    ]));
  }

  function size(n) {
    return n > 1048576 ? (n / 1048576).toFixed(1) + ' MB' : Math.max(1, Math.round(n / 1024)) + ' KB';
  }

  function afterDelete(d, names) {
    apply(d);
    if (draft && !dirty) pick(sel, true);
    else if (draft) {
      draft.items = draft.items.filter(function (it) { return names.indexOf(it.src) < 0; });
      draft.version = current().version; // deleting a file republishes the screens that used it
      stashDraft();
      renderEditor();
    }
  }

  function tile(o) {
    return h('div', { class: 'tile', title: o.title, onclick: function () {
      if (!draft) return;
      o.add();
      touch(); renderEditor();
      say('Added to ' + draft.name + '. Publish to send it to the TV.');
    } }, [
      o.pic,
      h('span', { class: 'tag', text: o.tag }),
      o.canDelete && h('button', { class: 'small danger del', text: '\u2715', title: 'Delete', onclick: function (ev) {
        ev.stopPropagation();
        ask({ text: o.confirm, ok: 'Delete', danger: true }).then(function (yes) {
          if (!yes) return;
          api('DELETE', o.deleteUrl).then(function (d) { afterDelete(d, o.names); }).catch(function (e) { say(e.message, true); });
        });
      } }),
      h('div', { class: 'cap' }, [o.caption, h('span', { class: 'sz', text: '  ' + o.sub })])
    ]);
  }

  function renderLibrary() {
    var box = $('library');
    box.textContent = '';
    var docs = {}, order = [];
    S.media.forEach(function (m) {
      if (!m.doc) { order.push({ file: m }); return; }
      if (!docs[m.doc]) { docs[m.doc] = []; order.push({ doc: m.doc }); }
      docs[m.doc].push(m);
    });
    order.forEach(function (entry) {
      if (entry.doc) {
        var pages = docs[entry.doc].slice().sort(function (a, b) { return a.page - b.page; });
        var names = pages.map(function (p) { return p.name; });
        box.appendChild(tile({
          title: 'Add every page to the playlist',
          pic: h('img', { src: '/media/' + encodeURIComponent(names[0]), alt: '', loading: 'lazy' }),
          tag: pages.length + (pages.length === 1 ? ' page' : ' pages'),
          caption: entry.doc, sub: 'document', names: names, canDelete: me.role === 'admin' || pages[0].owner === me.username,
          confirm: 'Delete ' + entry.doc + ' (' + pages.length + ' pages)? It is removed from every playlist too.',
          deleteUrl: '/api/docs/' + encodeURIComponent(entry.doc),
          add: function () { names.forEach(function (n) { draft.items.push({ type: 'image', src: n, fit: 'contain', duration: 15 }); }); }
        }));
        return;
      }
      var m = entry.file;
      var src = '/media/' + encodeURIComponent(m.name);
      box.appendChild(tile({
        title: 'Add to playlist',
        pic: m.kind === 'video' ? h('video', { src: src, preload: 'metadata', muted: true }) : h('img', { src: src, alt: '', loading: 'lazy' }),
        tag: m.kind, caption: m.name, sub: size(m.size), names: [m.name], canDelete: me.role === 'admin' || m.owner === me.username,
        confirm: 'Delete ' + m.name + '? It is removed from every playlist too.',
        deleteUrl: '/api/media/' + encodeURIComponent(m.name),
        add: function () { draft.items.push({ type: m.kind, src: m.name, fit: 'contain', duration: m.kind === 'video' ? 0 : 10 }); }
      }));
    });
    if (!S.media.length) box.appendChild(h('div', { class: 'hint', text: 'Nothing uploaded yet.' }));
  }

  function uploadFiles(list) {
    var files = Array.prototype.slice.call(list);
    if (!files.length) return;
    var chain = Promise.resolve(), done = 0, failed = [];
    files.forEach(function (f) {
      chain = chain.then(function () {
        say('Uploading ' + (done + 1) + ' of ' + files.length + ': ' + f.name + (/\.(pdf|pptx?|xlsx?)$/i.test(f.name) ? ' (converting pages, this can take a minute)' : ''));
        return fetch('/api/upload?name=' + encodeURIComponent(f.name), { method: 'POST', headers: { 'X-TVBoard': '1' }, body: f })
          .then(function (r) { return r.json().catch(function () { return {}; }).then(function (j) { if (!r.ok) throw new Error(j.error || 'failed'); }); })
          .catch(function (e) { failed.push(f.name + ' (' + e.message + ')'); })
          .then(function () { done++; });
      });
    });
    chain.then(function () {
      if (failed.length) say('Could not upload: ' + failed.join(', '), true);
      else say('Uploaded ' + files.length + (files.length === 1 ? ' file.' : ' files.'));
      return api('GET', '/api/state').then(apply);
    });
  }

  $('file').addEventListener('change', function () { uploadFiles(this.files); this.value = ''; });
  var drop = $('drop');
  drop.addEventListener('dragover', function (e) { e.preventDefault(); drop.classList.add('over'); });
  drop.addEventListener('dragleave', function () { drop.classList.remove('over'); });
  drop.addEventListener('drop', function (e) { e.preventDefault(); drop.classList.remove('over'); uploadFiles(e.dataTransfer.files); });

  $('addScreen').addEventListener('click', function () {
    api('POST', '/api/screens', {}).then(function (d) {
      apply(d);
      if (!dirty) pick(S.screens[S.screens.length - 1].id, true);
    }).catch(function (e) { say(e.message, true); });
  });
  $('identifyAll').addEventListener('click', function () {
    api('POST', '/api/screens/identify-all').then(function () { say('Every connected TV is showing its name for 20 seconds.'); }).catch(function (e) { say(e.message, true); });
  });
  $('pairToggle').addEventListener('click', function () {
    var on = !S.pairing;
    var connected = S.screens.filter(function (s) { return statusOf(s) !== 'offline'; }).length;
    ask({
      text: on
        ? 'Turn on TV pairing? From then on only paired TVs can load the screens. TVs that are connected right now keep working: they are paired automatically (' +
          (connected ? connected + (connected === 1 ? ' screen has' : ' screens have') + ' a TV connected' : 'none is connected at the moment') +
          '). Any other TV shows a code that has to be typed in here.'
        : 'Turn off TV pairing? Anyone on this network will be able to open the TV pages and see what is on the screens.',
      ok: on ? 'Turn on pairing' : 'Turn off pairing', danger: !on
    }).then(function (yes) {
      if (!yes) return;
      api('PUT', '/api/settings', { pairing: on }).then(function (d) {
        apply(d);
        say(on ? 'TV pairing is on. Connected TVs are being paired now; any other TV shows a code.' : 'TV pairing is off.');
      }).catch(function (e) { say(e.message, true); });
    });
  });
  // ---- pages: screens / users / activity / change password

  function show(name) {
    if (forced) name = 'password';
    ['Screens', 'Users', 'Activity', 'Password'].forEach(function (v) { $('view' + v).hidden = v.toLowerCase() !== name; });
    var tabs = { screens: 'navScreens', users: 'navUsers', activity: 'navActivity', password: 'changePw' };
    Object.keys(tabs).forEach(function (k) { $(tabs[k]).className = $(tabs[k]).className.replace(/ ?\bon\b/, '') + (k === name ? ' on' : ''); });
    if (name === 'users') loadUsers();
    if (name === 'activity') loadActivity();
    if (name === 'password') {
      $('pwNote').textContent = forced
        ? 'Welcome. Choose your own password before you start (at least ' + (S.minPassword || 12) + ' characters).'
        : 'At least ' + (S.minPassword || 12) + ' characters. Your other devices are signed out when you change it.';
      $('pwCancel').hidden = forced;
      $('pwCur').value = $('pwNew').value = $('pwRep').value = '';
    }
  }

  function fail(e) { say(e.message, true); }

  function loadUsers() { api('GET', '/api/users').then(function (d) { renderUsers(d.users); }).catch(fail); }

  function saveUser(username, change, done) {
    api('PUT', '/api/users/' + encodeURIComponent(username), change)
      .then(function (d) { renderUsers(d.users); say(done); })
      .catch(function (e) { fail(e); loadUsers(); });
  }

  function when(iso) { return iso ? new Date(iso).toLocaleString() : 'never'; }

  function renderUsers(list) {
    var box = $('userList');
    box.textContent = '';
    var table = h('table', {}, [h('tr', {}, ['User', 'Level', 'Screens they can use', 'Last sign-in', ''].map(function (t) { return h('th', { text: t }); }))]);
    list.forEach(function (u) {
      var self = u.username === me.username;
      var level = h('select', { disabled: self, 'aria-label': 'Level for ' + u.username, onchange: function () {
        saveUser(u.username, { role: level.value }, u.username + ' is now ' + LEVELS[level.value] + '.');
      } }, Object.keys(LEVELS).map(function (k) { return h('option', { value: k, text: LEVELS[k], selected: u.role === k }); }));
      var access;
      if (u.role === 'admin') {
        access = h('span', { class: 'hint', text: 'All screens' });
      } else {
        var boxes = [h('label', { class: 'chk' }, [h('input', { type: 'checkbox', checked: !u.screens, onchange: function () {
          saveUser(u.username, { screens: this.checked ? null : [] }, 'Updated ' + u.username + '.');
        } }), 'All screens'])];
        if (u.screens) S.screens.forEach(function (s) {
          boxes.push(h('label', { class: 'chk' }, [h('input', { type: 'checkbox', checked: u.screens.indexOf(s.id) >= 0, onchange: function () {
            var next = u.screens.filter(function (x) { return x !== s.id; });
            if (this.checked) next.push(s.id);
            saveUser(u.username, { screens: next }, 'Updated ' + u.username + '.');
          } }), s.name]));
        });
        access = h('div', {}, boxes);
      }
      var status = u.disabled ? 'Disabled' : (u.mustChange ? 'Has not set their own password yet' : '');
      var actions = self ? h('span', { class: 'hint', text: 'This is you' }) : h('div', { class: 'row' }, [
        h('button', { class: 'small', text: 'Reset password', onclick: function () {
          ask({
            text: 'Temporary password for ' + u.username + ' (at least ' + (S.minPassword || 12) + ' characters). They must change it when they sign in.',
            input: 'Temporary password', secret: true, ok: 'Reset password'
          }).then(function (p) {
            if (p) saveUser(u.username, { password: p }, 'Password reset for ' + u.username + '. They are signed out everywhere.');
          });
        } }),
        h('button', { class: 'small', text: u.disabled ? 'Enable' : 'Disable', onclick: function () {
          saveUser(u.username, { disabled: !u.disabled }, u.username + (u.disabled ? ' can sign in again.' : ' is disabled and signed out.'));
        } }),
        h('button', { class: 'small danger', text: 'Delete', onclick: function () {
          ask({ text: 'Delete the account "' + u.username + '"? Their past activity stays in the log.', ok: 'Delete account', danger: true }).then(function (yes) {
            if (!yes) return;
            api('DELETE', '/api/users/' + encodeURIComponent(u.username)).then(function (d) { renderUsers(d.users); say('Deleted ' + u.username + '.'); }).catch(fail);
          });
        } })
      ]);
      table.appendChild(h('tr', {}, [
        h('td', {}, [h('strong', { text: u.username }), status ? h('div', { class: 'hint', text: status }) : null]),
        h('td', {}, [level]), h('td', {}, [access]), h('td', { text: when(u.lastLogin) }), h('td', {}, [actions])
      ]));
    });
    box.appendChild(table);
  }

  $('nuAdd').addEventListener('click', function () {
    api('POST', '/api/users', { username: $('nuName').value, password: $('nuPass').value, role: $('nuRole').value, screens: null }).then(function (d) {
      say('Added ' + $('nuName').value.trim().toLowerCase() + '. Tick the screens they may use.');
      $('nuName').value = $('nuPass').value = '';
      renderUsers(d.users);
    }).catch(fail);
  });

  var ACTIONS = {
    'login.ok': 'Signed in', 'login.fail': 'Failed sign-in', 'login.locked': 'Sign-in blocked (locked out)', 'logout': 'Signed out',
    'screen.publish': 'Published playlist', 'screen.add': 'Added screen', 'screen.delete': 'Deleted screen', 'screen.rename': 'Renamed screen',
    'media.upload': 'Uploaded file', 'media.delete': 'Deleted file', 'document.upload': 'Uploaded document', 'document.delete': 'Deleted document',
    'password.set': 'Password set from the server console', 'password.change': 'Changed own password',
    'cert.make': 'HTTPS certificate made from the server console',
    'user.add': 'Added user', 'user.update': 'Changed user', 'user.delete': 'Deleted user',
    'screen.pair': 'Paired a TV', 'screen.unpair': 'Unpaired TVs', 'pairing.on': 'Turned on TV pairing', 'pairing.off': 'Turned off TV pairing',
    'session.idle': 'Signed out after inactivity'
  };

  function describe(e) {
    var d = e.detail || {};
    if (e.action === 'screen.publish') return d.name + ': ' + ((d.items || []).join(', ') || 'emptied');
    if (e.action === 'user.update') return d.username + ' (' + ((d.changes || []).join('; ') || 'no change') + ')';
    return Object.keys(d).map(function (k) { return k + ': ' + d[k]; }).join(', ');
  }

  function actor(e) {
    if (e.user) return e.user;
    if (e.ip === '-') return 'server console';
    return e.detail && e.detail.username ? e.detail.username + ' (not signed in)' : 'not signed in';
  }

  function loadActivity() {
    api('GET', '/api/audit?limit=500').then(function (d) {
      actEntries = d.entries;
      var pick = $('actUser'), keep = pick.value, names = {};
      actEntries.forEach(function (e) { if (e.user) names[e.user] = 1; });
      pick.textContent = '';
      pick.appendChild(h('option', { value: '', text: 'Everyone' }));
      Object.keys(names).sort().forEach(function (n) { pick.appendChild(h('option', { value: n, text: n, selected: n === keep })); });
      renderActivity();
    }).catch(fail);
  }

  function renderActivity() {
    var box = $('actList'), who = $('actUser').value;
    box.textContent = '';
    var rows = actEntries.filter(function (e) { return !who || e.user === who; });
    if (!rows.length) { box.appendChild(h('div', { class: 'hint', text: 'Nothing recorded yet.' })); return; }
    var table = h('table', {}, [h('tr', {}, ['When', 'Who', 'What', 'Details', 'From address'].map(function (t) { return h('th', { text: t }); }))]);
    rows.forEach(function (e) {
      table.appendChild(h('tr', {}, [
        h('td', { text: when(e.time), style: 'white-space:nowrap' }), h('td', { text: actor(e) }),
        h('td', { text: ACTIONS[e.action] || e.action }), h('td', { text: describe(e), style: 'word-break:break-word' }), h('td', { text: e.ip })
      ]));
    });
    box.appendChild(table);
    box.appendChild(h('p', { class: 'hint', text: 'Showing the latest ' + rows.length + ' entries. The full history is in audit.log on the server.' }));
  }

  $('actUser').addEventListener('change', renderActivity);
  $('actRefresh').addEventListener('click', loadActivity);
  $('navScreens').addEventListener('click', function () { show('screens'); });
  $('navUsers').addEventListener('click', function () { show('users'); });
  $('navActivity').addEventListener('click', function () { show('activity'); });
  $('changePw').addEventListener('click', function () { show('password'); });
  $('pwCancel').addEventListener('click', function () { show('screens'); });
  $('pwSave').addEventListener('click', function () {
    if ($('pwNew').value !== $('pwRep').value) { say('The two new passwords do not match.', true); return; }
    api('POST', '/api/password', { current: $('pwCur').value, next: $('pwNew').value }).then(function () {
      forced = false;
      say('Password changed.');
      show('screens');
      return refresh();
    }).catch(fail);
  });

  $('signOut').addEventListener('click', function () {
    function go() {
      dirty = false;
      stashDraft();
      api('POST', '/api/logout').then(function () { location.href = '/login'; }).catch(function (e) { say(e.message, true); });
    }
    if (!dirty) { go(); return; }
    ask({ text: 'Sign out and discard the unpublished changes?', ok: 'Sign out', danger: true }).then(function (yes) { if (yes) go(); });
  });
  // only warn about leaving when the unpublished changes could not be kept in this browser
  window.addEventListener('beforeunload', function (e) { if (dirty && !stashed) { e.preventDefault(); e.returnValue = ''; } });

  $('pickUrl').textContent = tvBase() + '/tv';
  refresh().then(renderEditor);
  setInterval(refresh, 3000);
})();
</script>
</body>
</html>`;

// ---------------------------------------------------------------- sign-in page

const LOGIN_HTML = String.raw`<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Screen Cast - Sign in</title>
<link rel="icon" type="image/svg+xml" href="data:image/svg+xml,%3Csvg%20xmlns%3D%22http%3A%2F%2Fwww.w3.org%2F2000%2Fsvg%22%20viewBox%3D%220%200%20100%20100%22%3E%3Cdefs%3E%3CradialGradient%20id%3D%22g%22%20cx%3D%22.3%22%20cy%3D%22.25%22%20r%3D%22.9%22%3E%3Cstop%20offset%3D%220%22%20stop-color%3D%22%233a3e46%22%2F%3E%3Cstop%20offset%3D%221%22%20stop-color%3D%22%2316181c%22%2F%3E%3C%2FradialGradient%3E%3C%2Fdefs%3E%3Crect%20width%3D%22100%22%20height%3D%22100%22%20rx%3D%2224%22%20fill%3D%22url(%23g)%22%2F%3E%3Cg%20transform%3D%22translate(9%209)%20scale(.82)%22%3E%3Cpath%20d%3D%22M71.13%2010.27A45%2045%200%200%201%2028.87%2089.73M17.63%2081.26A45%2045%200%200%201%2017.63%2018.74%22%20fill%3D%22none%22%20stroke-width%3D%228%22%20stroke-linecap%3D%22round%22%20stroke%3D%22%23eef0f3%22%2F%3E%3Cpath%20d%3D%22M28.87%2010.27A45%2045%200%200%201%2057.81%205.68%22%20fill%3D%22none%22%20stroke-width%3D%228%22%20stroke-linecap%3D%22round%22%20stroke%3D%22%23ff7a2e%22%2F%3E%3Cg%20fill%3D%22%23eef0f3%22%3E%3Ccircle%20cx%3D%2233%22%20cy%3D%2224.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2250%22%20cy%3D%2224.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2258.5%22%20cy%3D%2224.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2267%22%20cy%3D%2224.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2224.5%22%20cy%3D%2233%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2258.5%22%20cy%3D%2233%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2267%22%20cy%3D%2233%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2275.5%22%20cy%3D%2233%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2224.5%22%20cy%3D%2241.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2275.5%22%20cy%3D%2241.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2224.5%22%20cy%3D%2250%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2224.5%22%20cy%3D%2258.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2275.5%22%20cy%3D%2258.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2224.5%22%20cy%3D%2267%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2258.5%22%20cy%3D%2267%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2267%22%20cy%3D%2267%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2275.5%22%20cy%3D%2267%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2233%22%20cy%3D%2275.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2250%22%20cy%3D%2275.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2258.5%22%20cy%3D%2275.5%22%20r%3D%222.6%22%2F%3E%3Ccircle%20cx%3D%2267%22%20cy%3D%2275.5%22%20r%3D%222.6%22%2F%3E%3C%2Fg%3E%3Cpath%20d%3D%22M39%2031L39%2069L71%2050Z%22%20fill%3D%22%23eef0f3%22%20stroke%3D%22%23eef0f3%22%20stroke-width%3D%228%22%20stroke-linejoin%3D%22round%22%2F%3E%3C%2Fg%3E%3C%2Fsvg%3E">
<style>
@font-face{font-family:"Unbounded";src:url(/fonts/unbounded-v1.woff2) format("woff2");font-weight:200 900;font-style:normal;font-display:swap}
@font-face{font-family:"Jost";src:url(/fonts/jost-v1.woff2) format("woff2");font-weight:100 900;font-style:normal;font-display:swap}
:root{color-scheme:light;--bg:#e6e7eb;--text:#24272c;--mute:#5a5f68;--hi:rgba(255,255,255,.95);--lo:rgba(163,169,184,.74);--accent:#b03f08;--bad:#b52a38;--sans:"Jost","Century Gothic","Avenir Next",Avenir,Futura,"URW Gothic","Segoe UI Variable Text","Segoe UI",system-ui,-apple-system,Roboto,sans-serif;--wide:"Unbounded","Century Gothic","Avenir Next",Avenir,Futura,"Segoe UI",system-ui,sans-serif;--up:8px 8px 18px var(--lo),-8px -8px 18px var(--hi);--up2:4px 4px 10px var(--lo),-4px -4px 10px var(--hi);--up1:2px 2px 5px var(--lo),-2px -2px 5px var(--hi);--in:inset 5px 5px 11px var(--lo),inset -5px -5px 11px var(--hi);--in2:inset 3px 3px 6px var(--lo),inset -3px -3px 6px var(--hi)}
:root[data-theme=dark]{color-scheme:dark;--bg:#282b31;--text:#e9ebef;--mute:#a3a9b3;--hi:rgba(255,255,255,.07);--lo:rgba(0,0,0,.55);--accent:#ff8a45;--bad:#ff7b7b}
*{box-sizing:border-box}
body{margin:0;min-height:100vh;display:flex;align-items:center;justify-content:center;background:var(--bg);color:var(--text);font:16px/1.5 var(--sans)}
form{width:380px;max-width:calc(100vw - 32px);border-radius:34px;padding:28px;box-shadow:var(--up)}
h1 svg{display:block;width:76px;height:76px;margin:0 auto 18px}
h1{margin:0 0 26px;font:600 16px/1 var(--wide);letter-spacing:.2em;text-align:center;color:var(--text);border-radius:22px;padding:26px 10px;box-shadow:var(--in)}
label{display:block;font:600 11px/1.2 var(--sans);letter-spacing:.16em;text-transform:uppercase;color:var(--mute);margin:0 0 9px 6px}
input{width:100%;font:inherit;color:var(--text);background:var(--bg);border:0;border-radius:16px;padding:13px 16px;box-shadow:var(--in2)}
input:focus{outline:2px solid var(--accent);outline-offset:1px}
button{font:600 12px/1.2 var(--sans);letter-spacing:.16em;text-transform:uppercase;color:var(--text);background:var(--bg);border:0;border-radius:999px;cursor:pointer;box-shadow:var(--up2);transition:box-shadow .15s}
button:hover{box-shadow:var(--up1)}
button:active{box-shadow:var(--in2)}
input:focus-visible,button:focus-visible{outline:2px solid var(--accent);outline-offset:3px}
#go{width:100%;margin-top:26px;padding:16px;color:var(--accent)}
#go:disabled{opacity:.55}
#theme{position:fixed;top:18px;right:18px;width:42px;height:42px;font-size:17px;line-height:42px;padding:0}
#msg{min-height:20px;margin-top:16px;font-size:14px;color:var(--bad);text-align:center;font-weight:600}
@media (prefers-reduced-motion:reduce){*{transition:none!important}}
</style>
</head>
<body>
<button id="theme" type="button"></button>
<form id="f">
  <h1><svg viewBox="0 0 100 100" aria-hidden="true"><path d="M71.13 10.27A45 45 0 0 1 28.87 89.73M17.63 81.26A45 45 0 0 1 17.63 18.74" fill="none" stroke-width="6" stroke-linecap="round" stroke="currentColor"/><path d="M28.87 10.27A45 45 0 0 1 57.81 5.68" fill="none" stroke-width="6" stroke-linecap="round" style="stroke:var(--glow,#ff7a2e)"/><g fill="currentColor"><circle cx="43.8" cy="19" r="1.9"/><circle cx="50" cy="19" r="1.9"/><circle cx="56.2" cy="19" r="1.9"/><circle cx="31.4" cy="25.2" r="1.9"/><circle cx="43.8" cy="25.2" r="1.9"/><circle cx="50" cy="25.2" r="1.9"/><circle cx="56.2" cy="25.2" r="1.9"/><circle cx="62.4" cy="25.2" r="1.9"/><circle cx="68.6" cy="25.2" r="1.9"/><circle cx="25.2" cy="31.4" r="1.9"/><circle cx="31.4" cy="31.4" r="1.9"/><circle cx="56.2" cy="31.4" r="1.9"/><circle cx="62.4" cy="31.4" r="1.9"/><circle cx="68.6" cy="31.4" r="1.9"/><circle cx="74.8" cy="31.4" r="1.9"/><circle cx="25.2" cy="37.6" r="1.9"/><circle cx="31.4" cy="37.6" r="1.9"/><circle cx="68.6" cy="37.6" r="1.9"/><circle cx="74.8" cy="37.6" r="1.9"/><circle cx="19" cy="43.8" r="1.9"/><circle cx="25.2" cy="43.8" r="1.9"/><circle cx="31.4" cy="43.8" r="1.9"/><circle cx="74.8" cy="43.8" r="1.9"/><circle cx="81" cy="43.8" r="1.9"/><circle cx="19" cy="50" r="1.9"/><circle cx="25.2" cy="50" r="1.9"/><circle cx="31.4" cy="50" r="1.9"/><circle cx="81" cy="50" r="1.9"/><circle cx="19" cy="56.2" r="1.9"/><circle cx="25.2" cy="56.2" r="1.9"/><circle cx="31.4" cy="56.2" r="1.9"/><circle cx="74.8" cy="56.2" r="1.9"/><circle cx="81" cy="56.2" r="1.9"/><circle cx="25.2" cy="62.4" r="1.9"/><circle cx="31.4" cy="62.4" r="1.9"/><circle cx="68.6" cy="62.4" r="1.9"/><circle cx="74.8" cy="62.4" r="1.9"/><circle cx="25.2" cy="68.6" r="1.9"/><circle cx="31.4" cy="68.6" r="1.9"/><circle cx="56.2" cy="68.6" r="1.9"/><circle cx="62.4" cy="68.6" r="1.9"/><circle cx="68.6" cy="68.6" r="1.9"/><circle cx="74.8" cy="68.6" r="1.9"/><circle cx="31.4" cy="74.8" r="1.9"/><circle cx="43.8" cy="74.8" r="1.9"/><circle cx="50" cy="74.8" r="1.9"/><circle cx="56.2" cy="74.8" r="1.9"/><circle cx="62.4" cy="74.8" r="1.9"/><circle cx="68.6" cy="74.8" r="1.9"/><circle cx="43.8" cy="81" r="1.9"/><circle cx="50" cy="81" r="1.9"/><circle cx="56.2" cy="81" r="1.9"/></g><path d="M39 31L39 69L71 50Z" fill="currentColor" stroke="currentColor" stroke-width="6" stroke-linejoin="round"/></svg>SCREEN CAST</h1>
  <label for="un">Username</label>
  <input id="un" type="text" autocomplete="username" autocapitalize="none" spellcheck="false" autofocus required>
  <label for="pw" style="margin-top:12px">Password</label>
  <input id="pw" type="password" autocomplete="current-password" required>
  <button id="go" type="submit">Sign in</button>
  <div id="msg" role="alert"></div>
</form>
<script>
(function () {
  var f = document.getElementById('f'), pw = document.getElementById('pw'), un = document.getElementById('un');
  var go = document.getElementById('go'), msg = document.getElementById('msg');

  // ---- light / dark: light unless the person has chosen dark with the sun/moon button
  function theme() {
    var t = document.documentElement.getAttribute('data-theme');
    if (t) return t;
    return 'light';
  }
  function paintTheme() {
    var b = document.getElementById('theme'), dark = theme() === 'dark';
    b.textContent = dark ? '☀' : '☾';
    b.title = dark ? 'Switch to light mode' : 'Switch to dark mode';
    b.setAttribute('aria-label', b.title);
  }
  try {
    var savedTheme = localStorage.getItem('tvb_look');
    if (savedTheme === 'dark' || savedTheme === 'light') document.documentElement.setAttribute('data-theme', savedTheme);
  } catch (e) {}
  document.getElementById('theme').addEventListener('click', function () {
    var next = theme() === 'dark' ? 'light' : 'dark';
    document.documentElement.setAttribute('data-theme', next);
    try { localStorage.setItem('tvb_look', next); } catch (e) {}
    paintTheme();
  });
  paintTheme();
  if (/[?&]idle=1/.test(location.search)) msg.textContent = 'You were signed out after a long time without activity.';
  f.addEventListener('submit', function (e) {
    e.preventDefault();
    go.disabled = true;
    msg.textContent = '';
    fetch('/api/login', {
      method: 'POST',
      headers: { 'X-TVBoard': '1', 'Content-Type': 'application/json' },
      body: JSON.stringify({ username: un.value, password: pw.value })
    }).then(function (r) {
      return r.json().catch(function () { return {}; }).then(function (j) {
        if (r.ok) { location.href = '/'; return; }
        msg.textContent = j.error || 'Could not sign in';
        go.disabled = false;
        pw.value = '';
        pw.focus();
      });
    }).catch(function () { msg.textContent = 'Cannot reach the server'; go.disabled = false; });
  });
})();
</script>
</body>
</html>`;

const ADMIN_CSP = cspFor(ADMIN_HTML);
const LOGIN_CSP = cspFor(LOGIN_HTML);

// ---------------------------------------------------------------- start

function onRequest(req, res) {
  handle(req, res).catch(function (err) {
    const code = err.statusCode || 500;
    if (code === 500) console.error(err);
    if (res.headersSent) { res.destroy(); return; }
    sendJson(res, code, { error: code === 500 ? 'Server error' : err.message, idle: err.idle || undefined });
    req.resume(); // let a refused upload finish sending, so the browser shows the reason instead of a dropped connection
  });
}

// ---- HTTPS certificate, made here so that nothing has to be installed
// The certificate vouches for this server only (it is not a certificate authority), so a
// device that is told to trust it trusts nothing else because of it.

function der(tag, parts) { // one piece of a certificate: tag, length, contents
  const body = Buffer.isBuffer(parts) ? parts : Buffer.concat(parts);
  const n = body.length;
  const len = n < 128 ? [n] : n < 256 ? [0x81, n] : [0x82, n >> 8, n & 255];
  return Buffer.concat([Buffer.from([tag].concat(len)), body]);
}

function derOid(dotted) {
  const p = dotted.split('.').map(Number);
  const out = [p[0] * 40 + p[1]];
  p.slice(2).forEach(function (n) {
    const chunk = [n & 0x7F];
    for (n = Math.floor(n / 128); n > 0; n = Math.floor(n / 128)) chunk.unshift((n & 0x7F) | 0x80);
    Array.prototype.push.apply(out, chunk);
  });
  return der(0x06, Buffer.from(out));
}

function derTime(d) { // YYMMDDHHMMSSZ
  return der(0x17, Buffer.from(d.toISOString().replace(/[-:T]/g, '').slice(2, 14) + 'Z', 'ascii'));
}

function derExtension(oid, critical, value) {
  return der(0x30, [derOid(oid)].concat(critical ? [Buffer.from([1, 1, 0xFF])] : [], [der(0x04, value)]));
}

function pem(label, bytes) {
  return '-----BEGIN ' + label + '-----\n' + bytes.toString('base64').replace(/(.{64})/g, '$1\n').trim() +
    '\n-----END ' + label + '-----\n';
}

// The names and addresses the control page may be opened by. A browser only accepts the
// certificate for one of these.
function certNames(extra) {
  const names = ['localhost', '127.0.0.1', String(os.hostname() || '').toLowerCase()];
  const nets = os.networkInterfaces();
  Object.keys(nets).forEach(function (k) {
    (nets[k] || []).forEach(function (n) { if (n.family === 'IPv4' && !n.internal) names.push(n.address); });
  });
  if (BIND) names.push(BIND.toLowerCase());
  (extra || []).forEach(function (n) { names.push(String(n).trim().toLowerCase()); });
  const dns = /^[a-z0-9]([a-z0-9-]{0,61}[a-z0-9])?(\.[a-z0-9]([a-z0-9-]{0,61}[a-z0-9])?)*$/;
  return names.filter(function (n, i) {
    return n && names.indexOf(n) === i && (ipToInt(n) !== null || (dns.test(n) && !/^[\d.]+$/.test(n)));
  });
}

function makeCertificate(names, days) {
  const keys = crypto.generateKeyPairSync('rsa', { modulusLength: 2048 });
  const now = Date.now();
  const from = new Date(now - 24 * 3600 * 1000); // a day back, for clocks that are a little off
  const until = new Date(now + days * 24 * 3600 * 1000);
  const serial = crypto.randomBytes(16);
  serial[0] = (serial[0] & 0x3F) | 0x40; // positive, and no leading zero byte
  const algorithm = der(0x30, [derOid('1.2.840.113549.1.1.11'), Buffer.from([5, 0])]); // RSA with SHA-256
  const name = der(0x30, [der(0x31, [der(0x30, [derOid('2.5.4.3'), der(0x0C, Buffer.from('Screen Cast on ' + (os.hostname() || 'this server'), 'utf8'))])])]);
  const altNames = der(0x30, names.map(function (n) {
    return ipToInt(n) !== null ? der(0x87, Buffer.from(n.split('.').map(Number))) : der(0x82, Buffer.from(n, 'ascii'));
  }));
  const extensions = der(0xA3, [der(0x30, [
    derExtension('2.5.29.19', true, der(0x30, [])),                                 // not a certificate authority
    derExtension('2.5.29.15', true, der(0x03, Buffer.from([5, 0xA0]))),             // for signing and key exchange
    derExtension('2.5.29.37', false, der(0x30, [derOid('1.3.6.1.5.5.7.3.1')])),     // for a web server
    derExtension('2.5.29.17', false, altNames)                                      // the names it is good for
  ])]);
  const body = der(0x30, [
    Buffer.from([0xA0, 3, 2, 1, 2]), der(0x02, serial), algorithm, name,
    der(0x30, [derTime(from), derTime(until)]), name,
    keys.publicKey.export({ type: 'spki', format: 'der' }), extensions
  ]);
  const signature = crypto.sign('sha256', body, keys.privateKey);
  const certPem = pem('CERTIFICATE', der(0x30, [body, algorithm, der(0x03, [Buffer.from([0]), signature])]));
  // read it back the way a browser would, rather than trust the lines above
  const check = new crypto.X509Certificate(certPem);
  if (!check.verify(keys.publicKey) || check.ca) throw new Error('The certificate did not come out right');
  return { cert: certPem, key: keys.privateKey.export({ type: 'pkcs8', format: 'pem' }), until: until, print: check.fingerprint256 };
}

function certInfo() { // what the certificate in use says about itself
  const x = new crypto.X509Certificate(fs.readFileSync(TLS_CERT));
  return {
    until: new Date(x.validTo), print: x.fingerprint256,
    names: String(x.subjectAltName || '').split(',').map(function (s) { return s.trim().replace(/^[^:]*:/, '').toLowerCase(); }).filter(Boolean)
  };
}

function makeCertCli() {
  const names = certNames(process.argv.slice(3));
  const made = makeCertificate(names, CERT_DAYS);
  const replaced = fs.existsSync(path.join(TLS_DIR, 'cert.pem'));
  fs.mkdirSync(TLS_DIR, { recursive: true });
  fs.writeFileSync(path.join(TLS_DIR, 'key.pem'), made.key, { mode: 0o600 });
  fs.writeFileSync(path.join(TLS_DIR, 'cert.pem'), made.cert);
  fs.writeFileSync(path.join(TLS_DIR, 'TVBoard-certificate.crt'), made.cert); // the same thing, named so that Windows opens it
  audit(null, 'cert.make', { names: names.join(', ') });
  console.log((replaced ? 'A new certificate has replaced the old one in ' : 'A certificate is ready in ') + TLS_DIR);
  console.log('  Good for:    ' + names.join(', '));
  console.log('  Runs out on: ' + made.until.toDateString());
  console.log('  Fingerprint: ' + made.print);
  console.log('');
  console.log('Restart the server. The control page is then at https://<one of the names above>:' + HTTPS_PORT + '/');
  console.log('Browsers will warn that they do not know this certificate. It is safe to continue when the');
  console.log('fingerprint the browser shows is the one above. To stop the warning on a Windows PC, open');
  console.log('TVBoard-certificate.crt from that folder and install it under "Trusted Root Certification Authorities".');
  if (replaced) console.log('PCs that were told to trust the old certificate need this new one instead.');
  console.log('key.pem is the secret half: it stays on this machine and is never copied anywhere.');
}

function setPasswordCli() {
  const readline = require('readline');
  const tty = !!process.stdin.isTTY;
  const rl = readline.createInterface({ input: process.stdin, output: process.stdout, terminal: tty });
  let hidden = false;
  if (tty) {
    // do not echo what is typed while a password is being entered
    rl._writeToOutput = function (s) {
      if (!hidden) rl.output.write(s);
      else if (/[\r\n]/.test(s)) rl.output.write('\n');
    };
  }
  const queue = [];
  const waiting = [];
  rl.on('line', function (l) { if (waiting.length) waiting.shift()(l); else queue.push(l); });
  rl.on('close', function () { while (waiting.length) waiting.shift()(null); });
  function ask(question) {
    process.stdout.write(question);
    hidden = true;
    return new Promise(function (resolve) {
      if (queue.length) resolve(queue.shift()); else waiting.push(resolve);
    }).then(function (v) { hidden = false; if (!tty) process.stdout.write('\n'); return v; });
  }
  function stop(message) { console.error(message); process.exit(1); }
  (async function () {
    const name = String(process.argv[3] || 'admin').toLowerCase();
    if (!USERNAME_RE.test(name)) stop('Usernames are 2 to 32 characters: letters, numbers, dot, dash or underscore.');
    const a = await ask('Password for the admin account "' + name + '" (at least ' + MIN_PASSWORD + ' characters): ');
    if (a === null) stop('No password entered.');
    if (a.length < MIN_PASSWORD) stop('Too short. Use at least ' + MIN_PASSWORD + ' characters; a few unrelated words works well.');
    const b = await ask('Type it again: ');
    if (a !== b) stop('The two entries did not match. Nothing was changed.');
    let u = findUser(name);
    if (!u) {
      u = { username: name, screens: null, created: new Date().toISOString() };
      users.push(u);
    }
    setPassword(u, a);
    u.role = 'admin';
    u.disabled = false;
    u.mustChange = false;
    saveUsers();
    audit(null, 'password.set', { username: name });
    console.log('Admin account "' + name + '" is ready. Restart the server if it is running.');
    rl.close();
  })();
}

function start() {
  const addrs = [];
  const nets = os.networkInterfaces();
  Object.keys(nets).forEach(function (k) {
    (nets[k] || []).forEach(function (n) { if (n.family === 'IPv4' && !n.internal) addrs.push(n.address); });
  });
  const host = BIND || addrs[0] || 'localhost';
  let pending = 1;
  function ready() {
    if (--pending) return;
    console.log('Screen Cast is running.');
    console.log('  Control page:  ' + (TLS_ON ? 'https://' + host + ':' + HTTPS_PORT : 'http://' + host + ':' + PORT) + '/');
    console.log('  On each TV:    http://' + host + ':' + PORT + '/tv');
    if (BIND) console.log('  Listening on ' + BIND + ' only (BIND).');
    else if (addrs.length > 1) console.log('  Reachable on every network this machine is on: ' + addrs.join(', ') + '. Set BIND to one of them to listen there only.');
    console.log('  TV pairing:    ' + (state.pairing ? 'on (only paired TVs can load the screens)' : 'off (anyone on the network can open the TV pages; switch it on under "Set up a TV")'));
    console.log('  Data folder:   ' + DATA_DIR);
    console.log('  Loaded:        ' + state.screens.length + ' screens, ' + listMedia().length + ' media files, ' + users.length + ' accounts');
    if (freshState) {
      console.log('  NOTE: no saved screens were found in that folder, so this is a blank start with ' + DEFAULT_SCREENS + ' empty TVs.');
      console.log('        If you had TVs set up before, they are in the tvboard-data folder beside the server.js you ran');
      console.log('        before. Stop now, copy that folder next to this server.js (or set DATA_DIR to it), and start again.');
    }
    if (ADMIN_ALLOW) console.log('  Control page limited to: ' + process.env.ADMIN_ALLOW);
    if (TV_ALLOW) console.log('  TV pages limited to: ' + process.env.TV_ALLOW);
    console.log('  PDF uploads:   ' + (HAS_PDF ? 'on' : 'off (run "npm install mupdf" in this folder)'));
    console.log('  PowerPoint and Excel uploads: ' + (HAS_PDF && SOFFICE ? 'on' : HAS_PDF ? 'off (install LibreOffice)' : 'off'));
    if (!users.length) console.log('  WARNING: no accounts yet, so nobody can sign in. Run: node server.js set-password');
    if (!TLS_ON) console.log('  WARNING: HTTPS is off. The admin password crosses the network unencrypted. Run: node server.js make-cert');
    if (tlsInfo) {
      const left = Math.floor((tlsInfo.until - Date.now()) / 86400000);
      console.log('  HTTPS:         on. Certificate runs out on ' + tlsInfo.until.toDateString() + '. Fingerprint ' + tlsInfo.print);
      if (left < 0) console.log('  WARNING: the HTTPS certificate has run out, so browsers will refuse it. Run: node server.js make-cert');
      else if (left < 30) console.log('  WARNING: the HTTPS certificate runs out in ' + left + ' days. Run: node server.js make-cert');
      const missing = [host].concat(BIND ? [] : addrs).filter(function (a, i, all) {
        return all.indexOf(a) === i && tlsInfo.names.indexOf(a.toLowerCase()) < 0;
      });
      if (missing.length) {
        console.log('  WARNING: the HTTPS certificate was not made for ' + missing.join(', ') + ', so browsers will warn there.');
        console.log('           This machine\'s address has probably changed. Run: node server.js make-cert');
      }
    }
  }
  function listen(server, port) {
    server.on('error', function (e) { // say what is wrong in plain words instead of a stack trace
      if (e.code === 'EADDRINUSE') console.error('Cannot start: port ' + port + ' is already in use. Is Screen Cast already running in another window?');
      else if (e.code === 'EADDRNOTAVAIL') console.error('Cannot start: this machine has no network address "' + BIND + '" (BIND). Its addresses are: ' + (addrs.join(', ') || 'none found'));
      else console.error('Cannot start on port ' + port + ': ' + e.message);
      process.exit(1);
    });
    if (BIND) server.listen(port, BIND, ready); else server.listen(port, ready);
  }
  let tlsInfo = null;
  if (TLS_ON) {
    let secure;
    try {
      secure = https.createServer({ cert: fs.readFileSync(TLS_CERT), key: fs.readFileSync(TLS_KEY) }, onRequest);
      tlsInfo = certInfo();
    } catch (e) {
      // Starting without HTTPS here would quietly put passwords back on the network in
      // the clear, so it stops instead and says how to put it right.
      console.error('Cannot start: the HTTPS certificate could not be used (' + e.message + ').');
      console.error('  Certificate: ' + TLS_CERT);
      console.error('  Key:         ' + TLS_KEY);
      console.error(TLS_MADE
        ? '  Make a new one with: node server.js make-cert    (or remove the tls folder to go back to plain HTTP)'
        : '  Check the TLS_CERT and TLS_KEY settings.');
      process.exit(1);
    }
    pending++;
    listen(secure, HTTPS_PORT);
  }
  listen(http.createServer(onRequest), PORT);
}

// ---------------------------------------------------------------- embedded fonts
// The two fonts of the control page, kept inside this file so that it stays the only file
// to copy. They are the Latin parts of:
//   Unbounded - Copyright 2022 The Unbounded Project Authors (https://github.com/googlefonts/unbounded)
//   Jost      - Copyright 2020 The Jost Project Authors (https://github.com/indestructible-type/Jost)
// Both are licensed under the SIL Open Font License, Version 1.1. The licence, which is at
// https://openfontlicense.org, lets them be used and passed on inside other software like
// this as long as this notice stays with them. The files are exactly as Google Fonts
// serves them; each also carries its copyright line and licence link inside itself.
const FONT_FILES = {
  'unbounded-v1.woff2': `
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
`,
  'jost-v1.woff2': `
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
iLJboZCr0b/LK0+JTTtVWAn5X8x7KkuhVwM=
`
};
const FONTS = {}; // file name -> the bytes to send
Object.keys(FONT_FILES).forEach(function (name) {
  FONTS[name] = Buffer.from(FONT_FILES[name].replace(/\s+/g, ''), 'base64');
});
// ---------------------------------------------------------------- end of embedded fonts

if (require.main === module) {
  if (process.argv[2] === 'set-password') setPasswordCli();
  else if (process.argv[2] === 'make-cert') makeCertCli();
  else if (process.argv[2] === 'render-pdf') renderPdfCli(process.argv[3], process.argv[4]);
  else start();
} else {
  module.exports = { parseAllow: parseAllow, ipAllowed: ipAllowed, looksLike: looksLike };
}
