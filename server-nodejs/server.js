/* Live Monitor — Nowgoal26 style
 * Server Node.js fără dependențe. Sursa datelor: ESPN (scoruri + statistici live).
 * - Sincronizează la fiecare POLL_MS toate ligile cu meciuri în ziua curentă
 * - Calculează probabilități live (Poisson), indice de IMPULS (presiune) per meci
 * - Detectează golurile (impuls -> GOL -> reset)
 */
const http = require('http');
const fs = require('fs');
const path = require('path');

const PORT = 3000;
const POLL_MS = 20000;          // sincronizare scoruri/statistici
const LEAGUES_REFRESH_MS = 180000; // re-descoperă ligile cu meciuri
const HIST_WINDOW_MS = 12 * 60 * 1000; // fereastra pentru presiune (12 min)
const PULSE_THRESHOLD = 55;     // indice de impuls peste care cardul pulsează
const GOAL_FLASH_MS = 90 * 1000;

// Ligi de bază, mereu verificate (pe lângă cele descoperite automat)
const CORE_LEAGUES = [
  'eng.1','eng.2','esp.1','esp.2','ita.1','ita.2','ger.1','ger.2','fra.1','fra.2',
  'ned.1','ned.2','por.1','tur.1','gre.1','sco.1','bel.1','sui.1','aut.1','rou.1',
  'uefa.champions','uefa.europa','uefa.europa.conf','usa.1','mex.1','arg.1','bra.1','bra.2',
  'den.1','nor.1','swe.1','jpn.1','ksa.1','afc.champions'
];

const state = {
  matches: new Map(),     // id -> meci normalizat
  leagues: new Set(CORE_LEAGUES),
  lastSync: null,
  syncOk: false,
  source: 'espn',
  dateOffset: 0,          // 0 = azi (se poate schimba din UI)
};
const history = new Map();  // id -> [{t, minute, stats...}]
const prevProbs = new Map();// id -> probabilități anterioare (pt. trend ▲/▼)
const goalEvents = [];      // {id, team, teamName, score, minute, t}
const alertLog = [];        // monitoare: alerte de impuls {id, t, text, level}

function fetchJson(url, timeoutMs = 12000) {
  return new Promise((resolve, reject) => {
    const ctrl = new AbortController();
    const to = setTimeout(() => ctrl.abort(), timeoutMs);
    fetch(url, { signal: ctrl.signal, headers: { 'User-Agent': 'Mozilla/5.0 LiveMonitor' } })
      .then(r => { if (!r.ok) throw new Error('HTTP ' + r.status); return r.json(); })
      .then(j => { clearTimeout(to); resolve(j); })
      .catch(e => { clearTimeout(to); reject(e); });
  });
}

function yyyymmdd(offsetDays) {
  const d = new Date(Date.now() + offsetDays * 86400000);
  // folosim fusul Europe/Bucharest aproximativ prin UTC+3
  const local = new Date(d.getTime() + 3 * 3600000);
  return local.toISOString().slice(0, 10).replace(/-/g, '');
}

async function discoverLeagues() {
  try {
    const d = await fetchJson('https://site.web.api.espn.com/apis/v2/scoreboard/header?sport=soccer&region=us&lang=en');
    const sp = (d.sports || [])[0];
    if (sp && sp.leagues) {
      for (const l of sp.leagues) if (l.slug) state.leagues.add(l.slug);
    }
  } catch (e) { /* păstrăm lista existentă */ }
}

function num(v) { const n = parseFloat(v); return isNaN(n) ? 0 : n; }

function parseMinute(status) {
  // displayClock: "67'", "90'+4'", "HT", "0'"
  const dc = (status && status.displayClock) || '';
  const m = dc.match(/^(\d+)'/);
  let minute = m ? parseInt(m[1], 10) : 0;
  const extra = dc.match(/\+(\d+)'/);
  if (extra) minute += parseInt(extra[1], 10);
  return minute;
}

function normalizeEvent(ev, leagueName, leagueSlug) {
  const comp = ev.competitions && ev.competitions[0];
  if (!comp) return null;
  const st = ev.status || {};
  const t = (st.type || {});
  const stateStr = t.state === 'in' ? 'live' : t.state === 'post' ? 'finished' : 'scheduled';
  const minute = parseMinute(st);
  const isHT = /HT|Halftime/i.test(t.shortDetail || '') || (t.description === 'Halftime');
  const period = st.period || 0;

  const out = {
    id: String(ev.id), league: leagueName, leagueSlug, state: stateStr,
    minute, period, isHT,
    detail: t.shortDetail || '', startTime: ev.date,
    teams: {}, score: {}, stats: {},
  };
  for (const c of comp.competitors || []) {
    const side = c.homeAway === 'home' ? 'home' : 'away';
    out.teams[side] = c.team ? (c.team.shortDisplayName || c.team.displayName) : '?';
    out.score[side] = parseInt(c.score || '0', 10) || 0;
    const s = {};
    for (const stat of (c.statistics || [])) s[stat.name] = num(stat.displayValue);
    out.stats[side] = {
      shots: s.totalShots || 0,
      onTarget: s.shotsOnTarget || 0,
      corners: s.wonCorners || 0,
      possession: s.possessionPct || 0,
      fouls: s.foulsCommitted || 0,
      yellow: s.yellowCards || 0,
      red: s.redCards || 0,
      saves: s.saves || 0,
    };
  }
  if (!out.teams.home || !out.teams.away) return null;
  return out;
}

/* ---------- model de probabilități (Poisson pe restul meciului) ---------- */
function poissonCdfAtMost(k, lambda) {
  if (k < 0) return 0;
  let sum = 0, term = Math.exp(-lambda);
  for (let i = 0; i <= k; i++) { sum += term; term *= lambda / (i + 1); }
  return Math.min(1, sum);
}
function pct(x) { return Math.round(Math.max(0, Math.min(1, x)) * 100); }

function computeModel(m, pressure) {
  const g = m.score.home + m.score.away;
  const minute = m.state === 'finished' ? 95 : m.state === 'scheduled' ? 0 : Math.min(m.minute, 95);
  const total = 95;
  const remaining = m.state === 'finished' ? 0 : Math.max(0, total - minute);

  // intensitate din statistici: șuturi/minut raportat la medie (~0.26 total)
  const sh = (m.stats.home || {}), sa = (m.stats.away || {});
  const shotsTotal = (sh.shots || 0) + (sa.shots || 0);
  const sotTotal = (sh.onTarget || 0) + (sa.onTarget || 0);
  let intensity = 1;
  if (m.state === 'live' && minute >= 10 && shotsTotal > 0) {
    const spm = shotsTotal / minute;
    const sotpm = sotTotal / minute;
    intensity = Math.pow(spm / 0.26, 0.55) * Math.pow(Math.max(sotpm, 0.01) / 0.09, 0.25);
    intensity = Math.max(0.5, Math.min(2.0, intensity));
  }
  // impulsul curent crește ușor intensitatea pe termen scurt
  const pressBoost = 1 + (pressure.total / 100) * 0.25;
  const lambdaRemain = 2.7 * (remaining / total) * intensity * pressBoost;

  // împărțire acasă/deplasare după forța ofensivă
  const fH = (sh.onTarget || 0) * 2 + (sh.shots || 0) + (sh.corners || 0) * 0.7 + 1.2; // +avantaj teren
  const fA = (sa.onTarget || 0) * 2 + (sa.shots || 0) + (sa.corners || 0) * 0.7 + 0.8;
  const shareH = fH / (fH + fA);
  const lH = lambdaRemain * shareH, lA = lambdaRemain * (1 - shareH);

  const over = {};
  for (const line of [0.5, 1.5, 2.5, 3.5, 4.5]) {
    const need = Math.floor(line) + 1 - g; // goluri suplimentare necesare
    over['o' + String(line).replace('.', '')] = need <= 0 ? 100 : pct(1 - poissonCdfAtMost(need - 1, lambdaRemain));
  }

  // ambele înscriu
  let btts;
  if (m.score.home > 0 && m.score.away > 0) btts = 100;
  else if (m.state === 'finished') btts = 0;
  else {
    const pH = m.score.home > 0 ? 1 : 1 - Math.exp(-lH);
    const pA = m.score.away > 0 ? 1 : 1 - Math.exp(-lA);
    btts = pct(pH * pA);
  }

  // 1 / X / 2 — distribuție Poisson pe golurile rămase
  let p1 = 0, px = 0, p2 = 0;
  const MAX = 7;
  const pois = (l) => { const a = [Math.exp(-l)]; for (let i = 1; i <= MAX; i++) a[i] = a[i-1] * l / i; return a; };
  const ph = pois(lH), pa = pois(lA);
  for (let i = 0; i <= MAX; i++) for (let j = 0; j <= MAX; j++) {
    const p = ph[i] * pa[j];
    const diff = (m.score.home + i) - (m.score.away + j);
    if (diff > 0) p1 += p; else if (diff === 0) px += p; else p2 += p;
  }
  const s = p1 + px + p2;

  return {
    over05: over.o05, over15: over.o15, over25: over.o25, over35: over.o35, over45: over.o45,
    btts, p1: pct(p1 / s), px: pct(px / s), p2: pct(p2 / s),
    lambdaRemain: Math.round(lambdaRemain * 100) / 100,
  };
}

/* ---------- indice de IMPULS (presiune recentă) ---------- */
function computePressure(id, m) {
  const now = Date.now();
  let arr = history.get(id);
  if (!arr) { arr = []; history.set(id, arr); }
  const snap = {
    t: now, minute: m.minute,
    hShots: m.stats.home.shots, hSot: m.stats.home.onTarget, hCor: m.stats.home.corners,
    aShots: m.stats.away.shots, aSot: m.stats.away.onTarget, aCor: m.stats.away.corners,
    hPos: m.stats.home.possession,
  };
  arr.push(snap);
  while (arr.length && now - arr[0].t > HIST_WINDOW_MS) arr.shift();
  if (m.state !== 'live' || arr.length < 2) return { total: 0, home: 0, away: 0 };

  const first = arr[0], last = arr[arr.length - 1];
  const dtMin = Math.max(2, (last.t - first.t) / 60000);
  const dH = { shots: last.hShots - first.hShots, sot: last.hSot - first.hSot, cor: last.hCor - first.hCor };
  const dA = { shots: last.aShots - first.aShots, sot: last.aSot - first.aSot, cor: last.aCor - first.aCor };
  const raw = (d) => (d.sot * 3 + d.shots * 1.2 + d.cor * 1.5) / dtMin; // evenimente ponderate / minut
  const rH = raw(dH), rA = raw(dA);
  // normalizare: ~0.9/min = presiune foarte mare
  const norm = (r) => Math.round(Math.max(0, Math.min(100, (r / 0.9) * 100)));
  const home = norm(rH), away = norm(rA);
  const posSkew = Math.abs((last.hPos || 50) - 50) / 50 * 10;
  const total = Math.min(100, Math.round(Math.max(home, away) * 0.85 + Math.min(home, away) * 0.15 + posSkew));
  return { total, home, away };
}

/* ---------- sincronizare ---------- */
let syncing = false;
async function syncAll() {
  if (syncing) return;
  syncing = true;
  try {
    const dateStr = yyyymmdd(state.dateOffset);
    const slugs = Array.from(state.leagues);
    const results = await Promise.allSettled(
      slugs.map(sl => fetchJson(`https://site.api.espn.com/apis/site/v2/sports/soccer/${sl}/scoreboard?dates=${dateStr}`))
    );
    const seen = new Set();
    let anyOk = false;
    results.forEach((res, i) => {
      if (res.status !== 'fulfilled') return;
      anyOk = true;
      const d = res.value;
      const lname = (d.leagues && d.leagues[0] && (d.leagues[0].name || d.leagues[0].abbreviation)) || slugs[i];
      for (const ev of d.events || []) {
        const m = normalizeEvent(ev, lname, slugs[i]);
        if (!m) continue;
        if (seen.has(m.id)) continue;
        seen.add(m.id);
        const prev = state.matches.get(m.id);
        // detecție gol
        if (prev && (m.score.home > prev.score.home || m.score.away > prev.score.away)) {
          const side = m.score.home > prev.score.home ? 'home' : 'away';
          goalEvents.push({
            id: m.id, team: side, teamName: m.teams[side],
            score: `${m.score.home}-${m.score.away}`, minute: m.minute, t: Date.now(),
          });
          alertLog.unshift({
            id: m.id, t: Date.now(), level: 'goal',
            text: `GOL! ${m.teams.home} ${m.score.home}-${m.score.away} ${m.teams.away} (${m.minute}')`,
          });
        }
        const pressure = computePressure(m.id, m);
        m.pressure = pressure;
        m.pulse = m.state === 'live' && pressure.total >= PULSE_THRESHOLD;
        // alertă nouă de impuls (o singură dată la trecerea pragului)
        if (m.pulse && (!prev || !prev.pulse)) {
          alertLog.unshift({
            id: m.id, t: Date.now(), level: 'pulse',
            text: `Impuls ridicat (${pressure.total}) — ${m.teams.home} ${m.score.home}-${m.score.away} ${m.teams.away} (${m.minute}')`,
          });
        }
        const probs = computeModel(m, pressure);
        const old = prevProbs.get(m.id);
        m.probs = probs;
        m.trend = {};
        if (old) for (const k of ['over15','over25','over35','btts']) m.trend[k] = Math.round((probs[k] - old[k]) * 10) / 10;
        prevProbs.set(m.id, probs);
        // gol recent?
        const ge = goalEvents.filter(g => g.id === m.id && Date.now() - g.t < GOAL_FLASH_MS);
        m.recentGoal = ge.length ? ge[ge.length - 1] : null;
        state.matches.set(m.id, m);
      }
    });
    // curățăm meciurile care nu mai apar (schimbare de zi)
    for (const id of Array.from(state.matches.keys())) {
      if (!seen.has(id)) { state.matches.delete(id); history.delete(id); prevProbs.delete(id); }
    }
    while (alertLog.length > 80) alertLog.pop();
    while (goalEvents.length > 300) goalEvents.shift();
    state.lastSync = new Date().toISOString();
    state.syncOk = anyOk;
  } catch (e) {
    state.syncOk = false;
  } finally {
    syncing = false;
  }
}

/* ---------- HTTP ---------- */
const MIME = { '.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.png': 'image/png', '.svg': 'image/svg+xml' };

const server = http.createServer(async (req, res) => {
  const u = new URL(req.url, 'http://x');
  res.setHeader('Access-Control-Allow-Origin', '*');

  if (u.pathname === '/api/state') {
    const off = parseInt(u.searchParams.get('offset') || '0', 10) || 0;
    if (off !== state.dateOffset) {
      state.dateOffset = off;
      state.matches.clear(); history.clear(); prevProbs.clear();
      await syncAll();
    }
    const matches = Array.from(state.matches.values());
    const order = { live: 0, scheduled: 1, finished: 2 };
    matches.sort((a, b) => (order[a.state] - order[b.state])
      || (b.pressure?.total || 0) - (a.pressure?.total || 0)
      || (b.minute - a.minute));
    const body = JSON.stringify({
      lastSync: state.lastSync, syncOk: state.syncOk, source: state.source,
      dateOffset: state.dateOffset, date: yyyymmdd(state.dateOffset),
      counts: {
        total: matches.length,
        live: matches.filter(m => m.state === 'live').length,
        scheduled: matches.filter(m => m.state === 'scheduled').length,
        finished: matches.filter(m => m.state === 'finished').length,
        alerts: matches.filter(m => m.pulse).length,
      },
      matches,
      alerts: alertLog.slice(0, 40),
      recentGoals: goalEvents.filter(g => Date.now() - g.t < GOAL_FLASH_MS),
    });
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(body);
    return;
  }

  // static
  let p = u.pathname === '/' ? '/index.html' : u.pathname;
  const file = path.join(__dirname, 'public', path.normalize(p).replace(/^(\.\.[\/\\])+/, ''));
  fs.readFile(file, (err, data) => {
    if (err) { res.writeHead(404); res.end('Not found'); return; }
    res.writeHead(200, { 'Content-Type': MIME[path.extname(file)] || 'application/octet-stream' });
    res.end(data);
  });
});

server.listen(PORT, '0.0.0.0', async () => {
  console.log('Live Monitor pornit pe http://0.0.0.0:' + PORT);
  await discoverLeagues();
  await syncAll();
  setInterval(syncAll, POLL_MS);
  setInterval(discoverLeagues, LEAGUES_REFRESH_MS);
});
