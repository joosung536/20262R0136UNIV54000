/* MOST WANTED: NIGHT RUN — no dependencies, no network, one animation loop. */
(() => {
  'use strict';

  const $ = id => document.getElementById(id);
  const canvas = $('game');
  const ctx = canvas.getContext('2d', { alpha: false });
  const mapCanvas = $('minimap');
  const mapCtx = mapCanvas.getContext('2d', { alpha: false });
  const ui = {};
  ['speed', 'gear', 'speed-fill', 'health', 'health-fill', 'nitro', 'nitro-fill', 'time', 'score', 'wanted', 'notice', 'best-score', 'pause-button', 'menu-screen', 'pause-screen', 'over-screen', 'pursuit-label', 'pursuit-detail'].forEach(id => { ui[id] = $(id); });
  const WORLD = 3240, GRID = 540, ROAD = 184, COUNT = 6;
  const HALF_L = 24, HALF_W = 12, STEP = 1 / 120, WANTED_INTERVAL = 25;
  const MAX_SPEED = 360, NITRO_SPEED = 495, SPEED_SCALE = 0.62;
  const clamp = (n, lo, hi) => Math.max(lo, Math.min(hi, n));
  const mix = (a, b, t) => a + (b - a) * t;
  const smooth = (rate, dt) => 1 - Math.exp(-rate * dt);
  const angleDiff = a => Math.atan2(Math.sin(a), Math.cos(a));
  const distance = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);
  const centers = Array.from({ length: COUNT }, (_, i) => GRID * (i + 0.5));
  const formatTime = t => `${String(Math.floor(t / 60)).padStart(2, '0')}:${String(Math.floor(t % 60)).padStart(2, '0')}`;
  const formatScore = n => String(Math.floor(n)).padStart(6, '0');
  const keys = new Set();
  const buildings = [], nodes = [], particles = [], skidMarks = [], bonuses = [], floatTexts = [];
  let cops = [], player, state = 'MENU', elapsed = 0, score = 0, wanted = 1, best = 0;
  let spawnClock = 0, bonusClock = 8, hudClock = 0, mapClock = 0, simClock = 0;
  let width = 1000, height = 650, dpr = 1, accumulator = 0, lastTime = null;
  let shake = 0, flash = 0, noticeTime = 0, closestCop = Infinity, newRecord = false;
  let visualTime = 0, hudCache = Object.create(null);
  const reducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  const camera = { x: 1180, y: 1670, zoom: 0.9 };
  let randomState = 0x7ab194;
  function random() {
    randomState ^= randomState << 13; randomState ^= randomState >>> 17; randomState ^= randomState << 5;
    return (randomState >>> 0) / 4294967296;
  }
  try { best = Math.max(0, Math.floor(Number(localStorage.getItem('night-run-best')) || 0)); } catch (_) { /* Private/file storage may be disabled. */ }
  if (!Number.isFinite(best)) best = 0;
  ui['best-score'].textContent = formatScore(best);

  // Blocks have simple rectangular collision hulls; roof details are decorative.
  const names = ['NIGHT MARKET', 'KINO', 'NOCTURNE', 'MOTOR CO.', 'VOID', 'AFTER HOURS', 'NEON', '24 / 7'];
  for (let row = -1; row < COUNT; row++) {
    for (let col = -1; col < COUNT; col++) {
      const left = col < 0 ? 0 : centers[col] + ROAD / 2 + 18;
      const top = row < 0 ? 0 : centers[row] + ROAD / 2 + 18;
      const right = col + 1 >= COUNT ? WORLD : centers[col + 1] - ROAD / 2 - 18;
      const bottom = row + 1 >= COUNT ? WORLD : centers[row + 1] - ROAD / 2 - 18;
      const id = (row + 1) * 7 + col + 1;
      buildings.push({ x: left, y: top, w: right - left, h: bottom - top, id,
        tone: ['#1a2931', '#1a252e', '#202a32', '#1c2b30'][id % 4],
        neon: ['#35b3b0', '#bc678f', '#c5bc7d', '#6a96b9'][id % 4], name: names[id % names.length] });
    }
  }
  for (let row = 0; row < COUNT; row++) {
    for (let col = 0; col < COUNT; col++) {
      const id = row * COUNT + col;
      nodes.push({ id, x: centers[col], y: centers[row], links: [] });
    }
  }
  nodes.forEach(n => {
    const x = n.id % COUNT, y = Math.floor(n.id / COUNT);
    if (x > 0) n.links.push(n.id - 1);
    if (x < COUNT - 1) n.links.push(n.id + 1);
    if (y > 0) n.links.push(n.id - COUNT);
    if (y < COUNT - 1) n.links.push(n.id + COUNT);
  });

  function makeCar(x, y, angle, police = false, id = 0) {
    return { x, y, angle, vx: 0, vy: 0, steer: 0, grip: 8.5, health: 100, nitro: 100,
      immunity: 0, nitroLock: false, nitroActive: false, drifting: false, police, id,
      route: [], routeClock: 0, stuck: 0, reverse: 0, recoverCooldown: 0, progressClock: 0,
      progressX: x, progressY: y, skidClock: 0, speed: 0 };
  }
  player = makeCar(1350, 1670, -Math.PI / 2);

  // SAT for a rotated vehicle against another hull. The minimum translation
  // vector points from B toward A, so correction and impact use the same normal.
  function hull(car) {
    return { x: car.x, y: car.y, a: car.angle, l: HALF_L, w: HALF_W };
  }
  function boxHull(b) { return { x: b.x + b.w / 2, y: b.y + b.h / 2, a: 0, l: b.w / 2, w: b.h / 2 }; }
  function overlap(a, b) {
    const afx = Math.cos(a.a), afy = Math.sin(a.a), bfx = Math.cos(b.a), bfy = Math.sin(b.a);
    const axes = [[afx, afy], [-afy, afx], [bfx, bfy], [-bfy, bfx]];
    const dx = a.x - b.x, dy = a.y - b.y;
    let depth = Infinity, nx = 0, ny = 0;
    for (const axis of axes) {
      const [ax, ay] = axis;
      const ra = a.l * Math.abs(afx * ax + afy * ay) + a.w * Math.abs(-afy * ax + afx * ay);
      const rb = b.l * Math.abs(bfx * ax + bfy * ay) + b.w * Math.abs(-bfy * ax + bfx * ay);
      const signed = dx * ax + dy * ay;
      const penetration = ra + rb - Math.abs(signed);
      if (penetration <= 0) return null;
      if (penetration < depth) { depth = penetration; nx = ax * (signed >= 0 ? 1 : -1); ny = ay * (signed >= 0 ? 1 : -1); }
    }
    return { depth, nx, ny };
  }
  function pointFree(x, y, margin = 30) {
    return x >= margin && y >= margin && x <= WORLD - margin && y <= WORLD - margin &&
      !buildings.some(b => x > b.x - margin && x < b.x + b.w + margin && y > b.y - margin && y < b.y + b.h + margin);
  }
  // Segment/slab intersection with expanded rectangles, used for route clearance.
  function lineClear(a, b, margin = 32) {
    const dx = b.x - a.x, dy = b.y - a.y;
    for (const block of buildings) {
      let near = 0, far = 1;
      const ranges = [[a.x, dx, block.x - margin, block.x + block.w + margin], [a.y, dy, block.y - margin, block.y + block.h + margin]];
      let hit = true;
      for (const [origin, delta, lo, hi] of ranges) {
        if (Math.abs(delta) < 0.00001) { if (origin < lo || origin > hi) { hit = false; break; } }
        else {
          const t1 = (lo - origin) / delta, t2 = (hi - origin) / delta;
          near = Math.max(near, Math.min(t1, t2)); far = Math.min(far, Math.max(t1, t2));
          if (near > far) { hit = false; break; }
        }
      }
      if (hit) return false;
    }
    return true;
  }
  function damage(amount, x, y) {
    if (player.immunity > 0 || state !== 'PLAYING') return false;
    player.health = Math.max(0, player.health - amount);
    player.immunity = 1.15;
    shake = Math.max(shake, Math.min(9, amount * 0.36)); flash = 0.22;
    spark(x, y, 18, '#ffca77');
    if (player.health <= 0) gameOver();
    return true;
  }
  function wallImpact(car, nx, ny, depth) {
    car.x += nx * (depth + 0.04); car.y += ny * (depth + 0.04);
    const inward = car.vx * nx + car.vy * ny;
    if (inward < 0) {
      car.vx -= inward * nx * 1.16; car.vy -= inward * ny * 1.16;
      car.vx *= 0.86; car.vy *= 0.86;
      if (!car.police && -inward > 95) {
        damage(clamp((-inward - 55) * 0.045, 3, 19), car.x - nx * 20, car.y - ny * 20);
      }
    }
  }
  function resolveWorld(car) {
    // Multiple passes settle a car touching a corner or two independent edges.
    for (let pass = 0; pass < 3; pass++) {
      let collided = false;
      for (const b of buildings) {
        if (car.x < b.x - 36 || car.x > b.x + b.w + 36 || car.y < b.y - 36 || car.y > b.y + b.h + 36) continue;
        const contact = overlap(hull(car), boxHull(b));
        if (contact) { wallImpact(car, contact.nx, contact.ny, contact.depth); collided = true; }
      }
      const ex = Math.abs(Math.cos(car.angle)) * HALF_L + Math.abs(Math.sin(car.angle)) * HALF_W;
      const ey = Math.abs(Math.sin(car.angle)) * HALF_L + Math.abs(Math.cos(car.angle)) * HALF_W;
      if (car.x < ex) { wallImpact(car, 1, 0, ex - car.x); collided = true; }
      if (car.x > WORLD - ex) { wallImpact(car, -1, 0, car.x - (WORLD - ex)); collided = true; }
      if (car.y < ey) { wallImpact(car, 0, 1, ey - car.y); collided = true; }
      if (car.y > WORLD - ey) { wallImpact(car, 0, -1, car.y - (WORLD - ey)); collided = true; }
      if (!collided) break;
    }
  }
  function resolveCars(a, b) {
    if (distance(a, b) > 56) return;
    const c = overlap(hull(a), hull(b));
    if (!c) return;
    const impact = -( (a.vx - b.vx) * c.nx + (a.vy - b.vy) * c.ny );
    a.x += c.nx * (c.depth + 0.1) * 0.5; a.y += c.ny * (c.depth + 0.1) * 0.5;
    b.x -= c.nx * (c.depth + 0.1) * 0.5; b.y -= c.ny * (c.depth + 0.1) * 0.5;
    if (impact > 0) {
      const impulse = impact * 0.62;
      a.vx += c.nx * impulse; a.vy += c.ny * impulse;
      b.vx -= c.nx * impulse; b.vy -= c.ny * impulse;
    }
    if ((!a.police || !b.police) && impact > 12) {
      damage(clamp(7 + impact * 0.061, 8, 29), (a.x + b.x) / 2, (a.y + b.y) / 2);
    }
  }

  // Attach both ends of the current road segment to the intersection graph.
  // Considering both ends avoids nearest-intersection U-turn oscillation.
  function roadAnchors(p) {
    const col = clamp(Math.round((p.x - GRID / 2) / GRID), 0, COUNT - 1);
    const row = clamp(Math.round((p.y - GRID / 2) / GRID), 0, COUNT - 1);
    const dx = Math.abs(p.x - centers[col]), dy = Math.abs(p.y - centers[row]);
    const ids = new Set();
    if (dx <= dy + 35) {
      const r = Math.floor((p.y - GRID / 2) / GRID);
      [r, r + 1].forEach(y => ids.add(clamp(y, 0, COUNT - 1) * COUNT + col));
    }
    if (dy <= dx + 35) {
      const c = Math.floor((p.x - GRID / 2) / GRID);
      [c, c + 1].forEach(x => ids.add(row * COUNT + clamp(x, 0, COUNT - 1)));
    }
    return [...ids].filter(id => lineClear(p, nodes[id], 28));
  }
  function findRoute(from, to) {
    if (lineClear(from, to)) return [{ x: to.x, y: to.y }];
    const starts = roadAnchors(from), ends = roadAnchors(to);
    // A car at the outside edge of a pavement first returns to its road center.
    if (!starts.length || !ends.length) {
      let nearest = null, dist = Infinity;
      for (const n of nodes) { const d = distance(from, n); if (d < dist && lineClear(from, n, 8)) { nearest = n; dist = d; } }
      return nearest ? [nearest] : [];
    }
    const costs = nodes.map(() => Infinity), previous = nodes.map(() => -1), closed = new Set();
    starts.forEach(id => { costs[id] = distance(from, nodes[id]); });
    for (let step = 0; step < nodes.length; step++) {
      let id = -1, cost = Infinity;
      for (let i = 0; i < nodes.length; i++) if (!closed.has(i) && costs[i] < cost) { id = i; cost = costs[i]; }
      if (id === -1) break;
      closed.add(id);
      for (const next of nodes[id].links) if (cost + GRID < costs[next]) { costs[next] = cost + GRID; previous[next] = id; }
    }
    let end = ends[0];
    for (const id of ends) if (costs[id] + distance(nodes[id], to) < costs[end] + distance(nodes[end], to)) end = id;
    const route = [];
    for (let id = end; id !== -1; id = previous[id]) route.unshift(nodes[id]);
    route.push({ x: to.x, y: to.y });
    while (route.length > 1 && lineClear(from, route[1])) route.shift();
    return route;
  }
  function isOffscreen(p, margin = 80) {
    return Math.abs(p.x - camera.x) > width / camera.zoom / 2 + margin || Math.abs(p.y - camera.y) > height / camera.zoom / 2 + margin;
  }
  function spawnCop(id) {
    const candidates = [];
    nodes.forEach(n => {
      candidates.push({ x: n.x, y: n.y });
      if (n.id % COUNT < COUNT - 1) candidates.push({ x: n.x + GRID / 2, y: n.y });
      if (n.id < COUNT * (COUNT - 1)) candidates.push({ x: n.x, y: n.y + GRID / 2 });
    });
    const valid = candidates.filter(p => pointFree(p.x, p.y) && isOffscreen(p, 100) && distance(p, player) > 480 && cops.every(c => distance(c, p) > 140));
    // The arena's bounded CSS width always leaves a road outside the camera.
    if (!valid.length) return null;
    valid.sort((a, b) => Math.abs(distance(a, player) - 790) - Math.abs(distance(b, player) - 790));
    const spot = valid[Math.floor(random() * Math.min(4, valid.length))];
    const route = findRoute(spot, player), target = route[0] || player;
    const car = makeCar(spot.x, spot.y, Math.atan2(target.y - spot.y, target.x - spot.x), true, id);
    car.route = route; car.routeClock = 0.4 + id * 0.03;
    return car;
  }
  function playerInput(dt) {
    const gas = keys.has('KeyW') || keys.has('ArrowUp');
    const brake = keys.has('KeyS') || keys.has('ArrowDown');
    const steer = Number(keys.has('KeyD') || keys.has('ArrowRight')) - Number(keys.has('KeyA') || keys.has('ArrowLeft'));
    const handbrake = keys.has('Space');
    const shift = keys.has('ShiftLeft') || keys.has('ShiftRight');
    let fx = Math.cos(player.angle), fy = Math.sin(player.angle);
    let forward = player.vx * fx + player.vy * fy;
    player.steer = mix(player.steer, steer, smooth(11, dt));
    player.drifting = handbrake && Math.abs(forward) > 65;
    player.grip = mix(player.grip, player.drifting ? 1.65 : 8.5, smooth(player.drifting ? 18 : 4.8, dt));
    const steeringRate = 2.55 * clamp(Math.abs(forward) / 85, 0, 1) * (1 - 0.32 * clamp(Math.abs(forward) / MAX_SPEED, 0, 1));
    player.angle += player.steer * steeringRate * Math.sign(forward) * (player.drifting ? 1.38 : 1) * dt;
    fx = Math.cos(player.angle); fy = Math.sin(player.angle);
    forward = player.vx * fx + player.vy * fy;
    let side = -player.vx * fy + player.vy * fx;
    if (!shift) player.nitroLock = false;
    if (player.nitro <= 0.01) player.nitroLock = true;
    player.nitroActive = shift && gas && !brake && forward > 10 && player.nitro > 0 && !player.nitroLock;
    if (gas && !brake) forward += (forward < -5 ? 470 : player.nitroActive ? 490 : 305) * dt;
    if (brake) forward -= (forward > 5 ? 475 : 185) * dt;
    forward *= Math.exp(-(handbrake ? 0.76 : 0.34) * dt);
    side *= Math.exp(-player.grip * dt);
    forward = clamp(forward, -125, player.nitroActive ? NITRO_SPEED : MAX_SPEED);
    if (!gas && !brake && Math.abs(forward) < 0.9) forward = 0;
    player.vx = fx * forward - fy * side; player.vy = fy * forward + fx * side;
    player.nitro = clamp(player.nitro + (player.nitroActive ? -27 : 12) * dt, 0, 100);
    if (player.drifting && Math.abs(side) > 55) score += Math.abs(side) * 0.065 * dt;
    player.skidClock -= dt;
    if (player.drifting && player.skidClock <= 0) { addSkids(player); player.skidClock = 0.035; }
    player.x += player.vx * dt; player.y += player.vy * dt;
    resolveWorld(player);
    player.speed = Math.hypot(player.vx, player.vy);
  }
  function updateCop(cop, dt) {
    const dist = distance(cop, player);
    cop.routeClock -= dt; cop.recoverCooldown = Math.max(0, cop.recoverCooldown - dt);
    const target = { x: player.x + player.vx * (dist < 400 ? 0.4 : 0.18), y: player.y + player.vy * (dist < 400 ? 0.4 : 0.18) };
    if (!pointFree(target.x, target.y, 30)) { target.x = player.x; target.y = player.y; }
    if (cop.routeClock <= 0) { cop.route = findRoute(cop, target); cop.routeClock = 0.38 + cop.id * 0.035; }
    while (cop.route.length > 1 && (distance(cop, cop.route[0]) < 48 || lineClear(cop, cop.route[1], 38))) cop.route.shift();
    const aim = cop.route[0] || target;
    let ax = aim.x - cop.x, ay = aim.y - cop.y;
    // Small separation changes steering; the SAT solver handles actual contact.
    for (const other of cops) {
      if (other === cop) continue;
      const d = distance(cop, other);
      if (d > 0.1 && d < 100) { ax += (cop.x - other.x) / d * (100 - d) * 1.3; ay += (cop.y - other.y) / d * (100 - d) * 1.3; }
    }
    let error = angleDiff(Math.atan2(ay, ax) - cop.angle);
    cop.progressClock += dt;
    if (cop.progressClock >= 0.8) {
      const moved = Math.hypot(cop.x - cop.progressX, cop.y - cop.progressY);
      cop.stuck = moved < 20 && dist > 65 ? cop.stuck + cop.progressClock : Math.max(0, cop.stuck - 0.65);
      cop.progressX = cop.x; cop.progressY = cop.y; cop.progressClock = 0;
      if (cop.stuck > 1.5 && cop.recoverCooldown <= 0) { cop.reverse = 0.8; cop.recoverCooldown = 2.6; cop.routeClock = 0; }
    }
    let speed = 250 + wanted * 12 + (dist < 470 ? 32 : 0) + cop.id * 3;
    // Brake before a right-angle turn instead of ploughing into the far curb.
    speed *= clamp(1 - Math.abs(error) * 0.65, 0.24, 1);
    if (cop.route.length > 1 && distance(cop, aim) < 155) {
      const next = cop.route[1];
      const turn = Math.abs(angleDiff(Math.atan2(next.y - aim.y, next.x - aim.x) - Math.atan2(ay, ax)));
      if (turn > 0.5) speed = Math.min(speed, 145);
    }
    if (dist < 110 && Math.abs(error) > 0.7) speed = Math.min(speed, 110);
    if (cop.reverse > 0) {
      cop.reverse -= dt; speed = -95;
      error = -Math.sign(error || 1) * 0.8;
    }
    cop.steer = mix(cop.steer, clamp(error * 2.6, -1, 1), smooth(8, dt));
    cop.angle += clamp(error * 3.6, -3.2, 3.2) * dt;
    const fx = Math.cos(cop.angle), fy = Math.sin(cop.angle);
    let forward = cop.vx * fx + cop.vy * fy, side = -cop.vx * fy + cop.vy * fx;
    forward = mix(forward, speed, smooth(speed < forward ? 5.8 : 2.0, dt));
    side *= Math.exp(-7.5 * dt);
    cop.vx = fx * forward - fy * side; cop.vy = fy * forward + fx * side;
    cop.x += cop.vx * dt; cop.y += cop.vy * dt; resolveWorld(cop);
    cop.speed = Math.hypot(cop.vx, cop.vy);
    // An obstructed unit is only reassigned while outside the visible scene.
    if ((cop.stuck > 6 || dist > 1900) && isOffscreen(cop, 130)) {
      const replacement = spawnCop(cop.id);
      if (replacement) Object.assign(cop, replacement);
    }
  }

  function startRun() {
    keys.clear(); randomState = 0x7ab194;
    player = makeCar(1350, 1670, -Math.PI / 2);
    cops = []; particles.length = 0; skidMarks.length = 0; bonuses.length = 0; floatTexts.length = 0;
    elapsed = 0; score = 0; wanted = 1; spawnClock = 0; bonusClock = 8; hudClock = 0; mapClock = 0; simClock = 0;
    shake = 0; flash = 0; noticeTime = 0; closestCop = Infinity; newRecord = false;
    camera.x = player.x; camera.y = player.y; camera.zoom = 0.9;
    accumulator = 0; lastTime = null; hudCache = Object.create(null);
    setState('PLAYING');
    const first = spawnCop(0); if (first) cops.push(first);
    showNotice('추격 시작  /  코너는 SPACE, 탈출은 SHIFT', 3.2);
    updateHUD(); drawMinimap();
    canvas.focus({ preventScroll: true });
  }
  function setState(next) {
    state = next; document.body.dataset.state = state;
    ui['menu-screen'].hidden = state !== 'MENU'; ui['pause-screen'].hidden = state !== 'PAUSED'; ui['over-screen'].hidden = state !== 'GAME_OVER';
    ui['pause-button'].disabled = state !== 'PLAYING' && state !== 'PAUSED';
    ui['pause-button'].setAttribute('aria-label', state === 'PAUSED' ? '게임 재개' : '일시정지');
    ui['pause-button'].firstChild.nodeValue = state === 'PAUSED' ? '▷ ' : 'Ⅱ ';
    keys.clear(); accumulator = 0; lastTime = null;
  }
  function togglePause() {
    if (state === 'PLAYING') { setState('PAUSED'); $('resume-button').focus({ preventScroll: true }); }
    else if (state === 'PAUSED') { setState('PLAYING'); canvas.focus({ preventScroll: true }); }
  }
  function gameOver() {
    if (state !== 'PLAYING') return;
    score = Math.floor(score); newRecord = score > best;
    if (newRecord) { best = score; try { localStorage.setItem('night-run-best', String(best)); } catch (_) { /* The current session still retains its best. */ } }
    setState('GAME_OVER');
    $('final-time').textContent = formatTime(elapsed); $('final-score').textContent = formatScore(score); $('final-best').textContent = formatScore(best);
    $('record-label').textContent = newRecord ? 'NEW PERSONAL BEST' : 'PERSONAL BEST';
    ui['best-score'].textContent = formatScore(best); updateHUD();
    $('restart-button').focus({ preventScroll: true });
  }
  function showNotice(text, duration = 2.4) {
    ui.notice.textContent = text; ui.notice.classList.add('visible'); noticeTime = duration;
  }
  function spawnBonus() {
    if (bonuses.length >= 3) return;
    const options = [];
    for (const n of nodes) {
      const d = distance(n, player);
      if (d > 180 && d < 850 && bonuses.every(b => distance(b, n) > 150)) options.push(n);
    }
    if (!options.length) return;
    const spot = options[Math.floor(random() * options.length)];
    bonuses.push({ x: spot.x, y: spot.y, life: 28 });
  }
  function update(dt) {
    if (state !== 'PLAYING') return;
    elapsed += dt; simClock += dt;
    player.immunity = Math.max(0, player.immunity - dt);
    const level = Math.min(5, 1 + Math.floor(elapsed / WANTED_INTERVAL));
    if (level !== wanted) { wanted = level; showNotice(`WANTED ${'★'.repeat(wanted)}  /  지원 경찰 출동`, 3.1); }
    spawnClock -= dt;
    if (cops.length < wanted && spawnClock <= 0) { const cop = spawnCop(cops.length); if (cop) cops.push(cop); spawnClock = 0.5; }
    playerInput(dt);
    if (state !== 'PLAYING') return;
    for (const cop of cops) updateCop(cop, dt);
    // Two passes also handle a unit pushed against a building by another unit.
    for (let pass = 0; pass < 2; pass++) {
      for (let i = 0; i < cops.length; i++) {
        resolveCars(player, cops[i]);
        for (let j = i + 1; j < cops.length; j++) resolveCars(cops[i], cops[j]);
      }
      resolveWorld(player); cops.forEach(resolveWorld);
    }
    player.speed = Math.hypot(player.vx, player.vy);
    if (state !== 'PLAYING') return;
    score += dt * (10 + player.speed * 0.045);
    bonusClock -= dt;
    if (bonusClock <= 0) { spawnBonus(); bonusClock = 13; }
    for (let i = bonuses.length - 1; i >= 0; i--) {
      const b = bonuses[i]; b.life -= dt;
      if (distance(player, b) < 38) { score += 500; spark(b.x, b.y, 22, '#dcfa76'); floatTexts.push({ x: b.x, y: b.y, text: '+500', life: 1.2 }); bonuses.splice(i, 1); }
      else if (b.life <= 0) bonuses.splice(i, 1);
    }
    closestCop = cops.reduce((d, c) => Math.min(d, distance(c, player)), Infinity);
    camera.zoom = mix(camera.zoom, 0.9 - clamp(player.speed / NITRO_SPEED, 0, 1) * 0.095, smooth(2, dt));
    camera.x = mix(camera.x, player.x + player.vx * 0.2, smooth(5.5, dt));
    camera.y = mix(camera.y, player.y + player.vy * 0.2, smooth(5.5, dt));
    updateEffects(dt);
    hudClock -= dt; mapClock -= dt;
    if (hudClock <= 0) { updateHUD(); hudClock = 0.09; }
    if (mapClock <= 0) { drawMinimap(); mapClock = 0.08; }
    if (noticeTime > 0) { noticeTime -= dt; if (noticeTime <= 0) ui.notice.classList.remove('visible'); }
  }
  function setText(id, text) { if (hudCache[id] !== text) { ui[id].textContent = text; hudCache[id] = text; } }
  function updateHUD() {
    setText('speed', String(Math.round(player.speed * SPEED_SCALE)).padStart(3, '0'));
    const forward = player.vx * Math.cos(player.angle) + player.vy * Math.sin(player.angle);
    setText('gear', player.speed < 3 ? 'N' : forward < -3 ? 'R' : player.nitroActive ? 'N₂' : 'D');
    setText('health', String(Math.ceil(player.health))); setText('nitro', `${Math.round(player.nitro)}%`);
    setText('time', formatTime(elapsed)); setText('score', formatScore(score));
    ui['health-fill'].style.transform = `scaleX(${player.health / 100})`;
    ui['health-fill'].style.background = player.health < 30 ? '#ff6671' : '#d4f85c';
    ui['nitro-fill'].style.transform = `scaleX(${player.nitro / 100})`;
    ui['speed-fill'].style.transform = `scaleX(${clamp(player.speed / NITRO_SPEED, 0, 1)})`;
    if (hudCache.wanted !== wanted) {
      [...ui.wanted.children].forEach((star, i) => star.classList.toggle('active', i < wanted));
      ui.wanted.setAttribute('aria-label', `수배 레벨 ${wanted}`); hudCache.wanted = wanted;
    }
    setText('pursuit-label', closestCop < 210 ? 'HOT PURSUIT / 경찰 근접' : 'NIGHT CITY / SECTOR 07');
    setText('pursuit-detail', Number.isFinite(closestCop) ? `추격 경찰 ${cops.length}대  ·  가장 가까운 경찰 ${Math.round(closestCop * 0.1)}m` : '도시는 잠들지 않는다.');
  }
  function spark(x, y, count, color) {
    for (let i = 0; i < count && particles.length < 180; i++) {
      const a = random() * Math.PI * 2, speed = 40 + random() * 155;
      particles.push({ x, y, vx: Math.cos(a) * speed, vy: Math.sin(a) * speed, life: 0.25 + random() * 0.35, max: 0.6, color });
    }
  }
  function addSkids(car) {
    const fx = Math.cos(car.angle), fy = Math.sin(car.angle);
    for (const sign of [-1, 1]) {
      const x = car.x - fx * 16 - fy * sign * 11, y = car.y - fy * 16 + fx * sign * 11;
      skidMarks.push({ x, y, x2: x - car.vx * 0.045, y2: y - car.vy * 0.045, life: 9 });
    }
    if (skidMarks.length > 420) skidMarks.splice(0, skidMarks.length - 420);
  }
  function updateEffects(dt) {
    shake *= Math.exp(-9 * dt); flash = Math.max(0, flash - dt);
    for (let i = particles.length - 1; i >= 0; i--) {
      const p = particles[i]; p.life -= dt; p.x += p.vx * dt; p.y += p.vy * dt; p.vx *= Math.exp(-3 * dt); p.vy *= Math.exp(-3 * dt);
      if (p.life <= 0 || isOffscreen(p, 150)) particles.splice(i, 1);
    }
    for (let i = skidMarks.length - 1; i >= 0; i--) { const s = skidMarks[i]; s.life -= dt; if (s.life <= 0 || isOffscreen(s, 400)) skidMarks.splice(i, 1); }
    for (let i = floatTexts.length - 1; i >= 0; i--) { floatTexts[i].life -= dt; floatTexts[i].y -= dt * 22; if (floatTexts[i].life <= 0) floatTexts.splice(i, 1); }
  }

  function visible(b, padding = 50) {
    return b.x + b.w + padding > camera.x - width / camera.zoom / 2 && b.x - padding < camera.x + width / camera.zoom / 2 &&
      b.y + b.h + padding > camera.y - height / camera.zoom / 2 && b.y - padding < camera.y + height / camera.zoom / 2;
  }
  function drawCity() {
    ctx.fillStyle = '#0c151b'; ctx.fillRect(0, 0, WORLD, WORLD);
    ctx.fillStyle = '#1a252d';
    for (const c of centers) { ctx.fillRect(c - ROAD / 2, 0, ROAD, WORLD); ctx.fillRect(0, c - ROAD / 2, WORLD, ROAD); }
    ctx.lineWidth = 1; ctx.strokeStyle = '#344149';
    for (const c of centers) {
      for (const s of [-1, 1]) {
        ctx.beginPath(); ctx.moveTo(c + s * (ROAD / 2 - 7), 0); ctx.lineTo(c + s * (ROAD / 2 - 7), WORLD); ctx.stroke();
        ctx.beginPath(); ctx.moveTo(0, c + s * (ROAD / 2 - 7)); ctx.lineTo(WORLD, c + s * (ROAD / 2 - 7)); ctx.stroke();
      }
    }
    // Markings stop before junctions, leaving every crossing easy to read.
    for (let i = 0; i < COUNT; i++) {
      const c = centers[i];
      for (let j = -1; j < COUNT; j++) {
        const lo = j < 0 ? 0 : centers[j] + 115;
        const hi = j + 1 >= COUNT ? WORLD : centers[j + 1] - 115;
        ctx.strokeStyle = '#93895766'; ctx.lineWidth = 1.4; ctx.setLineDash([]);
        for (const offset of [-3, 3]) {
          ctx.beginPath(); ctx.moveTo(c + offset, lo); ctx.lineTo(c + offset, hi); ctx.stroke();
          ctx.beginPath(); ctx.moveTo(lo, c + offset); ctx.lineTo(hi, c + offset); ctx.stroke();
        }
        ctx.strokeStyle = '#a4b4b433'; ctx.lineWidth = 2; ctx.setLineDash([19, 22]);
        for (const offset of [-46, 46]) {
          ctx.beginPath(); ctx.moveTo(c + offset, lo); ctx.lineTo(c + offset, hi); ctx.stroke();
          ctx.beginPath(); ctx.moveTo(lo, c + offset); ctx.lineTo(hi, c + offset); ctx.stroke();
        }
        ctx.setLineDash([]);
      }
    }
    for (const n of nodes) {
      if (!visible({ x: n.x - 130, y: n.y - 130, w: 260, h: 260 })) continue;
      ctx.fillStyle = '#a6b9bb29';
      for (const side of [-1, 1]) for (let k = -3; k <= 3; k++) {
        ctx.fillRect(n.x + k * 21 - 7, n.y + side * 108 - 10, 10, 20);
        ctx.fillRect(n.x + side * 108 - 10, n.y + k * 21 - 7, 20, 10);
      }
      ctx.fillStyle = '#778b8d33';
      ctx.font = '8px Arial'; ctx.textAlign = 'left';
      ctx.fillText(`${String(n.id + 1).padStart(2, '0')} / NIGHT CITY`, n.x - 61, n.y + 69);
      for (const s of [-1, 1]) {
        ctx.fillStyle = '#73c9b926'; ctx.fillRect(n.x + s * 88 - 3, n.y - 88, 6, 6);
        ctx.fillStyle = '#8cd9bd'; ctx.fillRect(n.x + s * 88 - 1, n.y - 86, 2, 2);
      }
    }
    for (const b of buildings) {
      if (!visible(b)) continue;
      const { x, y, w, h } = b;
      ctx.fillStyle = '#28383e'; ctx.fillRect(x - 18, y - 18, w + 36, h + 36);
      ctx.strokeStyle = '#43515988'; ctx.lineWidth = 1; ctx.strokeRect(x - 17, y - 17, w + 34, h + 34);
      ctx.fillStyle = '#050c1270'; ctx.fillRect(x + 9, y + 11, w + 3, h + 3);
      ctx.fillStyle = b.tone; ctx.fillRect(x, y, w, h);
      ctx.strokeStyle = '#53646c55'; ctx.strokeRect(x + 1, y + 1, w - 2, h - 2);
      ctx.fillStyle = '#0d171c88'; ctx.fillRect(x + 13, y + 13, w - 26, h - 26);
      ctx.fillStyle = b.tone; ctx.fillRect(x + 19, y + 19, w - 38, h - 38);
      ctx.fillStyle = '#34434b'; ctx.fillRect(x + 28, y + 30, w * 0.48, h * 0.39);
      ctx.fillStyle = '#25343c'; ctx.fillRect(x + 32, y + 34, w * 0.48 - 8, h * 0.39 - 8);
      ctx.strokeStyle = '#52616833'; ctx.lineWidth = 1;
      for (let k = 1; k < 5; k++) {
        ctx.beginPath(); ctx.moveTo(x + 29, y + 30 + h * 0.39 * k / 5); ctx.lineTo(x + 27 + w * 0.48, y + 30 + h * 0.39 * k / 5); ctx.stroke();
      }
      // Air-conditioning housings and rooftop vents establish scale.
      const rx = x + w * 0.7, ry = y + h * 0.26;
      ctx.fillStyle = '#111c23'; ctx.fillRect(rx - 3, ry - 3, 38, 67);
      ctx.fillStyle = '#35464e'; ctx.fillRect(rx, ry, 31, 59);
      for (let k = 0; k < 2; k++) {
        ctx.fillStyle = '#17252d'; ctx.beginPath(); ctx.arc(rx + 15.5, ry + 15 + k * 28, 10, 0, Math.PI * 2); ctx.fill();
        ctx.strokeStyle = '#506068'; ctx.lineWidth = 2;
        ctx.beginPath(); ctx.moveTo(rx + 9, ry + 9 + k * 28); ctx.lineTo(rx + 22, ry + 21 + k * 28); ctx.moveTo(rx + 9, ry + 21 + k * 28); ctx.lineTo(rx + 22, ry + 9 + k * 28); ctx.stroke();
      }
      ctx.fillStyle = '#31434a'; ctx.fillRect(x + 28, y + h - 53, w - 56, 18);
      ctx.fillStyle = '#d3c49366';
      for (let k = 0; k < Math.floor((w - 70) / 22); k++) if ((b.id + k) % 4 !== 0) ctx.fillRect(x + 36 + k * 22, y + h - 49, 10, 3);
      ctx.save(); ctx.globalAlpha = 0.65; ctx.fillStyle = b.neon;
      ctx.shadowBlur = 13; ctx.shadowColor = b.neon;
      ctx.fillRect(x + 25, y + h - 3, Math.min(105, w - 50), 2);
      ctx.font = 'bold 12px Arial'; ctx.textAlign = 'left'; ctx.fillText(b.name, x + 28, y + h * 0.69);
      ctx.restore();
      ctx.fillStyle = '#687c8355'; ctx.font = '9px Courier New'; ctx.fillText(`BLK. ${String(b.id + 1).padStart(2, '0')}`, x + w - 78, y + h - 19);
      // Lamps sit on the sidewalk; their bodies are part of the solid block.
      for (const lx of [x + 12, x + w - 12]) {
        const light = ctx.createRadialGradient(lx, y - 10, 0, lx, y - 10, 49);
        light.addColorStop(0, '#70cbc91a'); light.addColorStop(1, '#70cbc900');
        ctx.fillStyle = light; ctx.fillRect(lx - 49, y - 59, 98, 98);
        ctx.fillStyle = '#8cb7bb'; ctx.fillRect(lx - 3, y - 13, 6, 2);
      }
    }
    ctx.strokeStyle = '#84a2a4'; ctx.lineWidth = 6; ctx.strokeRect(0, 0, WORLD, WORLD);
  }
  function drawHeadlights(car) {
    ctx.save(); ctx.translate(car.x, car.y); ctx.rotate(car.angle);
    const gradient = ctx.createLinearGradient(21, 0, 185, 0);
    gradient.addColorStop(0, car.police ? '#d0e9ff2c' : '#9bfff42e'); gradient.addColorStop(1, '#b1ecef00');
    ctx.fillStyle = gradient; ctx.beginPath(); ctx.moveTo(22, -9); ctx.lineTo(188, -53); ctx.lineTo(188, 53); ctx.lineTo(22, 9); ctx.closePath(); ctx.fill(); ctx.restore();
  }
  function drawVehicle(car, showcase = false) {
    ctx.save(); ctx.translate(car.x, car.y); ctx.rotate(car.angle);
    ctx.fillStyle = '#0008'; ctx.fillRect(-23 + 4, -12 + 5, 49, 27);
    if (car.police) {
      const blink = Math.sin(visualTime * 17 + car.id) > 0;
      for (const side of [-1, 1]) {
        const color = side < 0 ? (blink ? '#ff3f6370' : '#ff3f6310') : (blink ? '#3485ff10' : '#3485ff70');
        const g = ctx.createRadialGradient(0, side * 12, 0, 0, side * 12, 62);
        g.addColorStop(0, color); g.addColorStop(1, '#00000000'); ctx.fillStyle = g; ctx.fillRect(-64, -76, 128, 152);
      }
    } else if (car.nitroActive) {
      const tail = 24 + Math.sin(visualTime * 70) * 7;
      ctx.shadowColor = '#30dcff'; ctx.shadowBlur = 16;
      for (const s of [-1, 1]) {
        ctx.fillStyle = '#2fc9ffae'; ctx.beginPath(); ctx.moveTo(-22, s * 7 - 3); ctx.lineTo(-25 - tail, s * 7); ctx.lineTo(-22, s * 7 + 3); ctx.fill();
        ctx.fillStyle = '#d6fff8'; ctx.fillRect(-30, s * 7 - 1.3, 8, 2.6);
      }
      ctx.shadowBlur = 0;
    }
    // Four distinct wheels, with visible front-wheel steering.
    for (const x of [-16, 15]) for (const y of [-12, 12]) {
      ctx.save(); ctx.translate(x, y); if (x > 0) ctx.rotate(car.steer * 0.38);
      ctx.fillStyle = '#03080c'; ctx.fillRect(-6, -3, 12, 6); ctx.fillStyle = '#3c4b52'; ctx.fillRect(-3, -1.5, 6, 3); ctx.restore();
    }
    if (!car.police) { ctx.shadowColor = '#22cabc'; ctx.shadowBlur = showcase ? 7 : 10; }
    ctx.fillStyle = car.police ? '#cad7db' : '#35dfcd';
    ctx.beginPath(); ctx.moveTo(-24, -9); ctx.lineTo(-18, -12); ctx.lineTo(14, -12); ctx.lineTo(24, -8); ctx.lineTo(26, -4); ctx.lineTo(26, 4); ctx.lineTo(24, 8); ctx.lineTo(14, 12); ctx.lineTo(-18, 12); ctx.lineTo(-24, 9); ctx.closePath(); ctx.fill();
    ctx.shadowBlur = 0;
    ctx.strokeStyle = car.police ? '#78969e' : '#a2fff1'; ctx.lineWidth = 0.8; ctx.stroke();
    ctx.fillStyle = car.police ? '#18242d' : '#0d6a68'; ctx.fillRect(-23, -8, 5, 16);
    if (car.police) { ctx.fillStyle = '#14202a'; ctx.fillRect(11, -10, 12, 20); ctx.fillRect(-22, -10, 9, 20); }
    else {
      ctx.fillStyle = '#a4fff044'; ctx.fillRect(9, -7, 12, 1.4); ctx.fillRect(9, 5.6, 12, 1.4);
      ctx.fillStyle = '#0eaba1'; ctx.fillRect(-22, -10.5, 3, 21);
    }
    ctx.fillStyle = '#09161e';
    ctx.beginPath(); ctx.moveTo(10, -9.5); ctx.lineTo(4, -8); ctx.lineTo(4, 8); ctx.lineTo(10, 9.5); ctx.lineTo(13, 7.5); ctx.lineTo(13, -7.5); ctx.closePath(); ctx.fill();
    ctx.fillStyle = '#59858e66'; ctx.fillRect(9, -7, 1.5, 14);
    ctx.fillStyle = '#101e26'; ctx.fillRect(-12, -8, 5, 16);
    ctx.fillStyle = car.police ? '#e1ebed' : '#22b8ad'; ctx.fillRect(-6, -8, 10, 16);
    ctx.fillStyle = '#05151d'; ctx.fillRect(-5, -11, 12, 2); ctx.fillRect(-5, 9, 12, 2);
    if (car.police) {
      const blink = Math.sin(visualTime * 17 + car.id) > 0;
      ctx.fillStyle = '#07101b'; ctx.fillRect(-3, -11, 5, 22);
      ctx.shadowBlur = 10; ctx.shadowColor = '#ff365f'; ctx.fillStyle = blink ? '#ff496b' : '#672e43'; ctx.fillRect(-2, -10, 3, 8);
      ctx.shadowColor = '#327aff'; ctx.fillStyle = blink ? '#223b72' : '#4e9dff'; ctx.fillRect(-2, 2, 3, 8); ctx.shadowBlur = 0;
      ctx.fillStyle = '#233b47'; ctx.font = 'bold 6px Arial'; ctx.textAlign = 'center'; ctx.fillText(String(car.id + 1).padStart(2, '0'), -8, 2);
    }
    ctx.fillStyle = '#efffff'; ctx.shadowColor = '#b4fff2'; ctx.shadowBlur = 7; ctx.fillRect(23, -8, 2.5, 5); ctx.fillRect(23, 3, 2.5, 5);
    ctx.shadowColor = '#ff344d'; ctx.fillStyle = keys.has('KeyS') || keys.has('ArrowDown') || car.police ? '#ff5667' : '#be3546'; ctx.fillRect(-24, -8, 2, 5); ctx.fillRect(-24, 3, 2, 5);
    ctx.shadowBlur = 0; ctx.fillStyle = '#08131b'; ctx.fillRect(-25, -13, 3, 26);
    if (!car.police && car.immunity > 0 && Math.sin(simClock * 40) > 0) {
      ctx.strokeStyle = '#ffffffbb'; ctx.lineWidth = 1.5; ctx.strokeRect(-28, -16, 56, 32);
    }
    ctx.restore();
  }
  function drawBonus(b) {
    ctx.save(); ctx.translate(b.x, b.y); ctx.rotate(Math.PI / 4);
    ctx.globalAlpha = b.life < 5 ? 0.4 + Math.sin(visualTime * 9) * 0.3 : 1;
    ctx.shadowColor = '#ceef72'; ctx.shadowBlur = 18; ctx.fillStyle = '#d6f77622'; ctx.fillRect(-16, -16, 32, 32);
    ctx.strokeStyle = '#dcfa83'; ctx.lineWidth = 1.5; ctx.strokeRect(-12, -12, 24, 24); ctx.shadowBlur = 0;
    ctx.rotate(-Math.PI / 4); ctx.fillStyle = '#e3ff98'; ctx.font = 'bold 15px Arial'; ctx.textAlign = 'center'; ctx.fillText('+', 0, 5); ctx.restore();
  }
  function drawShowcase() {
    if (width < 650) return;
    const x = width * 0.745, y = height * 0.49, radius = Math.min(width * 0.135, height * 0.29);
    ctx.save(); ctx.translate(x, y);
    const glow = ctx.createRadialGradient(0, 0, 0, 0, 0, radius * 1.65);
    glow.addColorStop(0, '#22cdbc16'); glow.addColorStop(1, '#22cdbc00'); ctx.fillStyle = glow; ctx.fillRect(-radius * 1.7, -radius * 1.7, radius * 3.4, radius * 3.4);
    ctx.strokeStyle = '#6cb9b22a'; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.arc(0, 0, radius, 0, Math.PI * 2); ctx.stroke();
    ctx.setLineDash([2, 14]); ctx.beginPath(); ctx.arc(0, 0, radius + 10, 0, Math.PI * 2); ctx.stroke(); ctx.setLineDash([]);
    for (const s of [-1, 1]) { ctx.beginPath(); ctx.moveTo(s * (radius - 12), 0); ctx.lineTo(s * (radius + 20), 0); ctx.moveTo(0, s * (radius - 12)); ctx.lineTo(0, s * (radius + 20)); ctx.stroke(); }
    const scale = radius / 34; ctx.scale(scale, scale);
    drawVehicle({ ...player, x: 0, y: 0, angle: -0.97, steer: 0.1 }, true);
    ctx.restore();
  }
  function render() {
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0); ctx.fillStyle = '#091218'; ctx.fillRect(0, 0, width, height);
    ctx.save();
    const jolt = reducedMotion ? 0 : shake;
    ctx.translate(width / 2 + Math.sin(visualTime * 73) * jolt, height / 2 + Math.cos(visualTime * 91) * jolt * 0.65);
    ctx.scale(camera.zoom, camera.zoom); ctx.translate(-camera.x, -camera.y);
    drawCity();
    ctx.lineWidth = 3.8; ctx.lineCap = 'round';
    for (const s of skidMarks) { ctx.strokeStyle = `rgba(3,8,11,${Math.min(0.55, s.life * 0.12)})`; ctx.beginPath(); ctx.moveTo(s.x, s.y); ctx.lineTo(s.x2, s.y2); ctx.stroke(); }
    ctx.lineCap = 'butt'; bonuses.forEach(drawBonus);
    cops.forEach(drawHeadlights); drawHeadlights(player);
    cops.forEach(c => drawVehicle(c)); drawVehicle(player);
    for (const p of particles) { ctx.globalAlpha = clamp(p.life / p.max, 0, 1); ctx.strokeStyle = p.color; ctx.lineWidth = 1.8; ctx.beginPath(); ctx.moveTo(p.x, p.y); ctx.lineTo(p.x - p.vx * 0.035, p.y - p.vy * 0.035); ctx.stroke(); }
    ctx.globalAlpha = 1;
    for (const f of floatTexts) { ctx.globalAlpha = Math.min(1, f.life * 2); ctx.fillStyle = '#e1ff83'; ctx.font = 'bold 20px Courier New'; ctx.textAlign = 'center'; ctx.fillText(f.text, f.x, f.y - 30); }
    ctx.globalAlpha = 1; ctx.restore();
    if (state === 'MENU') drawShowcase();
    if (state !== 'MENU' && closestCop < 280) {
      const strength = (1 - closestCop / 280) * (0.08 + Math.sin(visualTime * 4) * 0.025);
      const edge = ctx.createRadialGradient(width / 2, height / 2, Math.min(width, height) * 0.32, width / 2, height / 2, Math.max(width, height) * 0.6);
      edge.addColorStop(0, '#fe4a6200'); edge.addColorStop(1, `rgba(255,57,87,${strength})`); ctx.fillStyle = edge; ctx.fillRect(0, 0, width, height);
    }
    if (flash > 0) { ctx.fillStyle = `rgba(255,96,91,${flash * 0.42})`; ctx.fillRect(0, 0, width, height); }
  }
  function drawMinimap() {
    const size = 180, scale = size / WORLD;
    mapCtx.setTransform(mapCanvas.width / size, 0, 0, mapCanvas.height / size, 0, 0);
    mapCtx.fillStyle = '#0b171e'; mapCtx.fillRect(0, 0, size, size);
    mapCtx.strokeStyle = '#30444e'; mapCtx.lineWidth = ROAD * scale;
    for (const c of centers) { mapCtx.beginPath(); mapCtx.moveTo(c * scale, 0); mapCtx.lineTo(c * scale, size); mapCtx.moveTo(0, c * scale); mapCtx.lineTo(size, c * scale); mapCtx.stroke(); }
    mapCtx.strokeStyle = '#87b8b247'; mapCtx.lineWidth = 0.7;
    mapCtx.strokeRect((camera.x - width / camera.zoom / 2) * scale, (camera.y - height / camera.zoom / 2) * scale, width / camera.zoom * scale, height / camera.zoom * scale);
    for (const b of bonuses) { mapCtx.fillStyle = '#d4f85c'; mapCtx.fillRect(b.x * scale - 1.7, b.y * scale - 1.7, 3.4, 3.4); }
    for (const c of cops) { mapCtx.fillStyle = '#ff5973'; mapCtx.beginPath(); mapCtx.arc(c.x * scale, c.y * scale, 2.5, 0, Math.PI * 2); mapCtx.fill(); }
    mapCtx.save(); mapCtx.translate(player.x * scale, player.y * scale); mapCtx.rotate(player.angle);
    mapCtx.fillStyle = '#4ff7df'; mapCtx.beginPath(); mapCtx.moveTo(5, 0); mapCtx.lineTo(-3, -3); mapCtx.lineTo(-1.4, 0); mapCtx.lineTo(-3, 3); mapCtx.closePath(); mapCtx.fill(); mapCtx.restore();
    mapCtx.strokeStyle = '#4c606880'; mapCtx.lineWidth = 1; mapCtx.strokeRect(0.5, 0.5, size - 1, size - 1);
  }
  function resize() {
    const rect = canvas.getBoundingClientRect();
    width = Math.max(1, rect.width); height = Math.max(1, rect.height); dpr = Math.min(window.devicePixelRatio || 1, 2);
    canvas.width = Math.round(width * dpr); canvas.height = Math.round(height * dpr);
    mapCanvas.width = Math.round(180 * dpr); mapCanvas.height = Math.round(180 * dpr);
    drawMinimap();
  }
  const controlledKeys = new Set(['KeyW', 'KeyA', 'KeyS', 'KeyD', 'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight', 'Space', 'ShiftLeft', 'ShiftRight', 'KeyP', 'Escape', 'KeyR', 'Enter']);
  window.addEventListener('keydown', event => {
    if (!controlledKeys.has(event.code) || event.ctrlKey || event.metaKey || event.altKey) return;
    if (event.target && event.target.tagName === 'BUTTON' && (event.code === 'Space' || event.code === 'Enter')) return;
    event.preventDefault();
    if (event.code === 'KeyP' || event.code === 'Escape') { if (!event.repeat) togglePause(); return; }
    if (event.code === 'KeyR' && state === 'GAME_OVER' && !event.repeat) { startRun(); return; }
    if (event.code === 'Enter' && state === 'MENU' && !event.repeat) { startRun(); return; }
    if (state === 'PLAYING') keys.add(event.code);
  });
  window.addEventListener('keyup', event => { keys.delete(event.code); if (controlledKeys.has(event.code)) event.preventDefault(); });
  function loseFocus() { keys.clear(); accumulator = 0; lastTime = null; if (state === 'PLAYING') togglePause(); }
  window.addEventListener('blur', loseFocus);
  document.addEventListener('visibilitychange', () => { if (document.hidden) loseFocus(); else { accumulator = 0; lastTime = null; } });
  window.addEventListener('resize', resize);
  $('start-button').addEventListener('click', startRun); $('restart-button').addEventListener('click', startRun);
  $('resume-button').addEventListener('click', togglePause); ui['pause-button'].addEventListener('click', togglePause);
  document.querySelector('.brand').addEventListener('click', event => { event.preventDefault(); if (state === 'PLAYING') togglePause(); });
  canvas.addEventListener('pointerdown', () => canvas.focus({ preventScroll: true }));
  function frame(timestamp) {
    const frameDt = lastTime === null ? 0 : clamp((timestamp - lastTime) / 1000, 0, 0.05);
    lastTime = timestamp;
    if (state === 'PLAYING') {
      accumulator += frameDt;
      while (accumulator + 1e-9 >= STEP && state === 'PLAYING') { update(STEP); accumulator = Math.max(0, accumulator - STEP); }
      visualTime += frameDt;
    } else {
      accumulator = 0;
      if (state === 'MENU') visualTime += frameDt;
    }
    render();
    requestAnimationFrame(frame);
  }
  resize(); updateHUD();
  requestAnimationFrame(frame);
})();
