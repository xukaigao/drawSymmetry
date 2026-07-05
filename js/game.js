/* 🪞 画出对称的另一半 —— 给出对称轴和图形的一半，孩子在格子纸上画出镜像的另一半。
 *
 * 思路：
 *  - 图形由「格点之间的单位线段」组成（横/竖/斜，8 个方向）。
 *  - 出题：在对称轴的一侧随机走一条折线（题目的一半），它关于轴的镜像就是标准答案。
 *  - 判定：孩子画的线段集合 == 题目一半的镜像集合（不多不少）。
 */
(() => {
  "use strict";

  const COLS = 10, ROWS = 8;   // 格子数（格点为 (COLS+1)×(ROWS+1)）
  const CS = 38, PAD = 22;     // 每格像素、外边距
  const AX = 5, AY = 4;        // 竖/横轴位置
  const DC1 = -1, DC2 = 9;     // 斜轴：y=x+DC1（过中心）、x+y=DC2（过中心）
  const SNAP = CS * 0.42;      // 画线时吸附到格点的距离阈值

  const DIRS8 = [[1, 0], [-1, 0], [0, 1], [0, -1], [1, 1], [1, -1], [-1, 1], [-1, -1]];
  // 2 格矩形对角线（斜率 1/2、2 等）
  const SLANT2 = [[2, 1], [2, -1], [-2, 1], [-2, -1], [1, 2], [1, -2], [-1, 2], [-1, -2]];
  // 3 格矩形对角线（斜率 1/3、2/3、3、3/2 等）
  const SLANT3 = [
    [3, 1], [3, -1], [-3, 1], [-3, -1], [1, 3], [1, -3], [-1, 3], [-1, -3],
    [3, 2], [3, -2], [-3, 2], [-3, -2], [2, 3], [2, -3], [-2, 3], [-2, -3],
  ];
  // 出题时按难度可用的「一步」向量（都是基本向量，gcd=1，无中间格点）
  const STEP_SETS = {
    easy: DIRS8,
    medium: DIRS8.concat(SLANT2),
    hard: DIRS8.concat(SLANT2, SLANT3),
  };
  const MAX_EXTENT = 3; // 画线时矩形最多跨 3 格

  const gcd = (a, b) => { a = Math.abs(a); b = Math.abs(b); while (b) { [a, b] = [b, a % b]; } return a; };

  const SVGNS = "http://www.w3.org/2000/svg";
  const $ = (id) => document.getElementById(id);
  const board = $("board");
  const boardCard = $("boardCard");
  const statusEl = $("status");
  const axisSel = $("axisSel");
  const diffSel = $("diffSel");
  const praiseModal = $("praiseModal");
  const praiseText = $("praiseText");

  let svg, gGhost, gKid, gPreview; // 关键 svg 图层
  let axis = null;              // 当前对称轴
  let givenSet = new Set();     // 题目给出的一半
  let requiredSet = new Set();  // 标准答案（镜像）
  let kidSet = new Set();       // 孩子已画
  let kidOrder = [];            // 画线顺序（用于按序渲染）
  let painting = false, lastPt = null;
  let ghostTimer = 0;
  let lastSolved = false;       // 防止重复弹通关祝贺
  let praiseTimer = 0;          // 通关后延时弹窗
  let currentFigure = null;     // 中等档：当前题目图形名（如「王冠」）
  let countedThisPuzzle = false; // 本题是否已计入成就（防止撤销再画重复计数）

  // 通关彩虹屁：随机一句，肯定 6–12 岁孩子的努力与思考
  const PRAISES = [
    "太厉害了！你把另一半画得分毫不差，对称感真好！",
    "你观察得好仔细，每一笔都找准了镜子里的位置！",
    "哇，你的眼睛像尺子一样准，画得又对又漂亮！",
    "你动了好多脑筋，这份认真特别了不起！",
    "你一步步想清楚再下笔，真是个会思考的孩子！",
    "完美对称！你的空间想象力越来越棒啦！",
    "你没有急着乱画，而是仔细对照，这样真聪明！",
    "你把斜线也画得这么准，手和脑配合得真好！",
    "了不起！再难的对称图形都被你拿下了！",
    "你的耐心和细心，让这幅图变得对称又好看！",
    "你越画越熟练，脑筋转得又快又准！",
    "真棒！你能看出镜子两边一一对应，思路很清晰！",
    "你敢于挑战难题，这股认真劲儿太可贵了！",
    "哇，画得真整齐！你对对称的理解越来越深啦！",
    "你把每条线都安排得恰到好处，真有数学头脑！",
    "你的努力都画在纸上啦，每一笔都值得表扬！",
    "你像小镜子一样，把图形对得严丝合缝！",
    "太赞了！你先思考再动手，越来越会学习了！",
    "你找到了所有对称的线，观察力满分！",
    "你做得又快又好，继续加油，你真是个小能手！",
  ];
  const randomPraise = () => PRAISES[Math.floor(Math.random() * PRAISES.length)];

  // ---------- 成就 / 进度（持久化，给孩子持续动力） ----------
  const LS_COUNT = "drawSym_solvedCount";
  const LS_COLLECTED = "drawSym_collected";
  let solvedCount = 0;          // 累计完成的题数（所有难度）
  let collected = new Set();    // 收集到的题库图形名（图鉴）
  let pendingProgressMsg = "";  // 通关弹窗里附带的进度文字
  let statsEl = null;

  function loadProgress() {
    try {
      solvedCount = parseInt(localStorage.getItem(LS_COUNT) || "0", 10) || 0;
      const arr = JSON.parse(localStorage.getItem(LS_COLLECTED) || "[]");
      if (Array.isArray(arr)) collected = new Set(arr);
    } catch (_) { /* localStorage 不可用就用内存值 */ }
  }
  function saveProgress() {
    try {
      localStorage.setItem(LS_COUNT, String(solvedCount));
      localStorage.setItem(LS_COLLECTED, JSON.stringify([...collected]));
    } catch (_) { }
  }
  function renderStats(bump) {
    if (!statsEl) return;
    const total = LIBRARY.length;
    statsEl.innerHTML =
      `<span class="chip${bump ? " bump" : ""}">🏅 已画好 <b>${solvedCount}</b> 个图形</span>` +
      `<span class="chip${bump ? " bump" : ""}">📒 图鉴 <b>${collected.size}</b>/${total}</span>`;
  }
  function onSolved() {
    solvedCount++;
    let newly = false;
    if (currentFigure && !collected.has(currentFigure)) { collected.add(currentFigure); newly = true; }
    saveProgress();
    renderStats(true);

    // 组织通关弹窗里的进度鼓励语
    const lines = [`这是你完成的第 ${solvedCount} 个图形！`];
    if (newly && collected.size >= LIBRARY.length) {
      lines.push(`🏆 太了不起！${LIBRARY.length} 种图形全部收集齐啦！`);
    } else if (newly) {
      lines.push(`🎉 解锁新图形【${currentFigure}】！图鉴 ${collected.size}/${LIBRARY.length}`);
    } else if (solvedCount % 5 === 0) {
      lines.push(`🔥 连续完成 ${solvedCount} 个，你太有毅力啦！`);
    }
    pendingProgressMsg = lines.join("<br>");
  }

  const el = (name, attrs) => {
    const n = document.createElementNS(SVGNS, name);
    for (const k in attrs) n.setAttribute(k, attrs[k]);
    return n;
  };
  const px = (x) => PAD + x * CS;
  const py = (y) => PAD + y * CS;
  const randInt = (a, b) => a + Math.floor(Math.random() * (b - a + 1));
  const shuffle = (arr) => { for (let i = arr.length - 1; i > 0; i--) { const j = randInt(0, i); [arr[i], arr[j]] = [arr[j], arr[i]]; } return arr; };

  // ---------- 坐标 / 线段 ----------
  const pStr = (p) => p[0] + "," + p[1];
  function segKey(a, b) {
    const ka = pStr(a), kb = pStr(b);
    return ka < kb ? ka + "|" + kb : kb + "|" + ka;
  }
  function parseSeg(key) {
    const [pa, pb] = key.split("|");
    return [pa.split(",").map(Number), pb.split(",").map(Number)];
  }
  const inBounds = ([x, y]) => x >= 0 && x <= COLS && y >= 0 && y <= ROWS;

  // ---------- 对称轴 ----------
  function makeAxis(type) {
    if (type === "v") return {
      type, reflect: ([x, y]) => [2 * AX - x, y], dist: ([x, y]) => x - AX,
      line: () => [[AX, 0], [AX, ROWS]], label: ["竖直对称轴", AX, 0],
    };
    if (type === "h") return {
      type, reflect: ([x, y]) => [x, 2 * AY - y], dist: ([x, y]) => y - AY,
      line: () => [[0, AY], [COLS, AY]], label: ["水平对称轴", 0, AY],
    };
    if (type === "d1") { // y = x + DC1
      const C = DC1;
      const xa = Math.max(0, -C), xb = Math.min(COLS, ROWS - C);
      return {
        type, reflect: ([x, y]) => [y - C, x + C], dist: ([x, y]) => y - x - C,
        line: () => [[xa, xa + C], [xb, xb + C]], label: null,
      };
    }
    // d2: x + y = DC2
    const C = DC2;
    const xa = Math.max(0, C - ROWS), xb = Math.min(COLS, C);
    return {
      type, reflect: ([x, y]) => [C - y, C - x], dist: ([x, y]) => x + y - C,
      line: () => [[xa, C - xa], [xb, C - xb]], label: null,
    };
  }

  function pickStart(ax) {
    for (let i = 0; i < 200; i++) {
      const p = [randInt(0, COLS), randInt(0, ROWS)];
      const d = ax.dist(p);
      if (d <= 0 && d >= -3 && inBounds(ax.reflect(p))) return p;
    }
    return [AX, AY]; // 兜底
  }

  // ---------- 出题 ----------
  // 简单档：从对称轴出发、不自交地走一圈再收回到轴上，形成「闭合轮廓」的一半，
  // 只有外轮廓、没有内部零碎线段，孩子描另一半更省事。
  function outlineWalk(ax, minLen, maxLen) {
    const axisPts = [];
    for (let x = 0; x <= COLS; x++)
      for (let y = 0; y <= ROWS; y++)
        if (ax.dist([x, y]) === 0) axisPts.push([x, y]);
    if (!axisPts.length) return null;

    for (let tryi = 0; tryi < 50; tryi++) {
      const start = axisPts[randInt(0, axisPts.length - 1)];
      const visited = new Set([pStr(start)]);
      const pts = [start];
      let p = start;
      const target = randInt(minLen, maxLen);
      let closed = false;
      while (pts.length - 1 < target) {
        const cands = [];
        for (const [dx, dy] of DIRS8) {
          const q = [p[0] + dx, p[1] + dy];
          if (!inBounds(q) || ax.dist(q) > 0) continue;
          if (visited.has(pStr(q))) continue;                    // 不重复经过格点（不自交）
          if (Math.min(ax.dist(p), ax.dist(q)) >= 0) continue;   // 不沿着轴走
          if (!inBounds(ax.reflect(q))) continue;
          cands.push(q);
        }
        if (!cands.length) break;
        const interior = cands.filter((q) => ax.dist(q) < 0);
        const onAxis = cands.filter((q) => ax.dist(q) === 0);
        if (pts.length - 1 >= minLen && onAxis.length && Math.random() < 0.6) {
          const q = onAxis[randInt(0, onAxis.length - 1)];
          pts.push(q); closed = true; break;                     // 收口回到对称轴
        }
        const pool = interior.length ? interior : cands;
        const q = pool[randInt(0, pool.length - 1)];
        pts.push(q); visited.add(pStr(q)); p = q;
      }
      if (pts.length >= 4) { // 至少 3 段
        const segs = new Set();
        for (let i = 0; i + 1 < pts.length; i++) segs.add(segKey(pts[i], pts[i + 1]));
        return segs;
      }
    }
    return null;
  }

  // 中等/较难档：自由折线（可含 2~3 格斜线、可分叉），更有挑战。
  function freeWalk(ax, steps, stepSet) {
    const segs = new Set();
    let p = pickStart(ax);
    let guard = 0;
    while (segs.size < steps && guard < steps * 8) {
      guard++;
      let moved = false;
      for (const [dx, dy] of shuffle(stepSet.slice())) {
        const q = [p[0] + dx, p[1] + dy];
        if (!inBounds(q) || ax.dist(q) > 0) continue;
        if (Math.min(ax.dist(p), ax.dist(q)) >= 0) continue;       // 不要落在轴上的线段
        const rp = ax.reflect(p), rq = ax.reflect(q);
        if (!inBounds(rp) || !inBounds(rq)) continue;
        const k = segKey(p, q);
        if (segs.has(k)) continue;
        segs.add(k); p = q; moved = true; break;
      }
      if (!moved) { // 卡住，跳到已有的某个端点继续
        const pts = [...segs].flatMap(parseSeg);
        if (!pts.length) break;
        p = pts[randInt(0, pts.length - 1)];
      }
    }
    return segs.size >= Math.max(3, steps - 2) ? segs : null;
  }

  // 中等档：固定题库——漂亮、有意义的图形（竖直对称）。
  // 每个图形用「左半边」的折线表示（端点 x≤AX=5，触轴只在顶点处），
  // 镜像后即得右半边标准答案。多段折线可拼出门、横杆等细节。
  const LIBRARY = [
    { name: "王冠", parts: [[[5, 7], [2, 7], [2, 4], [3, 2], [4, 4], [5, 2]]] },
    { name: "爱心", parts: [[[5, 7], [3, 5], [2, 4], [2, 3], [3, 2], [4, 2], [5, 3]]] },
    { name: "房子", parts: [[[5, 7], [2, 7], [2, 4], [5, 2]], [[4, 7], [4, 5], [5, 5]]] },
    { name: "圣诞树", parts: [[[5, 1], [2, 4], [3, 4], [1, 6], [4, 6], [4, 7], [5, 7]]] },
    { name: "钻石", parts: [[[5, 2], [3, 2], [2, 4], [5, 7]], [[2, 4], [5, 4]]] },
    { name: "箭头", parts: [[[5, 1], [2, 4], [4, 4], [4, 7], [5, 7]]] },
    { name: "杯子", parts: [[[5, 7], [2, 7], [1, 5], [1, 3], [5, 3]], [[1, 3], [0, 4]]] },
    { name: "蝴蝶结", parts: [[[5, 5], [2, 3], [2, 7], [5, 5]]] },
    { name: "小鱼", parts: [[[5, 1], [2, 3], [2, 5], [4, 7], [5, 5]]] },
    { name: "星星", parts: [[[5, 1], [4, 3], [2, 4], [4, 5], [5, 7]]] },
    {
      name: "城堡",
      parts: [
        [[5, 7], [1, 7], [1, 3], [2, 3], [2, 2], [3, 2], [3, 3], [4, 3], [4, 2], [5, 2]],
        [[4, 7], [4, 5], [5, 5]],
      ],
    },
    {
      name: "雪人",
      parts: [
        [[5, 1], [3, 2], [4, 3], [5, 3]],
        [[5, 3], [2, 4], [2, 6], [4, 7], [5, 7]],
        [[2, 5], [0, 4]],
      ],
    },
    { name: "蘑菇", parts: [[[5, 1], [2, 3], [3, 4], [4, 4], [4, 7], [5, 7]]] },
    { name: "雨伞", parts: [[[5, 1], [3, 2], [1, 4], [2, 5], [3, 4], [4, 5], [5, 4]]] },
    {
      name: "热气球",
      parts: [
        [[5, 0], [3, 1], [1, 3], [3, 5], [5, 5]],
        [[5, 6], [4, 6], [4, 7], [5, 7]],
        [[3, 5], [4, 6]],
      ],
    },
    {
      name: "皇冠宝石",
      parts: [
        [[5, 7], [2, 7], [2, 4], [3, 2], [4, 4], [5, 2]],
        [[5, 5], [3, 6], [5, 7]],
      ],
    },
    { name: "花朵", parts: [[[5, 6], [2, 5], [2, 2], [3, 4], [5, 1]], [[5, 6], [3, 7]]] },
    { name: "帆船", parts: [[[5, 7], [3, 7], [1, 6], [5, 6]], [[5, 2], [3, 6], [5, 6]]] },
  ];

  // 把折线按 gcd 拆成「基本格段」（与孩子画线时的拆分一致，保证可对上）
  function polyToSegs(points) {
    const out = [];
    for (let i = 0; i + 1 < points.length; i++) {
      const a = points[i], b = points[i + 1];
      const dx = b[0] - a[0], dy = b[1] - a[1];
      if (dx === 0 && dy === 0) continue;
      const g = gcd(dx, dy);
      const sx = dx / g, sy = dy / g;
      for (let j = 0; j < g; j++) {
        out.push(segKey([a[0] + sx * j, a[1] + sy * j], [a[0] + sx * (j + 1), a[1] + sy * (j + 1)]));
      }
    }
    return out;
  }

  // 洗牌不重复：把题库索引洗成一个袋子，逐个取，取完再洗（避免与上一个相邻重复）
  let figBag = [];
  let lastFigIdx = -1;
  function nextLibIndex() {
    if (!figBag.length) {
      figBag = LIBRARY.map((_, i) => i);
      shuffle(figBag);
      if (figBag.length > 1 && figBag[figBag.length - 1] === lastFigIdx) {
        [figBag[0], figBag[figBag.length - 1]] = [figBag[figBag.length - 1], figBag[0]];
      }
    }
    lastFigIdx = figBag.pop();
    return lastFigIdx;
  }

  function generateFromLibrary() {
    const ax = makeAxis("v"); // 这些图形都是竖直对称才好看，固定用竖轴
    const fig = LIBRARY[nextLibIndex()];
    const segs = new Set();
    for (const part of fig.parts) for (const k of polyToSegs(part)) segs.add(k);
    const required = new Set([...segs].map((k) => {
      const [a, b] = parseSeg(k);
      return segKey(ax.reflect(a), ax.reflect(b));
    }));
    return { axis: ax, given: [...segs], required, name: fig.name };
  }

  function generate(axisChoice, diff) {
    if (diff === "medium") return generateFromLibrary();
    const steps = STEPS[diff] || 5;
    const stepSet = STEP_SETS[diff] || DIRS8;
    let type;
    if (axisChoice === "v" || axisChoice === "h") type = axisChoice;
    else if (axisChoice === "diag") type = Math.random() < 0.5 ? "d1" : "d2";
    else type = ["v", "h", "d1", "d2"][randInt(0, 3)];

    for (let attempt = 0; attempt < 80; attempt++) {
      const ax = makeAxis(type);
      const segs = diff === "easy" ? outlineWalk(ax, 4, 7) : freeWalk(ax, steps, stepSet);
      if (segs && segs.size >= 3) {
        const required = new Set([...segs].map((k) => {
          const [a, b] = parseSeg(k);
          return segKey(ax.reflect(a), ax.reflect(b));
        }));
        return { axis: ax, given: [...segs], required };
      }
    }
    // 兜底：竖轴上的一个小轮廓（都用基本格段，保证可画可对）
    const ax = makeAxis("v");
    const fb = [[5, 1], [4, 2], [4, 3], [5, 4]];
    const g = [];
    for (let i = 0; i + 1 < fb.length; i++) g.push(segKey(fb[i], fb[i + 1]));
    const required = new Set(g.map((k) => { const [a, b] = parseSeg(k); return segKey(ax.reflect(a), ax.reflect(b)); }));
    return { axis: ax, given: g, required };
  }

  // ---------- 渲染 ----------
  function buildBoard() {
    board.innerHTML = "";
    const w = COLS * CS + 2 * PAD, h = ROWS * CS + 2 * PAD;
    svg = el("svg", { viewBox: `0 0 ${w} ${h}`, role: "img" });

    // 背景
    svg.appendChild(el("rect", { x: 0, y: 0, width: w, height: h, rx: 10, fill: "#fff" }));

    // 格子纸
    const gGrid = el("g", {});
    for (let x = 0; x <= COLS; x++) {
      const c = el("line", { x1: px(x), y1: py(0), x2: px(x), y2: py(ROWS), class: "grid-line" });
      if (x === 0 || x === COLS) c.classList.add("edge");
      gGrid.appendChild(c);
    }
    for (let y = 0; y <= ROWS; y++) {
      const c = el("line", { x1: px(0), y1: py(y), x2: px(COLS), y2: py(y), class: "grid-line" });
      if (y === 0 || y === ROWS) c.classList.add("edge");
      gGrid.appendChild(c);
    }
    svg.appendChild(gGrid);

    // 对称轴
    const [la, lb] = axis.line();
    svg.appendChild(el("line", { x1: px(la[0]), y1: py(la[1]), x2: px(lb[0]), y2: py(lb[1]), class: "axis-line" }));

    // 格点
    const gDots = el("g", {});
    for (let x = 0; x <= COLS; x++)
      for (let y = 0; y <= ROWS; y++)
        gDots.appendChild(el("circle", { cx: px(x), cy: py(y), r: 2.6, class: "dot" }));
    svg.appendChild(gDots);

    // 题目（给定一半）
    const gGiven = el("g", {});
    for (const k of givenSet) {
      const [a, b] = parseSeg(k);
      gGiven.appendChild(el("line", { x1: px(a[0]), y1: py(a[1]), x2: px(b[0]), y2: py(b[1]), class: "seg-given" }));
    }
    svg.appendChild(gGiven);

    gGhost = el("g", {}); svg.appendChild(gGhost);   // 提示层
    gKid = el("g", {}); svg.appendChild(gKid);       // 孩子画的
    gPreview = el("g", {}); svg.appendChild(gPreview); // 拖动预览

    // 对称轴文字提示
    let lbl;
    if (axis.type === "v") {
      lbl = el("text", { x: px(AX), y: py(0) + 14, class: "axis-label", "text-anchor": "middle" });
      lbl.textContent = "← 镜子 →";
    } else if (axis.type === "h") {
      lbl = el("text", { x: px(COLS) - 6, y: py(AY) - 8, class: "axis-label", "text-anchor": "end" });
      lbl.textContent = "↑ 镜子 ↓";
    } else {
      // 斜轴：把「镜子」放在轴线中点旁，并沿轴线方向倾斜
      const mx = (px(la[0]) + px(lb[0])) / 2;
      const my = (py(la[1]) + py(lb[1])) / 2;
      const angle = axis.type === "d1" ? 45 : -45;  // d1 沿 ↘、d2 沿 ↗
      const ox = axis.type === "d1" ? 9 : 9;
      const oy = axis.type === "d1" ? -9 : 9;        // 偏到轴线一侧，避免压住虚线
      const ax2 = mx + ox, ay2 = my + oy;
      lbl = el("text", {
        x: ax2, y: ay2, class: "axis-label", "text-anchor": "middle",
        transform: `rotate(${angle}, ${ax2}, ${ay2})`,
      });
      lbl.textContent = "镜子 🪞";
    }
    svg.appendChild(lbl);

    board.appendChild(svg);
    bindDrawing();
    renderKid();
  }

  function renderKid() {
    while (gKid.firstChild) gKid.removeChild(gKid.firstChild);
    for (const k of kidOrder) {
      const [a, b] = parseSeg(k);
      const cls = requiredSet.has(k) ? "seg-ok" : "seg-bad";
      gKid.appendChild(el("line", { x1: px(a[0]), y1: py(a[1]), x2: px(b[0]), y2: py(b[1]), class: cls }));
      const hit = el("line", { x1: px(a[0]), y1: py(a[1]), x2: px(b[0]), y2: py(b[1]), class: "seg-hit" });
      hit.dataset.key = k;
      gKid.appendChild(hit);
    }
  }

  // ---------- 交互 ----------
  function svgPoint(clientX, clientY) {
    const pt = svg.createSVGPoint();
    pt.x = clientX; pt.y = clientY;
    const loc = pt.matrixTransform(svg.getScreenCTM().inverse());
    return loc;
  }
  // 返回离指针最近的格点及其距离（格点已限制在网格内）
  function nearestDotInfo(clientX, clientY) {
    const loc = svgPoint(clientX, clientY);
    const gx = Math.round((loc.x - PAD) / CS);
    const gy = Math.round((loc.y - PAD) / CS);
    if (gx < 0 || gx > COLS || gy < 0 || gy > ROWS) return null;
    const dist = Math.hypot(loc.x - px(gx), loc.y - py(gy));
    return { pt: [gx, gy], dist };
  }
  // 把指针位置取整到最近的格点（始终返回，已夹在网格内）——用于拖动终点
  function roundDot(clientX, clientY) {
    const loc = svgPoint(clientX, clientY);
    const gx = Math.min(COLS, Math.max(0, Math.round((loc.x - PAD) / CS)));
    const gy = Math.min(ROWS, Math.max(0, Math.round((loc.y - PAD) / CS)));
    return [gx, gy];
  }

  function addSeg(a, b) {
    const k = segKey(a, b);
    if (givenSet.has(k) || kidSet.has(k)) return;
    kidSet.add(k); kidOrder.push(k);
  }
  function removeSeg(k) {
    if (!kidSet.has(k)) return;
    kidSet.delete(k);
    kidOrder = kidOrder.filter((x) => x !== k);
    renderKid(); evaluate();
  }

  // 把任意「A→B 直线」拆成若干基本格段后加入（支持 2~3 格矩形对角线）
  function commitSegment(a, b) {
    let dx = b[0] - a[0], dy = b[1] - a[1];
    if (dx === 0 && dy === 0) return;
    if (Math.max(Math.abs(dx), Math.abs(dy)) > MAX_EXTENT) return; // 超过 3 格忽略
    const g = gcd(dx, dy);
    const sx = dx / g, sy = dy / g;
    for (let i = 0; i < g; i++) {
      addSeg([a[0] + sx * i, a[1] + sy * i], [a[0] + sx * (i + 1), a[1] + sy * (i + 1)]);
    }
    renderKid(); evaluate();
  }

  function clearPreview() { while (gPreview.firstChild) gPreview.removeChild(gPreview.firstChild); }
  function drawPreview(a, b) {
    clearPreview();
    if (a[0] === b[0] && a[1] === b[1]) return;
    const tooLong = Math.max(Math.abs(b[0] - a[0]), Math.abs(b[1] - a[1])) > MAX_EXTENT;
    gPreview.appendChild(el("line", {
      x1: px(a[0]), y1: py(a[1]), x2: px(b[0]), y2: py(b[1]),
      stroke: tooLong ? "#c0392b" : "#7aa0d0", "stroke-width": 4,
      "stroke-linecap": "round", "stroke-dasharray": "3 6", "pointer-events": "none",
    }));
  }

  function bindDrawing() {
    svg.addEventListener("pointerdown", (e) => {
      const info = nearestDotInfo(e.clientX, e.clientY);
      const t = e.target;
      const onHit = t && t.classList && t.classList.contains("seg-hit") && t.dataset.key;
      if (info && info.dist <= SNAP) {        // 在格点附近起笔
        e.preventDefault();
        painting = true; lastPt = info.pt;
        svg.setPointerCapture(e.pointerId);
        return;
      }
      if (onHit) { e.preventDefault(); removeSeg(t.dataset.key); } // 点已画线中段 → 擦掉
    });

    svg.addEventListener("pointermove", (e) => {
      if (!painting) return;
      drawPreview(lastPt, roundDot(e.clientX, e.clientY));
    });

    const finish = (e) => {
      if (!painting) return;
      painting = false;
      clearPreview();
      if (e && typeof e.clientX === "number") commitSegment(lastPt, roundDot(e.clientX, e.clientY));
    };
    svg.addEventListener("pointerup", finish);
    svg.addEventListener("pointercancel", () => { painting = false; clearPreview(); });
    svg.addEventListener("lostpointercapture", () => { painting = false; clearPreview(); });
  }

  // ---------- 判定 / 反馈 ----------
  function evaluate() {
    let correct = 0, wrong = 0;
    for (const k of kidSet) (requiredSet.has(k) ? correct++ : wrong++);
    const remaining = requiredSet.size - correct;
    const solved = wrong === 0 && remaining === 0;

    boardCard.classList.toggle("solved", solved);
    statusEl.className = "status";
    if (solved) {
      statusEl.classList.add("ok");
      statusEl.textContent = currentFigure ? `🎉 完成！这是一个漂亮的【${currentFigure}】！` : "🎉 完成！这就是漂亮的轴对称图形！";
      celebrate();
      newBtn?.classList.add("celebrate");
      if (!lastSolved) { // 刚通关：记一次成就，先让孩子看 2 秒图形，再弹祝贺
        if (!countedThisPuzzle) { countedThisPuzzle = true; onSolved(); }
        clearTimeout(praiseTimer);
        praiseTimer = setTimeout(showPraise, 2000);
      }
    } else {
      clearTimeout(praiseTimer); // 还没通关/又改动了，取消待弹的祝贺
      newBtn?.classList.remove("celebrate");
      clearSparkle();
      let msg = currentFigure ? `画出【${currentFigure}】的另一半 · 还要画 ${remaining} 笔` : `还要画 ${remaining} 笔`;
      if (wrong > 0) { msg += ` · 有 ${wrong} 笔画到不对称的位置了（红色）`; statusEl.classList.add("bad"); }
      statusEl.textContent = msg;
    }
    lastSolved = solved;
  }

  function showPraise() {
    praiseText.innerHTML = randomPraise() +
      (pendingProgressMsg ? `<span class="progress-line">${pendingProgressMsg}</span>` : "");
    praiseModal.classList.remove("hidden");
  }
  function hidePraise() { praiseModal.classList.add("hidden"); }

  function clearSparkle() {
    const old = svg.querySelectorAll(".sparkle");
    old.forEach((n) => n.remove());
  }
  function celebrate() {
    clearSparkle();
    const w = COLS * CS + 2 * PAD;
    [[w * 0.5, 16], [w * 0.2, 40], [w * 0.8, 40]].forEach(([x, y], i) => {
      const s = el("text", { x, y, "text-anchor": "middle", "font-size": 22, class: "sparkle" });
      s.style.animationDelay = i * 0.08 + "s";
      s.textContent = "✨";
      svg.appendChild(s);
    });
  }

  // ---------- 提示 ----------
  function showHint() {
    while (gGhost.firstChild) gGhost.removeChild(gGhost.firstChild);
    for (const k of requiredSet) {
      if (kidSet.has(k)) continue;
      const [a, b] = parseSeg(k);
      gGhost.appendChild(el("line", { x1: px(a[0]), y1: py(a[1]), x2: px(b[0]), y2: py(b[1]), class: "seg-ghost" }));
    }
    clearTimeout(ghostTimer);
    ghostTimer = setTimeout(() => { while (gGhost.firstChild) gGhost.removeChild(gGhost.firstChild); }, 1800);
  }

  // ---------- 出新题 ----------
  const STEPS = { easy: 4, medium: 5, hard: 7 };
  function newPuzzle() {
    axisSel.disabled = (diffSel.value === "medium"); // 中等档为固定题库，恒用竖轴
    const puzzle = generate(axisSel.value, diffSel.value);
    axis = puzzle.axis;
    currentFigure = puzzle.name || null;
    givenSet = new Set(puzzle.given);
    requiredSet = puzzle.required;
    kidSet = new Set(); kidOrder = [];
    lastSolved = false;
    countedThisPuzzle = false;
    clearTimeout(praiseTimer);
    newBtn?.classList.remove("celebrate");
    hidePraise();
    buildBoard();
    evaluate();
  }

  // ---------- 按钮 ----------
  // 用可选链 ?. 绑定，任一按钮暂时缺失也不会中断初始化、影响首屏出题
  const newBtn = $("newBtn");
  newBtn?.addEventListener("click", newPuzzle);
  $("clearBtn")?.addEventListener("click", () => {
    kidSet.clear(); kidOrder = []; renderKid(); evaluate();
  });
  $("hintBtn")?.addEventListener("click", showHint);
  $("praiseClose")?.addEventListener("click", hidePraise); // 关掉后停留在原题，方便细看
  praiseModal?.addEventListener("click", (e) => { if (e.target === praiseModal) hidePraise(); });
  axisSel?.addEventListener("change", newPuzzle);
  diffSel?.addEventListener("change", newPuzzle);

  statsEl = $("stats");
  loadProgress();
  renderStats(false);

  // 首屏出题。用 rAF 等一帧，确保布局就绪后再渲染，
  // 避免个别浏览器首帧时 SVG（仅有 viewBox、靠 CSS width:100%）被算成 0 尺寸而看不到图形。
  requestAnimationFrame(newPuzzle);
  // 兜底：页面完全加载后若棋盘里仍没有图形，再补出一题。
  window.addEventListener("load", () => {
    if (!board.querySelector("svg")) newPuzzle();
  });
})();
