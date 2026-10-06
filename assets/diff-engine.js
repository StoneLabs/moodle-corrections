/* Correction Diff — diff engine and HTML rendering.
   Pure functions without DOM access; exposed as window.CorrectionDiff
   (and module.exports, so it can be tested with Node). */
(function (root) {
'use strict';

const esc = s => s.replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]);

// Inline styles that survive Moodle: TinyMCE strips style="…" when pasting in
// Chromium/Safari, but its filter only matches double quotes, so single-quoted
// attributes come through. Every property is on HTMLPurifier's allow-list, and
// <del>/<ins>/<em> still read correctly if a filter ever drops the styles.
const STYLE = {
  del: 'color:#b42318;background-color:#fee4e2;text-decoration:line-through;text-decoration-color:#d92d20;border-radius:3px',
  ins: 'color:#067647;background-color:#dcfae6;text-decoration:none;border-radius:3px',
  note: 'color:#475467;background-color:#f2f4f7;font-style:italic;font-size:0.92em;border-radius:4px;padding:1px 6px',
  legend: 'color:#667085;font-size:0.875em',
  details: 'margin:0 0 0.6em',
  summary: 'cursor:pointer;color:#344054',
  sectionBody: 'margin:0.5em 0 0.9em 0.3em;padding:0.1em 0 0.1em 0.9em;border-left:3px solid #e4e7ec;color:#344054',
  unclear: 'background-color:#fef08a;border-radius:3px',
  unclearMark: 'color:#a16207;font-weight:700',
};

// Inline formatting is carried per character, next to the text, as a bit set.
const BOLD = 1, ITALIC = 2, UNDERLINE = 4;
const FORMAT_TAGS = [[BOLD, 'strong'], [ITALIC, 'em'], [UNDERLINE, 'u']];

// Han, kana and the prolonged sound mark are compared one character at a time,
// because Chinese and Japanese text has no spaces between words.
const CJK = '\\p{Script=Han}\\p{Script=Hiragana}\\p{Script=Katakana}\\u3005\\u3006\\u30FC';
const LETTER = `(?:(?![${CJK}])[\\p{L}\\p{N}\\p{M}])`;
const TOKEN_RE = new RegExp(`[${CJK}]|${LETTER}+(?:['’]${LETTER}+)*|[^\\S\\n]+|\\n|[\\s\\S]`, 'gu');
const CJK_RE = new RegExp(`[${CJK}]`, 'u');

function tokenize(text, mode) {
  const tokens = [], starts = [];
  if (mode === 'char') {
    let i = 0;
    for (const ch of text) { tokens.push(ch); starts.push(i); i += ch.length; }
  } else {
    TOKEN_RE.lastIndex = 0;
    let m;
    while ((m = TOKEN_RE.exec(text))) { tokens.push(m[0]); starts.push(m.index); }
  }
  return { tokens, starts, length: text.length };
}

function intern(ta, tb) {
  const ids = new Map();
  const conv = toks => {
    const out = new Int32Array(toks.length);
    for (let i = 0; i < toks.length; i++) {
      let id = ids.get(toks[i]);
      if (id === undefined) { id = ids.size; ids.set(toks[i], id); }
      out[i] = id;
    }
    return out;
  };
  return [conv(ta), conv(tb)];
}

const EQ = 0, DEL = 1, INS = 2;

// Myers' O(ND) diff in linear space (middle-snake bisection, as in diff-match-patch).
// Past the time budget, the remaining unmatched stretches become plain replacements.
let deadline = Infinity;
function diffTokens(a, b, resetBudget = true) {
  if (resetBudget) deadline = performance.now() + 250;
  const ops = [];
  diffRange(a, 0, a.length, b, 0, b.length, ops);
  return ops;
}

function diffRange(a, aLo, aHi, b, bLo, bHi, ops) {
  while (aLo < aHi && bLo < bHi && a[aLo] === b[bLo]) { ops.push(EQ); aLo++; bLo++; }
  let suffix = 0;
  while (aLo < aHi && bLo < bHi && a[aHi - 1] === b[bHi - 1]) { aHi--; bHi--; suffix++; }
  if (aLo === aHi) {
    for (let j = bLo; j < bHi; j++) ops.push(INS);
  } else if (bLo === bHi) {
    for (let i = aLo; i < aHi; i++) ops.push(DEL);
  } else {
    const split = bisect(a, aLo, aHi, b, bLo, bHi);
    const degenerate = !split || (split[0] === aLo && split[1] === bLo) || (split[0] === aHi && split[1] === bHi);
    if (degenerate) {
      for (let i = aLo; i < aHi; i++) ops.push(DEL);
      for (let j = bLo; j < bHi; j++) ops.push(INS);
    } else {
      diffRange(a, aLo, split[0], b, bLo, split[1], ops);
      diffRange(a, split[0], aHi, b, split[1], bHi, ops);
    }
  }
  for (let s = 0; s < suffix; s++) ops.push(EQ);
}

function bisect(a, aLo, aHi, b, bLo, bHi) {
  const n = aHi - aLo, m = bHi - bLo;
  const maxD = Math.ceil((n + m) / 2);
  const vOff = maxD, vLen = 2 * maxD;
  const v1 = new Int32Array(vLen + 2).fill(-1);
  const v2 = new Int32Array(vLen + 2).fill(-1);
  v1[vOff + 1] = 0;
  v2[vOff + 1] = 0;
  const delta = n - m;
  const front = (delta & 1) !== 0;
  let k1start = 0, k1end = 0, k2start = 0, k2end = 0;
  for (let d = 0; d < maxD; d++) {
    if ((d & 15) === 0 && performance.now() > deadline) return null;
    for (let k1 = -d + k1start; k1 <= d - k1end; k1 += 2) {
      const o = vOff + k1;
      let x1 = (k1 === -d || (k1 !== d && v1[o - 1] < v1[o + 1])) ? v1[o + 1] : v1[o - 1] + 1;
      let y1 = x1 - k1;
      while (x1 < n && y1 < m && a[aLo + x1] === b[bLo + y1]) { x1++; y1++; }
      v1[o] = x1;
      if (x1 > n) k1end += 2;
      else if (y1 > m) k1start += 2;
      else if (front) {
        const o2 = vOff + delta - k1;
        if (o2 >= 0 && o2 < vLen && v2[o2] !== -1 && x1 >= n - v2[o2]) return [aLo + x1, bLo + y1];
      }
    }
    for (let k2 = -d + k2start; k2 <= d - k2end; k2 += 2) {
      const o = vOff + k2;
      let x2 = (k2 === -d || (k2 !== d && v2[o - 1] < v2[o + 1])) ? v2[o + 1] : v2[o - 1] + 1;
      let y2 = x2 - k2;
      while (x2 < n && y2 < m && a[aHi - x2 - 1] === b[bHi - y2 - 1]) { x2++; y2++; }
      v2[o] = x2;
      if (x2 > n) k2end += 2;
      else if (y2 > m) k2start += 2;
      else if (!front) {
        const o1 = vOff + delta - k2;
        if (o1 >= 0 && o1 < vLen && v1[o1] !== -1) {
          const x1 = v1[o1];
          if (x1 >= n - x2) return [aLo + x1, bLo + x1 - (o1 - vOff)];
        }
      }
    }
  }
  return null;
}

// Collapse token ops into alternating equal / change runs, in character offsets.
function toRuns(ops, A, B) {
  const runs = [];
  let i = 0, j = 0, k = 0;
  while (k < ops.length) {
    const i0 = i, j0 = j, eq = ops[k] === EQ;
    if (eq) {
      while (k < ops.length && ops[k] === EQ) { i++; j++; k++; }
    } else {
      while (k < ops.length && ops[k] !== EQ) { if (ops[k] === DEL) i++; else j++; k++; }
    }
    runs.push({ eq, a0: i0, a1: i, b0: j0, b1: j });
  }
  const ca = t => (t < A.starts.length ? A.starts[t] : A.length);
  const cb = t => (t < B.starts.length ? B.starts[t] : B.length);
  for (const r of runs) { r.a0 = ca(r.a0); r.a1 = ca(r.a1); r.b0 = cb(r.b0); r.b1 = cb(r.b1); }
  return runs;
}

// How the raw token diff is shaped into what the student reads:
//   chars     — character diff, small leftovers inside words absorbed
//   words     — every changed word on its own (the minimal edit)
//   phrases   — neighbouring changes merged into one old/new pair, absorbing
//               leftover punctuation or one short word (≤ 3 letters) between them
//   sentences — like phrases, and a sentence that is mostly rewritten is shown
//               whole: the old sentence struck, then the new one
const STYLES = ['chars', 'words', 'phrases', 'sentences'];

const runSize = r => Math.max(r.a1 - r.a0, r.b1 - r.b0);
const mergeRuns = (x, y) => ({ eq: false, a0: x.a0, a1: y.a1, b0: x.b0, b1: y.b1 });
// A change that only moves line or paragraph breaks around.
const isLayout = (r, a, b) => {
  if (r.eq) return false;
  const ta = a.slice(r.a0, r.a1), tb = b.slice(r.b0, r.b1);
  return !/\S/.test(ta) && !/\S/.test(tb) && (ta + tb).includes('\n');
};

// Join neighbouring runs of the same kind and drop empty ones. A pure layout
// change stays apart from word changes.
function normaliseRuns(runs, a, b) {
  const out = [];
  for (const r of runs) {
    if (r.a1 === r.a0 && r.b1 === r.b0) continue;
    const prev = out[out.length - 1];
    if (prev && prev.eq === r.eq && (r.eq || (isLayout(prev, a, b) === isLayout(r, a, b) && prev.fine === r.fine && prev.whole === r.whole))) {
      prev.a1 = r.a1; prev.b1 = r.b1;
      continue;
    }
    out.push({ ...r });
  }
  return out;
}

// Absorb an equality sitting between two changes when keep(text, prev, next)
// says so. Never across a line break, never into a pure layout change.
function absorb(runs, a, b, keep) {
  const out = [];
  for (let k = 0; k < runs.length; k++) {
    const r = runs[k], prev = out[out.length - 1], next = runs[k + 1];
    if (r.eq && prev && !prev.eq && next && !next.eq && !isLayout(prev, a, b) && !isLayout(next, a, b)) {
      const t = a.slice(r.a0, r.a1);
      if (!t.includes('\n') && keep(t, prev, next)) { prev.a1 = r.a1; prev.b1 = r.b1; continue; }
    }
    if (!r.eq && prev && !prev.eq && !isLayout(r, a, b) && !isLayout(prev, a, b)) {
      prev.a1 = r.a1; prev.b1 = r.b1;
      continue;
    }
    out.push({ ...r });
  }
  return out;
}

const wordCount = t => (t.match(/[\p{L}\p{N}]+/gu) || []).length;

function shapeRuns(runs, a, b, style, fmtA, fmtB, letters) {
  runs = normaliseRuns(splitLayout(normaliseRuns(runs, a, b), a, b), a, b);
  const refine = rs => normaliseRuns(rs.flatMap(r => (r.eq || r.whole || isLayout(r, a, b) ? [r] : refineRun(r, a, b, fmtA, fmtB, letters))), a, b);
  if (style === 'words') return joinBreaks(refine(runs), a, b);
  if (style === 'chars') {
    return joinBreaks(absorb(runs, a, b, (t, p, n) => /^\s+$/.test(t) || t.length <= Math.min(runSize(p), runSize(n))), a, b);
  }
  // Phrases: absorb whitespace, and leftover punctuation or one short word
  // (like "a", "we", "das") that is smaller than the changes on both sides and
  // doesn't end a sentence. Longer words stay visible as unchanged.
  const keep = (t, p, n) => /^\s+$/.test(t) || (!/[.!?…]\s/.test(t) &&
    (t.match(/[\p{L}\p{N}]/gu) || []).length <= 3 && wordCount(t) <= 1 &&
    t.trim().length <= Math.min(runSize(p), runSize(n)));
  for (let before = -1; before !== runs.length;) {
    before = runs.length;
    runs = normaliseRuns(absorb(runs, a, b, keep), a, b);
  }
  if (style === 'sentences') runs = wholeSentences(runs, a, b, 0.5);
  return joinBreaks(refine(runs), a, b);
}

// Line breaks at the edge of a word change become a layout change of their own,
// so "Endlich" → "¶ Schlussendlich" reads as a paragraph break followed by
// "[-Endlich-] {+Schlussendlich+}", not as a break between old and new word.
function splitLayout(runs, a, b) {
  const out = [];
  for (const r of runs) {
    if (r.eq || isLayout(r, a, b)) { out.push(r); continue; }
    let { a0, a1, b0, b1 } = r;
    const lead = (s, e, t) => /^\s*/.exec(t.slice(s, e))[0].length;
    const trail = (s, e, t) => /\s*$/.exec(t.slice(s, e))[0].length;
    const la = lead(a0, a1, a), lb = lead(b0, b1, b);
    if ((a.slice(a0, a0 + la) + b.slice(b0, b0 + lb)).includes('\n')) {
      out.push({ eq: false, a0, a1: a0 + la, b0, b1: b0 + lb });
      a0 += la; b0 += lb;
    }
    const ta = trail(a0, a1, a), tb = trail(b0, b1, b);
    let tail = null;
    if ((a.slice(a1 - ta, a1) + b.slice(b1 - tb, b1)).includes('\n')) {
      tail = { eq: false, a0: a1 - ta, a1, b0: b1 - tb, b1 };
      a1 -= ta; b1 -= tb;
    }
    out.push({ ...r, a0, a1, b0, b1 });
    if (tail) out.push(tail);
  }
  return out;
}

// A layout change takes in the unchanged line breaks right next to it, so one
// added newline next to an existing one renders as "¶" + a real paragraph
// break instead of two loose line breaks.
function joinBreaks(runs, a, b) {
  const out = runs.map(r => ({ ...r }));
  for (let k = 0; k < out.length; k++) {
    const r = out[k];
    if (!isLayout(r, a, b)) continue;
    const prev = out[k - 1], next = out[k + 1];
    if (prev && prev.eq) {
      const ws = /\s*$/.exec(a.slice(prev.a0, prev.a1))[0];
      if (ws.includes('\n')) { prev.a1 -= ws.length; prev.b1 -= ws.length; r.a0 -= ws.length; r.b0 -= ws.length; }
    }
    if (next && next.eq) {
      const ws = /^\s*/.exec(a.slice(next.a0, next.a1))[0];
      if (ws.includes('\n')) { next.a0 += ws.length; next.b0 += ws.length; r.a1 += ws.length; r.b1 += ws.length; }
    }
  }
  return normaliseRuns(out, a, b);
}

// Inside one changed stretch, line the words up again. An identical word longer
// than three letters becomes unchanged (the plain diff can miss it when matching
// spaces scores the same), and with letters on, a word that is only slightly
// off gets a letter-level diff: "dies[-es-]{+em+}" instead of the whole word.
let fineId = 0;
function refineRun(r, a, b, fmtA, fmtB, letters) {
  const da = a.slice(r.a0, r.a1), db = b.slice(r.b0, r.b1);
  const D = tokenize(da, 'word'), I = tokenize(db, 'word');
  const words = T => T.tokens.map((t, i) => i).filter(i => /[\p{L}\p{N}]/u.test(T.tokens[i]));
  const dw = words(D), iw = words(I);
  if (!dw.length || !iw.length || dw.length * iw.length > 40000) return [r];

  const sameFmt = (ao, bo, len) => {
    for (let k = 0; k < len; k++) if (((fmtA && fmtA[ao + k]) || 0) !== ((fmtB && fmtB[bo + k]) || 0)) return false;
    return true;
  };
  // Score for pairing word x (in D) with word y (in I); 0 = cannot pair.
  const pairs = new Map();
  const pair = (i, j) => {
    const key = i * 65536 + j;
    if (pairs.has(key)) return pairs.get(key);
    const x = D.tokens[dw[i]], y = I.tokens[iw[j]];
    const ao = r.a0 + D.starts[dw[i]], bo = r.b0 + I.starts[iw[j]];
    let result = null;
    if (x === y) {
      if ((x.match(/[\p{L}\p{N}]/gu) || []).length > 3 && sameFmt(ao, bo, x.length)) result = { score: 2 * x.length };
    } else if (letters && sameFmt(ao, bo, Math.min(x.length, y.length))) {
      const fine = letterDiff(x, y);
      if (fine) result = { score: fine.common, fine: fine.runs };
    }
    pairs.set(key, result);
    return result;
  };

  // Weighted longest common subsequence over the words.
  const n = dw.length, m = iw.length, W = m + 1;
  const best = new Float64Array((n + 1) * (m + 1));
  for (let i = n - 1; i >= 0; i--) {
    for (let j = m - 1; j >= 0; j--) {
      let v = Math.max(best[(i + 1) * W + j], best[i * W + j + 1]);
      const p = pair(i, j);
      if (p) v = Math.max(v, best[(i + 1) * W + j + 1] + p.score);
      best[i * W + j] = v;
    }
  }
  if (!best[0]) return [r];

  const out = [];
  let ca = 0, cb = 0;
  // The text between two paired words: shared leading/trailing spaces stay
  // unchanged, the rest is one change.
  const gap = (ea, eb) => {
    const ga = da.slice(ca, ea), gb = db.slice(cb, eb);
    if (ga === gb) { if (ga) out.push({ eq: true, a0: r.a0 + ca, a1: r.a0 + ea, b0: r.b0 + cb, b1: r.b0 + eb }); return; }
    const lead = Math.min(/^[^\S\n]*/.exec(ga)[0].length, /^[^\S\n]*/.exec(gb)[0].length);
    let trail = Math.min(/[^\S\n]*$/.exec(ga)[0].length, /[^\S\n]*$/.exec(gb)[0].length);
    trail = Math.min(trail, ga.length - lead, gb.length - lead);
    const a0 = r.a0 + ca, b0 = r.b0 + cb, a1 = r.a0 + ea, b1 = r.b0 + eb;
    if (lead) out.push({ eq: true, a0, a1: a0 + lead, b0, b1: b0 + lead });
    out.push({ eq: false, a0: a0 + lead, a1: a1 - trail, b0: b0 + lead, b1: b1 - trail });
    if (trail) out.push({ eq: true, a0: a1 - trail, a1, b0: b1 - trail, b1 });
  };
  for (let i = 0, j = 0; i < n && j < m;) {
    const p = pair(i, j);
    if (p && best[i * W + j] === best[(i + 1) * W + j + 1] + p.score) {
      const sa = D.starts[dw[i]], sb = I.starts[iw[j]];
      gap(sa, sb);
      const ea = sa + D.tokens[dw[i]].length, eb = sb + I.tokens[iw[j]].length;
      if (!p.fine) {
        out.push({ eq: true, a0: r.a0 + sa, a1: r.a0 + ea, b0: r.b0 + sb, b1: r.b0 + eb });
      } else {
        const id = ++fineId;
        for (const f of p.fine) {
          out.push({ eq: f.eq, a0: r.a0 + sa + f.a0, a1: r.a0 + sa + f.a1, b0: r.b0 + sb + f.b0, b1: r.b0 + sb + f.b1, fine: f.eq ? undefined : id });
        }
      }
      ca = ea; cb = eb;
      i++; j++;
    } else if (best[i * W + j] === best[(i + 1) * W + j]) {
      i++;
    } else {
      j++;
    }
  }
  gap(da.length, db.length);
  return out.filter(x => x.a1 > x.a0 || x.b1 > x.b0);
}

// Letter-level diff of two words, or null when they are too different for it
// to help: words under four letters, more than two changed spots, or more than
// a third of the letters changed.
function letterDiff(x, y) {
  const L = Math.max(x.length, y.length);
  if (L < 4) return null;
  const A = tokenize(x, 'char'), B = tokenize(y, 'char');
  const [ia, ib] = intern(A.tokens, B.tokens);
  const runs = absorb(normaliseRuns(toRuns(diffTokens(ia, ib, false), A, B), x, y), x, y,
    (t, p, n) => t.length <= Math.min(runSize(p), runSize(n)));
  const changes = runs.filter(q => !q.eq);
  const changed = changes.reduce((k, q) => {
    const del = x.slice(q.a0, q.a1), ins = y.slice(q.b0, q.b1);
    const variant = spelled(del) === spelled(ins);
    return k + (variant ? (del + ins).toLowerCase().replace(/[^äöüß]/g, '').length : Math.max(del.length, ins.length));
  }, 0);
  if (!changes.length || changes.length > 2 || changed > Math.max(1, Math.floor(L / 3))) return null;
  return { runs, common: L - changed };
}
// ss/ß and umlauts typed without an umlaut key (ue, ae, oe) count as one letter each.
const spelled = t => t.toLowerCase().replace(/ä/g, 'ae').replace(/ö/g, 'oe').replace(/ü/g, 'ue').replace(/[ßẞ]/g, 'ss');

// Split the text at sentence ends and line breaks (only where both versions
// agree), then replace every sentence that is at least `threshold` rewritten
// and has more than one change as a whole.
const SENTENCE_END = /[.!?…]["'»«“”)\]]*[^\S\n]+|\n+/g;
function wholeSentences(runs, a, b, threshold) {
  const pieces = [];
  for (const r of runs) {
    if (!r.eq) { pieces.push(r); continue; }
    const t = a.slice(r.a0, r.a1);
    let last = 0, m;
    SENTENCE_END.lastIndex = 0;
    while ((m = SENTENCE_END.exec(t))) {
      const cut = m.index + m[0].length;
      pieces.push({ eq: true, a0: r.a0 + last, a1: r.a0 + cut, b0: r.b0 + last, b1: r.b0 + cut, end: true });
      last = cut;
    }
    if (last < t.length) pieces.push({ eq: true, a0: r.a0 + last, a1: r.a1, b0: r.b0 + last, b1: r.b1 });
  }

  const out = [];
  let sentence = [];
  const flush = () => {
    if (!sentence.length) return;
    const first = sentence[0], last = sentence[sentence.length - 1];
    const changes = sentence.filter(r => !r.eq);
    const changed = changes.reduce((n, r) => n + runSize(r), 0);
    const total = Math.max(last.a1 - first.a0, last.b1 - first.b0);
    if (changes.length > 1 && changed >= threshold * total) {
      // Keep the space after the sentence outside the replacement.
      const ws = last.eq ? /\s*$/.exec(a.slice(last.a0, last.a1))[0].length : 0;
      out.push({ eq: false, a0: first.a0, a1: last.a1 - ws, b0: first.b0, b1: last.b1 - ws, whole: true });
      if (ws) out.push({ eq: true, a0: last.a1 - ws, a1: last.a1, b0: last.b1 - ws, b1: last.b1 });
    } else {
      out.push(...sentence);
    }
    sentence = [];
  };
  for (const p of pieces) {
    if (isLayout(p, a, b)) { flush(); out.push(p); continue; }
    sentence.push(p);
    if (p.end) flush();
  }
  flush();
  return normaliseRuns(out, a, b);
}

// Pull [[notes]] out of the correction so they are not diffed. Returns the text
// without notes, a map from its indices back to the raw text, and the notes with
// their anchor position. A note alone on its line becomes a "block" note and its
// line is removed without disturbing the paragraph structure.
const NOTE_RE = /\[\[([\s\S]*?)\]\]/g;

function extractNotes(raw) {
  const found = [];
  NOTE_RE.lastIndex = 0;
  let m;
  while ((m = NOTE_RE.exec(raw))) {
    found.push({ s: m.index, e: m.index + m[0].length, text: m[1].trim(), multiline: m[1].includes('\n') });
  }
  if (!found.length) return { text: raw, map: null, notes: [] };

  for (const f of found) {
    f.ls = raw.lastIndexOf('\n', f.s - 1) + 1;
    const le = raw.indexOf('\n', f.e);
    f.le = le < 0 ? raw.length : le;
  }
  for (const f of found) {
    if (f.multiline) { f.block = false; continue; }
    let rest = '', cur = f.ls, ok = true;
    for (const g of found) {
      if (g.e <= f.ls || g.s >= f.le) continue;
      if (g.multiline) { ok = false; break; }
      rest += raw.slice(cur, g.s);
      cur = g.e;
    }
    rest += raw.slice(cur, f.le);
    f.block = ok && !/\S/.test(rest);
  }

  let out = '', cur = 0;
  const map = [], notes = [];
  const copy = (from, to) => {
    out += raw.slice(from, to);
    for (let k = from; k < to; k++) map.push(k);
  };
  const countNl = s => (s.match(/\n/g) || []).length;

  let i = 0;
  while (i < found.length) {
    const f = found[i];
    if (f.block) {
      let j = i;
      while (j + 1 < found.length && found[j + 1].block && !/\S/.test(raw.slice(found[j].le, found[j + 1].ls))) j++;
      const first = found[i], last = found[j];
      const before = raw.slice(0, first.ls), after = raw.slice(last.le);
      const hasPrev = /\S/.test(before);
      const nextRel = after.search(/\S/);
      const hasNext = nextRel >= 0;
      const r0 = hasPrev ? raw.indexOf('\n', before.search(/\s*$/)) : 0;
      const r1 = hasNext ? raw.lastIndexOf('\n', last.le + nextRel - 1) + 1 : raw.length;
      const p = countNl(raw.slice(r0, first.ls)), q = countNl(raw.slice(last.le, r1));
      const keep = hasPrev && hasNext ? Math.max(p, q) : 0;
      const kind = hasNext ? (q >= 2 ? 'para' : 'before') : (hasPrev && p < 2 ? 'after' : 'para');
      copy(cur, r0);
      for (let x = r0, k = keep; x < r1 && k > 0; x++) {
        if (raw[x] === '\n') { out += '\n'; map.push(x); k--; }
      }
      for (let g = i; g <= j; g++) {
        notes.push({ text: found[g].text, s: found[g].s, e: found[g].e, kind, pre: '', post: '', pos: out.length });
      }
      cur = r1;
      i = j + 1;
      continue;
    }

    // Inline note: swallow the space in front of it ("went [[note]] home" → "went home").
    copy(cur, f.s);
    let end = f.e, pre = '', post = '';
    const lineSoFar = out.slice(out.lastIndexOf('\n') + 1);
    if (/\S/.test(lineSoFar)) {
      const ws = /[^\S\n]*$/.exec(lineSoFar)[0].length;
      if (ws) { out = out.slice(0, out.length - ws); map.length -= ws; }
      pre = ' ';
    } else {
      const wsRe = /[^\S\n]*/y;
      wsRe.lastIndex = f.e;
      end = f.e + wsRe.exec(raw)[0].length;
      let nl = raw.indexOf('\n', end);
      if (nl < 0) nl = raw.length;
      post = /\S/.test(raw.slice(end, nl)) ? ' ' : '';
    }
    notes.push({ text: f.text, s: f.s, e: f.e, kind: 'inline', pre, post, pos: out.length });
    cur = end;
    i++;
  }
  copy(cur, raw.length);
  return { text: out, map, notes };
}

// "[? … ?]" marks a passage the teacher can't follow. The markers (and the
// spaces just inside them) are removed before diffing, like notes; the
// passage itself is diffed normally and later shown in yellow.
const UNCLEAR_RE = /\[\?[^\S\n]*([\s\S]*?)[^\S\n]*\?\]/g;
function findUnclear(text) {
  const found = [];
  UNCLEAR_RE.lastIndex = 0;
  let m;
  while ((m = UNCLEAR_RE.exec(text))) {
    const open = /^\[\?[^\S\n]*/.exec(m[0])[0].length;
    const close = m[1] ? /[^\S\n]*\?\]$/.exec(m[0])[0].length : m[0].length - open;
    found.push({ s: m.index, e: m.index + m[0].length, open, close });
  }
  return found;
}

// Remove the markers from the note-free text. Returns the new text, its map back
// to the raw correction, notes moved to the new positions, the marked ranges in
// the new text, and the raw ranges (markers included) for the editor highlight.
function extractUnclear(text, map, notes) {
  const found = findUnclear(text);
  if (!found.length) return { text, map, notes, ranges: [], raw: [] };
  const keep = new Uint8Array(text.length).fill(1);
  for (const f of found) {
    keep.fill(0, f.s, f.s + f.open);
    keep.fill(0, f.e - f.close, f.e);
  }
  const index = new Int32Array(text.length + 1);
  const newMap = [];
  let out = '';
  for (let i = 0; i < text.length; i++) {
    index[i] = newMap.length;
    if (keep[i]) { out += text[i]; newMap.push(map ? map[i] : i); }
  }
  index[text.length] = newMap.length;
  const raw = i => (map ? map[i] : i);
  for (const n of notes) n.pos = index[Math.min(n.pos, text.length)];
  return {
    text: out,
    map: newMap,
    notes,
    ranges: found.map(f => ({ start: index[f.s + f.open], end: index[f.e - f.close] })).filter(r => r.end > r.start),
    raw: found.map(f => [raw(f.s), raw(f.e - 1) + 1]),
  };
}

// Interleave notes with the diff runs at their anchor positions.
function buildSegments(runs, a, b, notes, ranges = []) {
  const segs = [];
  const cuts = [...new Set(ranges.flatMap(r => [r.start, r.end]))].sort((x, y) => x - y);
  let ni = 0;
  const flush = p => { while (ni < notes.length && notes[ni].pos <= p) segs.push({ t: 'note', note: notes[ni++] }); };
  const emitB = (t, b0, b1, fine) => {
    flush(b0);
    let cur = b0;
    const upTo = to => { if (to > cur) { segs.push({ t, b0: cur, b1: to, text: b.slice(cur, to), fine }); cur = to; } };
    for (;;) {
      const note = ni < notes.length ? notes[ni].pos : Infinity;
      const cut = cuts.find(c => c > cur);
      const p = Math.min(note, cut === undefined ? Infinity : cut);
      if (p >= b1) break;
      upTo(p);
      if (p === note) flush(p);
    }
    upTo(b1);
  };
  for (const r of runs) {
    if (r.eq) { emitB('eq', r.b0, r.b1); continue; }
    if (r.a1 > r.a0) { flush(r.b0); segs.push({ t: 'del', a0: r.a0, a1: r.a1, at: r.b0, text: a.slice(r.a0, r.a1), fine: r.fine }); }
    if (r.b1 > r.b0) emitB('ins', r.b0, r.b1, r.fine);
  }
  flush(Infinity);
  return segs;
}

// A token's identity includes its formatting, so making a word bold is a change.
// Formatting on whitespace is ignored.
function tokenKeys(T, fmt) {
  if (!fmt) return T.tokens;
  return T.tokens.map((tok, i) => {
    if (/^\s+$/.test(tok)) return tok;
    const s = T.starts[i];
    let sig = String(fmt[s] || 0);
    for (let k = 1; k < tok.length; k++) {
      if ((fmt[s + k] || 0) !== (fmt[s] || 0)) {
        sig = '';
        for (let j = 0; j < tok.length; j++) sig += (fmt[s + j] || 0) + ',';
        break;
      }
    }
    return sig === '0' ? tok : tok + '\u0001' + sig;
  });
}

// orig and corr are { text, fmt } — fmt (optional) holds the format bits of each
// character of text.
function computeDiff(orig, corr, opts) {
  const style = STYLES.includes(opts.style) ? opts.style : 'phrases';
  const mode = style === 'chars' ? 'char' : 'word';
  const notesOnly = extractNotes(corr.text);
  const ex = extractUnclear(notesOnly.text, notesOnly.map, notesOnly.notes);
  const fmtA = orig.fmt || null;
  const fmtB = corr.fmt ? (ex.map ? ex.map.map(i => corr.fmt[i]) : corr.fmt) : null;
  const a = orig.text.replace(/\s+$/, '');
  const b = ex.text.replace(/\s+$/, '');
  for (const n of ex.notes) if (n.pos > b.length) n.pos = b.length;
  const unclear = ex.ranges.map(r => ({ start: Math.min(r.start, b.length), end: Math.min(r.end, b.length) })).filter(r => r.end > r.start);

  const A = tokenize(a, mode), B = tokenize(b, mode);
  const [ia, ib] = intern(tokenKeys(A, fmtA), tokenKeys(B, fmtB));
  let runs = toRuns(diffTokens(ia, ib), A, B);
  runs = shapeRuns(runs, a, b, style, fmtA, fmtB, style !== 'chars' && opts.letters !== false);
  const segs = buildSegments(runs, a, b, ex.notes, unclear);

  // Per-character marks for highlighting inside the two editors.
  const origMarks = new Uint8Array(orig.text.length);
  const corrMarks = new Uint8Array(corr.text.length);
  for (const s of segs) {
    if (s.t === 'del') origMarks.fill(1, s.a0, s.a1);
    else if (s.t === 'ins') for (let i = s.b0; i < s.b1; i++) corrMarks[ex.map ? ex.map[i] : i] = 2;
  }
  for (const n of ex.notes) corrMarks.fill(3, n.s, n.e);

  return {
    segs,
    mode,
    changes: runs.filter(r => !r.eq && !r.fine).length + new Set(runs.filter(r => r.fine).map(r => r.fine)).size,
    notes: ex.notes.filter(n => n.text).length,
    unclear: unclear.length,
    unclearRanges: unclear,
    unclearRaw: ex.raw,
    empty: !a && !b && !ex.notes.some(n => n.text),
    original: a,
    corrected: b,
    fmtA,
    fmtB,
    origMarks,
    corrMarks,
  };
}

const isCJK = ch => !!ch && CJK_RE.test(ch);
const lastChar = s => { const arr = Array.from(s); return arr[arr.length - 1]; };

// HTML for a piece of text without line breaks; fmt[offset + i] formats text[i].
function fmtHTML(text, fmt, offset) {
  if (!fmt) return esc(text);
  let html = '';
  for (let i = 0; i < text.length;) {
    const f = fmt[offset + i] || 0;
    let j = i + 1;
    while (j < text.length && (fmt[offset + j] || 0) === f) j++;
    let chunk = esc(text.slice(i, j));
    for (const [bit, tag] of FORMAT_TAGS) if (f & bit) chunk = `<${tag}>${chunk}</${tag}>`;
    html += chunk;
    i = j;
  }
  return html;
}

function renderDiffHTML(diff) {
  const { segs, mode, fmtA, fmtB } = diff;
  const ranges = diff.unclearRanges || [];
  const wordPad = mode === 'word' ? ';padding:1px 2px' : '';
  const pad = wordPad;
  const paras = [[]];
  let cur = paras[0];

  // Unclear passages: a yellow span with "? … ?" inside it. A span can't cross
  // paragraphs, so it is closed and reopened at paragraph breaks.
  const U_OPEN = `<span style='${STYLE.unclear}'>`, U_CLOSE = '</span>';
  const Q = `<strong style='${STYLE.unclearMark}'>?</strong>`;
  let unclear = false;
  const setUnclear = on => {
    if (on === unclear) return;
    cur.push(on ? `${U_OPEN}${Q} ` : ` ${Q}${U_CLOSE}`);
    unclear = on;
  };
  const inside = p => ranges.some(r => r.start <= p && p < r.end);
  const newPara = () => {
    if (unclear) cur.push(U_CLOSE);
    if (cur.length) { cur = []; paras.push(cur); }
    if (unclear) cur.push(U_OPEN);
  };

  const pushText = (text, fmt, offset) => {
    const re = /\n(?:[^\S\n]*\n)+|\n/g;
    let last = 0, m;
    while ((m = re.exec(text))) {
      if (m.index > last) cur.push(fmtHTML(text.slice(last, m.index), fmt, offset + last));
      if (m[0] === '\n') cur.push('<br>'); else newPara();
      last = m.index + m[0].length;
    }
    if (last < text.length) cur.push(fmtHTML(text.slice(last), fmt, offset + last));
  };
  // Keep spaces at the edges of a change outside the colored box, so
  // "to{+ the+} school" renders as "to {the} school". Line breaks inside a
  // change show as ¶; an added paragraph break also starts a new paragraph.
  const BREAKS = /\n(?:[^\S\n]*\n)+|\n/g;
  const change = (tag, text, fmt, offset, fine) => {
    const pad = fine ? '' : wordPad;
    let lead = '', core = text, trail = '';
    if (/\S/.test(text)) {
      const m = /^([^\S\n]*)([\s\S]*?)([^\S\n]*)$/.exec(text);
      lead = m[1]; core = m[2]; trail = m[3];
    }
    const open = `<${tag} style='${STYLE[tag]}${pad}'>`, close = `</${tag}>`;
    if (lead) cur.push(esc(lead));
    let inner = '', from = 0, m;
    const base = offset + lead.length;
    BREAKS.lastIndex = 0;
    while ((m = BREAKS.exec(core))) {
      inner += fmtHTML(core.slice(from, m.index), fmt, base + from) + '¶';
      from = m.index + m[0].length;
      if (tag === 'ins') {
        cur.push(open + inner + close);
        if (m[0] === '\n') cur.push('<br>'); else newPara();
        inner = '';
      }
    }
    inner += fmtHTML(core.slice(from), fmt, base + from);
    if (inner) cur.push(open + inner + close);
    if (trail) cur.push(esc(trail));
  };
  // Only line breaks moved: show a single ¶ instead of coloured whitespace.
  const layout = (del, ins) => {
    const added = (ins.match(/\n/g) || []).length, removed = (del.match(/\n/g) || []).length;
    const paragraph = /\n[^\S\n]*\n/.test(ins);
    if (added > removed) {
      cur.push(`<ins style='${STYLE.ins}${pad}'>¶</ins>`);
      if (paragraph) newPara(); else cur.push('<br>');
    } else if (added < removed) {
      cur.push(`<del style='${STYLE.del}${pad}'>¶</del>`);
      cur.push(added ? '<br>' : ' ');
    } else if (paragraph) {
      newPara();
    } else {
      cur.push('<br>');
    }
  };
  const blank = t => !/\S/.test(t);
  const noteHTML = n => `<em style='${STYLE.note}'>${esc(n.text).replace(/\n/g, '<br>')}</em>`;

  for (let k = 0; k < segs.length; k++) {
    const s = segs[k];
    setUnclear(inside(s.t === 'del' ? s.at : s.t === 'note' ? s.note.pos : s.b0));
    if (s.t === 'eq') {
      pushText(s.text, fmtB, s.b0);
    } else if (s.t === 'del' || s.t === 'ins') {
      const nx = segs[k + 1];
      const del = s.t === 'del' ? s.text : '', ins = s.t === 'ins' ? s.text : nx && nx.t === 'ins' ? nx.text : '';
      const pairs = s.t === 'del' && nx && nx.t === 'ins';
      if (blank(del) && blank(ins) && (del + ins).includes('\n')) {
        layout(del, ins);
        if (pairs) k++;
        continue;
      }
      if (s.t === 'ins') { change('ins', s.text, fmtB, s.b0, s.fine); continue; }
      change('del', s.text, fmtA, s.a0, s.fine);
      const punctuation = t => !/[\p{L}\p{N}\s]/u.test(t);
      if (mode === 'word' && !s.fine && nx && nx.t === 'ins' && !/\s$/.test(s.text) && !/^\s/.test(nx.text) &&
          !(punctuation(s.text) && punctuation(nx.text)) &&
          !(isCJK(lastChar(s.text)) && isCJK(Array.from(nx.text)[0]))) {
        cur.push(' ');
      }
    } else if (s.t === 'note' && s.note.text) {
      const n = s.note;
      if (n.kind === 'para') { newPara(); cur.push(noteHTML(n)); newPara(); }
      else if (n.kind === 'before') cur.push(noteHTML(n), '<br>');
      else if (n.kind === 'after') cur.push('<br>', noteHTML(n));
      else cur.push(esc(n.pre) + noteHTML(n) + esc(n.post));
    }
  }
  setUnclear(false);
  return paras.filter(p => p.some(x => x !== U_OPEN && x !== U_CLOSE)).map(p => `<p>${p.join('')}</p>`).join('\n');
}

// Formatted text as HTML: blank lines start a paragraph, single newlines become
// <br>. With inline set, a single paragraph comes back without its <p>.
function modelToHTML(text, fmt, inline) {
  const start = text.search(/\S/);
  if (start < 0) return '';
  const end = text.replace(/\s+$/, '').length;
  const para = (s, e) => {
    const lines = [];
    let o = s;
    for (const line of text.slice(s, e).split('\n')) {
      lines.push(fmtHTML(line, fmt, o));
      o += line.length + 1;
    }
    return lines.join('<br>');
  };
  const paras = [];
  const re = /\n(?:[^\S\n]*\n)+/g;
  re.lastIndex = start;
  let from = start, m;
  while ((m = re.exec(text)) && m.index < end) {
    paras.push(para(from, m.index));
    from = m.index + m[0].length;
  }
  paras.push(para(from, end));
  return inline && paras.length === 1 ? paras[0] : paras.map(p => `<p>${p}</p>`).join('');
}

// A collapsed section the student can open. Moodle 6.0+ keeps <details>; older
// versions strip the tags, which leaves the bold title above the indented text.
function sectionHTML(title, html, open) {
  return `<details style='${STYLE.details}'${open ? ' open' : ''}>` +
    `<summary style='${STYLE.summary}'><strong>${esc(title)}</strong></summary>` +
    `<div style='${STYLE.sectionBody}'>${html}</div>` +
    `</details>`;
}

function legendHTML(del, ins, note, unclear) {
  const q = `<strong style='${STYLE.unclearMark}'>?</strong>`;
  return `<p style='${STYLE.legend}'>` +
    `<del style='${STYLE.del};padding:1px 2px'>${esc(del)}</del>&nbsp; ` +
    `<ins style='${STYLE.ins};padding:1px 2px'>${esc(ins)}</ins>&nbsp; ` +
    `<em style='${STYLE.note}'>${esc(note)}</em>` +
    (unclear ? `&nbsp; <span style='${STYLE.unclear}'>${q} ${esc(unclear)} ${q}</span>` : '') + '</p>';
}

const api = {
  esc, STYLE, STYLES, BOLD, ITALIC, UNDERLINE,
  extractNotes, findUnclear, computeDiff, renderDiffHTML, modelToHTML, sectionHTML, legendHTML,
};
root.CorrectionDiff = api;
if (typeof module === 'object' && module.exports) module.exports = api;
})(typeof globalThis !== 'undefined' ? globalThis : this);
