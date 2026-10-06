/* Correction Diff — page behaviour.
   Needs assets/vendor/nunjucks.min.js and assets/diff-engine.js loaded first. */
(() => {
'use strict';

const CD = window.CorrectionDiff;
const { esc, STYLE, BOLD, ITALIC, UNDERLINE } = CD;

/* ---------- Storage ---------- */

const KEYS = {
  state: 'correction-diff/state',
  settings: 'correction-diff/settings',
  signature: 'correction-diff/signature-html',
  oldSignature: 'correction-diff/signature',
  template: 'correction-diff/template',
};
const store = {
  get(key, fallback) {
    try { const v = localStorage.getItem(key); return v == null ? fallback : JSON.parse(v); } catch { return fallback; }
  },
  set(key, value) {
    try { localStorage.setItem(key, JSON.stringify(value)); } catch { /* private mode or blocked storage */ }
  },
  remove(key) {
    try { localStorage.removeItem(key); } catch { /* ignore */ }
  },
};

const DEFAULTS = { style: 'phrases', letters: true, syncScroll: true };
const settings = { ...DEFAULTS };
const savedSettings = store.get(KEYS.settings, {});
for (const key of Object.keys(DEFAULTS)) if (key in savedSettings) settings[key] = savedSettings[key];
if (!('style' in savedSettings)) {
  // Earlier versions had "compare by characters" and "group changes" switches.
  if (savedSettings.granularity === 'char') settings.style = 'chars';
  else if (savedSettings.group === false) settings.style = 'words';
}

const DEFAULT_TEMPLATE = `{{ diff }}

{{ original | collapsible("Original text") }}
{{ corrected | collapsible("Corrected text") }}

{% if feedback %}
<hr>
<h3>Feedback</h3>
{{ feedback }}
{% endif %}

{{ signature }}
`;

/* ---------- Elements ---------- */

const $ = id => document.getElementById(id);
const orig = $('orig'), corr = $('corr'), feedback = $('feedback'), signature = $('signature');
const preview = $('preview'), stats = $('stats');
const EDITORS = [orig, corr, feedback, signature];
// Feedback and signature allow lists and links; the two texts only inline formatting.
const isRich = el => el === feedback || el === signature;

/* ---------- Reading formatted text ---------- */

const BLOCK = new Set(['ADDRESS', 'ARTICLE', 'ASIDE', 'BLOCKQUOTE', 'DD', 'DETAILS', 'DIV', 'DL', 'DT', 'FIELDSET',
  'FIGCAPTION', 'FIGURE', 'FOOTER', 'FORM', 'H1', 'H2', 'H3', 'H4', 'H5', 'H6', 'HEADER', 'LI', 'MAIN', 'NAV', 'OL',
  'P', 'PRE', 'SECTION', 'SUMMARY', 'TABLE', 'TBODY', 'TFOOT', 'THEAD', 'TR', 'UL']);
const LINE_BLOCKS = new Set(['LI', 'TR', 'DT', 'DD']);
const SKIP = new Set(['SCRIPT', 'STYLE', 'TEMPLATE', 'NOSCRIPT', 'HEAD', 'TITLE', 'META', 'LINK', 'IMG', 'SVG',
  'OBJECT', 'EMBED', 'IFRAME', 'VIDEO', 'AUDIO', 'CANVAS', 'INPUT', 'SELECT', 'TEXTAREA', 'BUTTON']);
const FORMAT_TAGS = [[BOLD, 'strong'], [ITALIC, 'em'], [UNDERLINE, 'u']];

const parseHTML = html => new DOMParser().parseFromString(html, 'text/html').body;

// Effective format of an element from its tag and inline style. Google Docs wraps
// everything in <b style="font-weight:normal">, so styles can switch bold off again.
function formatOf(el, f) {
  switch (el.tagName) {
    case 'B': case 'STRONG': case 'TH':
    case 'H1': case 'H2': case 'H3': case 'H4': case 'H5': case 'H6': f |= BOLD; break;
    case 'I': case 'EM': case 'CITE': case 'DFN': f |= ITALIC; break;
    case 'U': f |= UNDERLINE; break;
  }
  const st = el.style;
  if (st) {
    const fw = st.fontWeight;
    if (fw) {
      const n = fw === 'bold' || fw === 'bolder' ? 700 : fw === 'normal' || fw === 'lighter' ? 400 : parseInt(fw, 10);
      if (n >= 600) f |= BOLD; else if (n > 0) f &= ~BOLD;
    }
    if (st.fontStyle === 'italic' || st.fontStyle === 'oblique') f |= ITALIC;
    else if (st.fontStyle === 'normal') f &= ~ITALIC;
    if ((st.textDecorationLine || st.textDecoration || '').includes('underline')) f |= UNDERLINE;
  }
  return f;
}

// A <br> that only keeps an otherwise empty line open (as editors add at the end
// of a paragraph) is not a line break of its own.
function isPlaceholderBr(br, root, collapse) {
  for (let n = br; n && n !== root; n = n.parentNode) {
    for (let s = n.nextSibling; s; s = s.nextSibling) {
      if (s.nodeType === 3) {
        if (collapse ? /\S/.test(s.data) : s.data.length) return false;
      } else if (s.nodeType === 1) {
        if (BLOCK.has(s.tagName)) return true;
        if (s.tagName === 'BR' || s.textContent.length) return false;
      }
    }
    if (n.parentNode && BLOCK.has(n.parentNode.tagName)) return true;
  }
  return true;
}

// Flatten a DOM tree to { text, fmt }: paragraphs become blank lines, <br> a
// newline, lists "• " lines. With positions, also records the text node and
// offset behind every character, for highlighting. collapse applies HTML
// whitespace rules (for pasted HTML; the editors keep whitespace as typed).
function readModel(root, { collapse = false, positions = false } = {}) {
  const chars = [], fmt = [];
  const nodes = positions ? [] : null, offs = positions ? [] : null;
  let pending = 0;
  let prefix = null; // list bullet, written just before the item's first character
  const emit = (ch, f, node, off) => {
    chars.push(ch); fmt.push(f);
    if (positions) { nodes.push(node); offs.push(off); }
  };
  const popSpaces = () => {
    while (chars.length && chars[chars.length - 1] === ' ') {
      chars.pop(); fmt.pop();
      if (positions) { nodes.pop(); offs.pop(); }
    }
  };
  const flush = () => {
    if (pending && chars.length) for (let k = 0; k < pending; k++) emit('\n', 0, null, 0);
    pending = 0;
    if (prefix) { const p = prefix; prefix = null; for (const ch of p) emit(ch, 0, null, 0); }
  };
  const brk = n => {
    if (prefix) return; // paragraphs directly inside a list item
    if (collapse) popSpaces();
    if (n > pending) pending = n;
  };
  const text = (data, f, node) => {
    for (let i = 0; i < data.length; i++) {
      let ch = data[i];
      if (ch === '\r') continue;
      if (ch === ' ') ch = ' ';
      if (collapse && /\s/.test(ch)) {
        const last = chars[chars.length - 1];
        if (pending || prefix || !chars.length || last === ' ' || last === '\n') continue;
        ch = ' ';
      }
      flush();
      emit(ch, f, node, i);
    }
  };
  const walk = (node, f, inItem) => {
    if (node.nodeType === 3) { text(node.data, f, node); return; }
    if (node.nodeType !== 1 || SKIP.has(node.tagName)) return;
    const tag = node.tagName;
    if (tag === 'BR') {
      if (isPlaceholderBr(node, root, collapse)) return;
      if (collapse) popSpaces();
      flush();
      emit('\n', 0, null, 0);
      return;
    }
    if (tag === 'HR') { brk(2); return; }
    const nf = formatOf(node, f);
    const gap = BLOCK.has(tag) ? (LINE_BLOCKS.has(tag) || inItem ? 1 : 2) : 0;
    if (gap) brk(gap);
    if (tag === 'LI') {
      const list = node.parentElement;
      const n = list && list.tagName === 'OL' ? Array.from(list.children).filter(c => c.tagName === 'LI').indexOf(node) + 1 : 0;
      prefix = n ? `${n}. ` : '• ';
    } else if ((tag === 'TD' || tag === 'TH') && node.previousElementSibling) {
      text(' | ', 0, null);
    }
    for (let c = node.firstChild; c; c = c.nextSibling) walk(c, nf, inItem || tag === 'LI');
    if (tag === 'LI') prefix = null;
    if (gap) brk(gap);
  };
  for (let c = root.firstChild; c; c = c.nextSibling) walk(c, 0, false);
  return { text: chars.join(''), fmt: Uint8Array.from(fmt), nodes, offs };
}

// Clean rich HTML for the feedback and signature: paragraphs, line breaks,
// lists, links and bold/italic/underline survive; everything else is unwrapped.
// Works in an inert document, so pasted images or handlers never load or run.
function cleanRich(source, collapse) {
  const doc = document.implementation.createHTMLDocument('');
  const box = doc.createElement('div');
  for (const n of Array.from(source.childNodes)) box.appendChild(doc.importNode(n, true));
  richTransform(box, 0, collapse);
  let run = null;
  for (const n of Array.from(box.childNodes)) {
    if (/^(P|UL|OL|HR)$/.test(n.nodeName)) { run = null; continue; }
    if (!run) { run = doc.createElement('p'); n.before(run); }
    run.appendChild(n);
  }
  for (const el of Array.from(box.querySelectorAll('p, li'))) {
    while (el.lastChild && el.lastChild.nodeName === 'BR') el.lastChild.remove();
  }
  for (const p of Array.from(box.querySelectorAll('p'))) if (!p.textContent.trim()) p.remove();
  for (const p of Array.from(box.querySelectorAll('li > p:only-child'))) p.replaceWith(...p.childNodes);
  return box.innerHTML.trim();
}

function richTransform(el, f, collapse) {
  const doc = el.ownerDocument;
  for (const node of Array.from(el.childNodes)) {
    if (node.nodeType === 3) {
      let t = node.data.replace(/ /g, ' ').replace(/\r/g, '');
      if (collapse) t = t.replace(/\s+/g, ' ');
      if (!t) { node.remove(); continue; }
      let out = doc.createDocumentFragment();
      t.split('\n').forEach((line, i) => {
        if (i) out.appendChild(doc.createElement('br'));
        if (line) out.appendChild(doc.createTextNode(line));
      });
      for (const [bit, tag] of FORMAT_TAGS) {
        if (f & bit) { const w = doc.createElement(tag); w.appendChild(out); out = w; }
      }
      node.replaceWith(out);
      continue;
    }
    if (node.nodeType !== 1 || SKIP.has(node.tagName)) { node.remove(); continue; }
    const tag = node.tagName;
    if (tag === 'BR' || tag === 'HR') { node.replaceWith(doc.createElement(tag)); continue; }
    richTransform(node, formatOf(node, f), collapse);
    const href = (node.getAttribute('href') || '').trim();
    let out;
    if (tag === 'UL' || tag === 'OL' || tag === 'LI') out = doc.createElement(tag);
    else if (tag === 'A' && /^(https?:|mailto:)/i.test(href)) { out = doc.createElement('a'); out.setAttribute('href', href); }
    else if (BLOCK.has(tag) && !node.querySelector('p, ul, ol, li, hr')) out = doc.createElement('p');
    else out = doc.createDocumentFragment();
    while (node.firstChild) out.appendChild(node.firstChild);
    node.replaceWith(out);
  }
}

// Clean HTML for an editor, from pasted or stored HTML (or plain text).
function cleanFor(ed, html, text, collapse = true) {
  if (html) {
    const body = parseHTML(html);
    if (isRich(ed)) return cleanRich(body, collapse);
    const m = readModel(body, { collapse });
    return CD.modelToHTML(m.text, m.fmt, collapse);
  }
  return CD.modelToHTML((text || '').replace(/\r\n?/g, '\n'), null, collapse);
}

const isEmpty = el => !el.textContent.trim() && !el.querySelector('li');
const richValue = el => (isEmpty(el) ? '' : cleanRich(el, false));
const updateEmpty = el => el.classList.toggle('is-empty', isEmpty(el));

/* ---------- Restore saved work ---------- */

const saved = store.get(KEYS.state, null);
if (saved) {
  if (saved.v === 2) {
    orig.innerHTML = cleanFor(orig, saved.orig || '', '', false);
    corr.innerHTML = saved.corr === saved.orig ? orig.innerHTML : cleanFor(corr, saved.corr || '', '', false);
    feedback.innerHTML = cleanFor(feedback, saved.feedback || '', '', false);
  } else {
    // Version 1 stored plain text.
    orig.innerHTML = CD.modelToHTML(saved.orig || '', null);
    corr.innerHTML = saved.corr === saved.orig ? orig.innerHTML : CD.modelToHTML(saved.corr || '', null);
    feedback.innerHTML = CD.modelToHTML(saved.feedback || '', null);
  }
}
{
  const html = store.get(KEYS.signature, null);
  const old = html == null ? store.get(KEYS.oldSignature, '') : '';
  signature.innerHTML = html != null ? cleanFor(signature, html, '', false) : CD.modelToHTML(old, null);
}
let prevOrigHTML = orig.innerHTML;

try {
  document.execCommand('defaultParagraphSeparator', false, 'p');
  document.execCommand('styleWithCSS', false, false);
} catch { /* not supported */ }

/* ---------- Diff & highlights ---------- */

const MARK_DEL = 1, MARK_INS = 2, MARK_NOTE = 3;
const canHighlight = typeof Highlight === 'function' && window.CSS && CSS.highlights;

function rangesFor(model, marks, value) {
  const ranges = [];
  for (let i = 0; i < marks.length;) {
    const node = model.nodes[i];
    if (marks[i] !== value || !node) { i++; continue; }
    let j = i + 1;
    while (j < marks.length && marks[j] === value && model.nodes[j] === node && model.offs[j] === model.offs[j - 1] + 1) j++;
    const r = new Range();
    r.setStart(node, model.offs[i]);
    r.setEnd(node, model.offs[j - 1] + 1);
    ranges.push(r);
    i = j;
  }
  return ranges;
}

function paintHighlights(om, cm) {
  if (!canHighlight) return;
  if (!om) {
    for (const name of ['cd-del', 'cd-ins', 'cd-note']) CSS.highlights.delete(name);
    return;
  }
  CSS.highlights.set('cd-del', new Highlight(...rangesFor(om, diff.origMarks, MARK_DEL)));
  CSS.highlights.set('cd-ins', new Highlight(...rangesFor(cm, diff.corrMarks, MARK_INS)));
  CSS.highlights.set('cd-note', new Highlight(...rangesFor(cm, diff.corrMarks, MARK_NOTE)));
}

const segmenter = typeof Intl !== 'undefined' && Intl.Segmenter ? new Intl.Segmenter(undefined, { granularity: 'word' }) : null;
function countWords(text) {
  if (!text.trim()) return 0;
  if (segmenter) {
    let n = 0;
    for (const s of segmenter.segment(text)) if (s.isWordLike) n++;
    return n;
  }
  return (text.match(/[\p{L}\p{N}]+/gu) || []).length;
}
const plural = (n, one, many) => `${n} ${n === 1 ? one : many}`;

let diff = null;
const parts = { diff: '', original: '', corrected: '' };
let slowDiff = false, diffTimer = 0;

function recomputeDiff() {
  const t0 = performance.now();
  const om = readModel(orig, { positions: true });
  const cm = readModel(corr, { positions: true });
  diff = CD.computeDiff(om, cm, settings);
  parts.diff = diff.empty ? '' : CD.renderDiffHTML(diff);
  parts.original = CD.modelToHTML(diff.original, diff.fmtA);
  parts.corrected = CD.modelToHTML(diff.corrected, diff.fmtB);
  paintHighlights(om, cm);
  slowDiff = performance.now() - t0 > 30;

  updateEmpty(orig);
  updateEmpty(corr);
  $('count-orig').textContent = om.text.trim() ? plural(countWords(om.text), 'word', 'words') : '';
  $('count-corr').textContent = cm.text.trim() ? plural(countWords(CD.extractNotes(cm.text).text), 'word', 'words') : '';
  renderStats();
  renderOutput();
}

function scheduleDiff() {
  clearTimeout(diffTimer);
  if (!slowDiff) { recomputeDiff(); return; }
  // Very long texts: drop the stale highlights now, recolor once typing pauses.
  paintHighlights(null);
  diffTimer = setTimeout(recomputeDiff, 150);
}

function renderStats() {
  if (!diff || diff.empty) { stats.innerHTML = ''; return; }
  const chips = [diff.changes
    ? `<span class="chip"><i class="sw sw-ins"></i>${plural(diff.changes, 'correction', 'corrections')}</span>`
    : '<span class="chip">No changes yet</span>'];
  if (diff.notes) chips.push(`<span class="chip"><i class="sw sw-note"></i>${plural(diff.notes, 'note', 'notes')}</span>`);
  stats.innerHTML = chips.join('');
}

/* ---------- Output template ---------- */

const nunjucks = window.nunjucks;
const env = nunjucks ? new nunjucks.Environment([], { autoescape: false, trimBlocks: true, lstripBlocks: true }) : null;
if (env) {
  env.addFilter('collapsible', (content, title, open) =>
    content ? CD.sectionHTML(title == null ? 'Details' : String(title), String(content), !!open) : '');
  env.addGlobal('legend', (del = 'removed', ins = 'added', note = 'note') => CD.legendHTML(String(del), String(ins), String(note)));
}

const cleanError = e => String((e && e.message) || e).replace(/^\(unknown path\)\s*/, '').replace(/\s*\n\s*/g, ' ').trim();
function compileTemplate(src) {
  if (!env) return { tpl: null, error: 'assets/vendor/nunjucks.min.js could not be loaded.' };
  try { return { tpl: nunjucks.compile(src, env, null, true), error: null }; } catch (e) { return { tpl: null, error: cleanError(e) }; }
}
const defaultTemplate = compileTemplate(DEFAULT_TEMPLATE).tpl;
let templateSource = store.get(KEYS.template, null);
if (typeof templateSource !== 'string') templateSource = DEFAULT_TEMPLATE;
let template = compileTemplate(templateSource);

// TinyMCE drops style="…" on paste in Chrome but keeps style='…', so styles
// written in the template are switched to single quotes too.
const singleQuoteStyles = html =>
  html.replace(/(<[a-zA-Z][^>]*?\sstyle\s*=\s*)"([^"]*)"/g, (m, pre, v) => `${pre}'${v.replace(/'/g, '&#39;')}'`);

function renderTemplate(tpl, vars) {
  try {
    return { html: singleQuoteStyles(tpl.render(vars)).replace(/\n{3,}/g, '\n\n').trim(), error: null };
  } catch (e) {
    return { html: '', error: cleanError(e) };
  }
}

function outputVars() {
  return {
    diff: parts.diff,
    original: parts.original,
    corrected: parts.corrected,
    feedback: richValue(feedback),
    signature: richValue(signature),
    changes: diff ? diff.changes : 0,
    notes: diff ? diff.notes : 0,
  };
}

// The final HTML. A broken custom template falls back to the default one.
function buildOutput(vars = outputVars()) {
  let result = template.tpl ? renderTemplate(template.tpl, vars) : { html: '', error: template.error };
  const error = result.error;
  if (error) {
    result = defaultTemplate ? renderTemplate(defaultTemplate, vars)
      : { html: [vars.diff, vars.feedback, vars.signature].filter(Boolean).join('\n') };
  }
  return { html: result.html, error };
}

const hasContent = () => (diff && !diff.empty) || !isEmpty(feedback) || !isEmpty(signature);

const EMPTY_PREVIEW =
  `<div class="empty"><strong>Nothing to preview yet</strong>` +
  `Paste a student's text on the left and correct it on the right. The result appears here with ` +
  `<del style='${STYLE.del};padding:1px 2px'>removed</del> and <ins style='${STYLE.ins};padding:1px 2px'>added</ins> words, ` +
  `your <em style='${STYLE.note}'>notes</em>, feedback and signature.</div>`;

function renderOutput() {
  const { html, error } = buildOutput();
  $('tpl-warning').hidden = !error;
  preview.innerHTML = hasContent() && html ? html : EMPTY_PREVIEW;
  if (dlg.open && !tplPanel.hidden) renderTemplatePanel();
}

/* ---------- Plain-text version ---------- */

function htmlToText(html) {
  const body = parseHTML(html);
  let out = '';
  const block = () => {
    out = out.replace(/[ \t]+$/, '');
    if (out && !out.endsWith('\n\n')) out += out.endsWith('\n') ? '\n' : '\n\n';
  };
  const walk = node => {
    if (node.nodeType === 3) { out += node.data.replace(/\s+/g, ' '); return; }
    if (node.nodeType !== 1) return;
    const tag = node.tagName;
    const inner = () => { for (let c = node.firstChild; c; c = c.nextSibling) walk(c); };
    switch (tag) {
      case 'BR': out = out.replace(/[ \t]+$/, '') + '\n'; return;
      case 'HR': block(); out += '———'; block(); return;
      case 'DEL': out += '[-'; inner(); out += '-]'; return;
      case 'INS': out += '{+'; inner(); out += '+}'; return;
      case 'LI': {
        out = out.replace(/[ \t]+$/, '');
        if (out && !out.endsWith('\n')) out += '\n';
        const list = node.parentElement;
        out += list && list.tagName === 'OL' ? `${Array.from(list.children).indexOf(node) + 1}. ` : '- ';
        inner();
        out += '\n';
        return;
      }
      case 'SUMMARY': block(); inner(); out += ':\n'; return;
      case 'EM':
        if (node.getAttribute('style') === STYLE.note) { out += '['; inner(); out += ']'; return; }
        break;
    }
    const isBlock = BLOCK.has(tag) && tag !== 'LI';
    if (isBlock) block();
    inner();
    if (isBlock) block();
  };
  walk(body);
  return out.replace(/\n[ \t]+/g, '\n').replace(/[ \t]+\n/g, '\n').replace(/ {2,}/g, ' ').replace(/\n{3,}/g, '\n\n').trim();
}

/* ---------- Saving ---------- */

let saveTimer = 0;
function saveSoon() {
  clearTimeout(saveTimer);
  saveTimer = setTimeout(() => {
    store.set(KEYS.state, { v: 2, orig: orig.innerHTML, corr: corr.innerHTML, feedback: feedback.innerHTML });
  }, 250);
}
const saveSignature = () => store.set(KEYS.signature, signature.innerHTML);

/* ---------- Editing ---------- */

let pastedOverAll = false;

orig.addEventListener('input', () => {
  // Mirror the student's text into the correction until the teacher edits it.
  const mirroring = corr.innerHTML === prevOrigHTML || isEmpty(corr);
  if (mirroring) corr.innerHTML = orig.innerHTML;
  prevOrigHTML = orig.innerHTML;
  scheduleDiff();
  saveSoon();
  if (pastedOverAll && !mirroring) {
    const before = snapshot();
    toast('New text pasted — your correction still holds the old one.',
      () => restore({ ...before, corr: before.orig }), 'Start over from it');
  }
  pastedOverAll = false;
});
corr.addEventListener('input', () => { scheduleDiff(); saveSoon(); });
feedback.addEventListener('input', () => { updateEmpty(feedback); renderOutput(); saveSoon(); });
signature.addEventListener('input', () => { updateEmpty(signature); renderOutput(); saveSignature(); });

function insertHTML(html) {
  if (!html) return;
  let ok = false;
  try { ok = document.execCommand('insertHTML', false, html); } catch { ok = false; }
  if (ok) return;
  const sel = getSelection();
  if (!sel.rangeCount) return;
  const range = sel.getRangeAt(0);
  const start = range.startContainer;
  const host = (start.nodeType === 1 ? start : start.parentElement).closest('.rte');
  range.deleteContents();
  const frag = range.createContextualFragment(html);
  const last = frag.lastChild;
  range.insertNode(frag);
  if (last) { range.setStartAfter(last); range.collapse(true); sel.removeAllRanges(); sel.addRange(range); }
  if (host) host.dispatchEvent(new Event('input', { bubbles: true }));
}

const selectionCoversAll = el => {
  const sel = getSelection();
  const all = el.textContent.replace(/\s/g, '');
  return !!all && sel.rangeCount > 0 && sel.toString().replace(/\s/g, '') === all;
};

let draggingInside = false;
document.addEventListener('dragstart', () => { draggingInside = true; });
document.addEventListener('dragend', () => { draggingInside = false; });

function placeCaretAt(x, y) {
  let range = null;
  if (document.caretPositionFromPoint) {
    const p = document.caretPositionFromPoint(x, y);
    if (p) { range = document.createRange(); range.setStart(p.offsetNode, p.offset); }
  } else if (document.caretRangeFromPoint) {
    range = document.caretRangeFromPoint(x, y);
  }
  if (range) { const sel = getSelection(); sel.removeAllRanges(); sel.addRange(range); }
}

function format(ed, cmd) {
  if (document.activeElement !== ed) ed.focus();
  try { document.execCommand(cmd, false, null); } catch { /* unsupported command */ }
  updateToolbars();
}

for (const ed of EDITORS) {
  ed.addEventListener('paste', e => {
    if (!e.clipboardData) return;
    e.preventDefault();
    if (ed === orig) pastedOverAll = selectionCoversAll(orig);
    insertHTML(cleanFor(ed, e.clipboardData.getData('text/html'), e.clipboardData.getData('text/plain')));
    pastedOverAll = false;
  });
  ed.addEventListener('drop', e => {
    if (draggingInside || !e.dataTransfer) return;
    e.preventDefault();
    const html = e.dataTransfer.getData('text/html'), text = e.dataTransfer.getData('text/plain');
    if (!html && !text) return;
    ed.focus();
    placeCaretAt(e.clientX, e.clientY);
    insertHTML(cleanFor(ed, html, text));
  });
  ed.addEventListener('keydown', e => {
    if (ed === signature && e.key === 'Enter' && !e.isComposing && !e.ctrlKey && !e.metaKey && !e.altKey) {
      e.preventDefault();
      document.execCommand('insertLineBreak');
      return;
    }
    if (e.isComposing || e.altKey || e.shiftKey || !(e.ctrlKey || e.metaKey)) return;
    const key = e.key.toLowerCase();
    const cmd = { b: 'bold', i: 'italic', u: 'underline' }[key];
    if (cmd) { e.preventDefault(); format(ed, cmd); }
    else if (key === 'm' && e.ctrlKey && ed === corr) { e.preventDefault(); insertNote(); }
  });
}

/* ---------- Toolbars ---------- */

const bars = Array.from(document.querySelectorAll('.fmt-bar'));
for (const bar of bars) {
  const ed = $(bar.dataset.for);
  bar.addEventListener('mousedown', e => { if (e.target.closest('button')) e.preventDefault(); });
  bar.addEventListener('click', e => {
    const b = e.target.closest('button[data-cmd]');
    if (b) format(ed, b.dataset.cmd);
  });
}
function updateToolbars() {
  const active = document.activeElement;
  for (const bar of bars) {
    const focused = active && active.id === bar.dataset.for;
    for (const b of bar.querySelectorAll('button[data-cmd]')) {
      let on = false;
      if (focused) { try { on = document.queryCommandState(b.dataset.cmd); } catch { on = false; } }
      b.setAttribute('aria-pressed', on ? 'true' : 'false');
    }
  }
}
document.addEventListener('selectionchange', updateToolbars);

/* ---------- German characters ---------- */

// Remember where the caret was in each editor, so a character button still
// inserts at the right spot after focus moved elsewhere.
let lastEditor = null;
const lastRanges = new Map();
document.addEventListener('selectionchange', () => {
  const sel = getSelection();
  if (!sel.rangeCount) return;
  const ed = EDITORS.find(e => e.contains(sel.anchorNode));
  if (ed) { lastEditor = ed; lastRanges.set(ed, sel.getRangeAt(0).cloneRange()); }
});

function insertChar(ch) {
  const ed = EDITORS.includes(document.activeElement) ? document.activeElement : lastEditor || orig;
  if (document.activeElement !== ed) {
    ed.focus();
    let range = lastRanges.get(ed);
    if (!range || !ed.contains(range.startContainer)) {
      range = document.createRange();
      range.selectNodeContents(ed);
      range.collapse(false);
    }
    const sel = getSelection();
    sel.removeAllRanges();
    sel.addRange(range);
  }
  let ok = false;
  try { ok = document.execCommand('insertText', false, ch); } catch { ok = false; }
  if (!ok) insertHTML(esc(ch));
}

const charBar = $('char-bar');
charBar.addEventListener('mousedown', e => { if (e.target.closest('button')) e.preventDefault(); });
charBar.addEventListener('click', e => {
  const b = e.target.closest('button[data-char]');
  if (b) insertChar(b.dataset.char);
});

/* ---------- Notes ---------- */

function insertNote() {
  if (document.activeElement !== corr) corr.focus();
  const sel = getSelection();
  if (!sel.rangeCount || !corr.contains(sel.anchorNode)) {
    const r = document.createRange();
    r.selectNodeContents(corr);
    r.collapse(false);
    sel.removeAllRanges();
    sel.addRange(r);
  }
  sel.collapseToEnd();
  const caret = sel.getRangeAt(0);
  const before = document.createRange();
  before.selectNodeContents(corr);
  before.setEnd(caret.endContainer, caret.endOffset);
  const text = before.toString();
  const lead = text && !/\s$/.test(text) ? ' ' : '';
  let ok = false;
  try { ok = document.execCommand('insertText', false, lead + '[[]]'); } catch { ok = false; }
  if (!ok) insertHTML(esc(lead + '[[]]'));
  if (sel.modify) { sel.modify('move', 'backward', 'character'); sel.modify('move', 'backward', 'character'); }
}
$('btn-note').addEventListener('click', insertNote);

/* ---------- Undoable bulk actions ---------- */

const snapshot = () => ({ orig: orig.innerHTML, corr: corr.innerHTML, feedback: feedback.innerHTML });
function restore(s) {
  orig.innerHTML = s.orig;
  corr.innerHTML = s.corr;
  feedback.innerHTML = s.feedback;
  prevOrigHTML = orig.innerHTML;
  updateEmpty(feedback);
  recomputeDiff();
  saveSoon();
}

$('btn-new').addEventListener('click', () => {
  if (isEmpty(orig) && isEmpty(corr) && isEmpty(feedback)) { orig.focus(); return; }
  const before = snapshot();
  restore({ orig: '', corr: '', feedback: '' });
  orig.scrollTop = corr.scrollTop = 0;
  orig.focus();
  toast('Cleared — ready for the next student', () => restore(before));
});

$('btn-clear-orig').addEventListener('click', () => {
  if (isEmpty(orig)) { orig.focus(); return; }
  const before = snapshot();
  restore({ ...before, orig: '', corr: before.corr === before.orig ? '' : before.corr });
  orig.focus();
  toast("Student's text cleared", () => restore(before));
});

$('btn-reset').addEventListener('click', () => {
  if (corr.innerHTML === orig.innerHTML) return;
  const before = snapshot();
  restore({ ...before, corr: before.orig });
  toast("Correction reset to the student's text", () => restore(before));
});

/* ---------- Scrolling & sizing ---------- */

let scrollLead = null;
for (const ed of [orig, corr]) {
  for (const ev of ['pointerenter', 'focus', 'wheel', 'touchstart', 'keydown']) {
    ed.addEventListener(ev, () => { scrollLead = ed; }, { passive: true });
  }
  ed.addEventListener('scroll', () => {
    if (!settings.syncScroll || scrollLead !== ed) return;
    const other = ed === orig ? corr : orig;
    const max = ed.scrollHeight - ed.clientHeight;
    other.scrollTop = (max > 0 ? ed.scrollTop / max : 0) * (other.scrollHeight - other.clientHeight);
  }, { passive: true });
}

// Dragging one editor's resize handle resizes the other one too.
let resizing = null;
for (const ed of [orig, corr]) ed.addEventListener('pointerdown', () => { resizing = ed; });
window.addEventListener('pointerup', () => { resizing = null; });
if ('ResizeObserver' in window) {
  const ro = new ResizeObserver(entries => {
    for (const entry of entries) {
      const ed = entry.target;
      if (ed !== resizing) continue;
      const other = ed === orig ? corr : orig;
      if (Math.abs(other.offsetHeight - ed.offsetHeight) > 1) other.style.height = ed.offsetHeight + 'px';
    }
  });
  ro.observe(orig);
  ro.observe(corr);
}

/* ---------- Clipboard ---------- */

// A synthetic copy event writes the HTML string untouched; the async Clipboard
// API would re-serialize it (turning our single-quoted styles into double quotes).
function copyRich(html, text) {
  let written = false;
  const onCopy = e => {
    e.clipboardData.setData('text/plain', text);
    if (html != null) e.clipboardData.setData('text/html', html);
    e.preventDefault();
    written = true;
  };
  const active = document.activeElement;
  const sel = window.getSelection();
  const saved = sel.rangeCount ? sel.getRangeAt(0).cloneRange() : null;
  const field = active && typeof active.selectionStart === 'number' ? [active.selectionStart, active.selectionEnd] : null;

  const holder = document.createElement('span');
  holder.textContent = text || ' ';
  holder.style.cssText = 'position:fixed;top:0;left:-9999px;white-space:pre;opacity:0;';
  document.body.appendChild(holder);
  const r = document.createRange();
  r.selectNodeContents(holder);
  sel.removeAllRanges();
  sel.addRange(r);

  document.addEventListener('copy', onCopy, true);
  try { document.execCommand('copy'); } catch { /* fall through to the async API */ }
  document.removeEventListener('copy', onCopy, true);
  sel.removeAllRanges();
  holder.remove();
  if (active && active.focus) active.focus({ preventScroll: true });
  if (field) active.setSelectionRange(field[0], field[1]);
  else if (saved) { sel.removeAllRanges(); sel.addRange(saved); }
  if (written) return Promise.resolve(true);

  if (navigator.clipboard) {
    if (html != null && window.ClipboardItem) {
      return navigator.clipboard.write([new ClipboardItem({
        'text/html': new Blob([html], { type: 'text/html' }),
        'text/plain': new Blob([text], { type: 'text/plain' }),
      })]).then(() => true, () => false);
    }
    return navigator.clipboard.writeText(text).then(() => true, () => false);
  }
  return Promise.resolve(false);
}

const copyBtn = $('btn-copy');
let copyFlash = 0;
async function copyForMoodle() {
  if (!hasContent()) { toast('Nothing to copy yet — paste a student text first.'); return; }
  const { html } = buildOutput();
  const ok = await copyRich('<meta charset="utf-8">' + html, htmlToText(html));
  if (!ok) { toast('Copying failed. Select the preview and press Ctrl+C instead.'); return; }
  copyBtn.classList.add('done');
  copyBtn.querySelector('.lbl').textContent = 'Copied';
  clearTimeout(copyFlash);
  copyFlash = setTimeout(() => {
    copyBtn.classList.remove('done');
    copyBtn.querySelector('.lbl').textContent = 'Copy for Moodle';
  }, 1600);
  toast('Copied — paste it into Moodle with Ctrl+V');
}
copyBtn.addEventListener('click', copyForMoodle);

$('btn-copy-text').addEventListener('click', async () => {
  if (!hasContent()) { toast('Nothing to copy yet — paste a student text first.'); return; }
  const ok = await copyRich(null, htmlToText(buildOutput().html));
  toast(ok ? 'Plain text copied' : 'Copying failed.');
});

document.addEventListener('keydown', e => {
  if (!e.isComposing && (e.ctrlKey || e.metaKey) && e.key === 'Enter' && !dlg.open) {
    e.preventDefault();
    copyForMoodle();
  }
});

/* ---------- Toast ---------- */

const toastEl = $('toast'), toastMsg = $('toast-msg'), toastAction = $('toast-action');
let toastTimer = 0, toastHandler = null;
function toast(message, action, label = 'Undo') {
  toastMsg.textContent = message;
  toastHandler = action || null;
  toastAction.hidden = !action;
  toastAction.textContent = label;
  toastEl.classList.add('show');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => toastEl.classList.remove('show'), action ? 7000 : 2600);
}
toastAction.addEventListener('click', () => {
  if (toastHandler) toastHandler();
  toastHandler = null;
  toastEl.classList.remove('show');
});

/* ---------- Settings dialog ---------- */

const dlg = $('settings');
const tplPanel = $('panel-template');
const TABS = { general: [$('tab-general'), $('panel-general')], template: [$('tab-template'), tplPanel] };

function showTab(name) {
  for (const [key, [tab, panel]] of Object.entries(TABS)) {
    tab.setAttribute('aria-selected', String(key === name));
    panel.hidden = key !== name;
  }
  dlg.classList.toggle('wide', name === 'template');
  if (name === 'template') renderTemplatePanel();
}
$('tab-general').addEventListener('click', () => showTab('general'));
$('tab-template').addEventListener('click', () => showTab('template'));
$('btn-settings').addEventListener('click', () => { showTab('general'); dlg.showModal(); });
const openTemplate = () => { showTab('template'); dlg.showModal(); tplInput.focus(); };
$('btn-template').addEventListener('click', openTemplate);
$('tpl-warning').addEventListener('click', openTemplate);

let downOnBackdrop = false;
dlg.addEventListener('mousedown', e => { downOnBackdrop = e.target === dlg; });
dlg.addEventListener('click', e => { if (downOnBackdrop && e.target === dlg) dlg.close(); });

const STYLE_INFO = {
  chars: 'Marks the exact letters that changed — best for spelling. Rewritten passages get choppy.',
  words: 'Every changed word on its own. Precise, but a rewritten passage breaks into many small pieces.',
  phrases: 'Neighbouring changes become one old → new pair, so rewritten passages stay readable. Recommended.',
  sentences: 'Like Phrases, and a sentence that is mostly rewritten is shown whole: the old sentence struck through, then the new one.',
};
const STYLE_SAMPLE = {
  orig: 'Gestern ich bin mit meine Freund ins grosse Kino gegangen. Der Film waren sehr gut und wir hat viel gelacht.',
  corr: 'Gestern bin ich mit meinem Freund ins große Kino gegangen. Der Film war wirklich gut, und wir haben viel gelacht.',
};
{
  const d = (t, cls) => `<${cls} style='${STYLE[cls]}'>${t}</${cls}>`;
  $('letters-desc').innerHTML = 'When a word is mostly right, only the wrong letters are marked: ' +
    `<span class="ex">diese${d('s', 'del')}${d('m', 'ins')}</span>, <span class="ex">gro${d('ss', 'del')}${d('ß', 'ins')}</span>, ` +
    `<span class="ex">${d('ue', 'del')}${d('ü', 'ins')}ber</span>. Words that changed more stay whole.`;
}

function syncSettingsUI() {
  for (const r of document.querySelectorAll('input[name="style"]')) r.checked = r.value === settings.style;
  $('style-desc').textContent = STYLE_INFO[settings.style] || '';
  const letters = $('opt-letters');
  letters.checked = settings.letters;
  letters.disabled = settings.style === 'chars';
  $('letters-row').classList.toggle('off', letters.disabled);
  const d = CD.computeDiff({ text: STYLE_SAMPLE.orig }, { text: STYLE_SAMPLE.corr }, settings);
  $('style-example').innerHTML = CD.renderDiffHTML(d);
  $('opt-sync').checked = settings.syncScroll;
}
function updateSetting(key, value, rediff) {
  settings[key] = value;
  store.set(KEYS.settings, settings);
  syncSettingsUI();
  if (rediff) recomputeDiff();
}
for (const r of document.querySelectorAll('input[name="style"]')) {
  r.addEventListener('change', () => { if (r.checked) updateSetting('style', r.value, true); });
}
$('opt-letters').addEventListener('change', e => updateSetting('letters', e.target.checked, true));
$('opt-sync').addEventListener('change', e => updateSetting('syncScroll', e.target.checked, false));

/* ---------- Template editor ---------- */

const tplInput = $('tpl'), tplError = $('tpl-error'), tplStatus = $('tpl-status');
const tplPreview = $('tpl-preview'), tplPreviewNote = $('tpl-preview-note');

const SAMPLE = {
  orig: 'Last summer I goed to Kyoto with my family. We visited many temple.',
  corr: 'Last summer I went [[irregular verb]] to Kyoto with my family. We visited many temples.',
};
function sampleVars() {
  const d = CD.computeDiff({ text: SAMPLE.orig }, { text: SAMPLE.corr }, settings);
  return {
    diff: CD.renderDiffHTML(d),
    original: CD.modelToHTML(d.original, null),
    corrected: CD.modelToHTML(d.corrected, null),
    feedback: richValue(feedback) || '<p>Nice story! Keep practising <strong>irregular past forms</strong>.</p>',
    signature: richValue(signature) || '<p>Best regards,<br>Your teacher</p>',
    changes: d.changes,
    notes: d.notes,
  };
}

function renderTemplatePanel() {
  const custom = templateSource !== DEFAULT_TEMPLATE;
  tplStatus.textContent = custom ? 'Custom · saved in this browser' : 'Default template';
  const useSample = !(diff && !diff.empty);
  tplPreviewNote.textContent = useSample ? 'with sample text' : 'with your current student';
  let error = template.error;
  let html = '';
  if (template.tpl) {
    const r = renderTemplate(template.tpl, useSample ? sampleVars() : outputVars());
    error = r.error;
    html = r.html;
  }
  tplError.hidden = !error;
  tplError.textContent = error ? `Template error: ${error}` : '';
  tplPreview.innerHTML = html || '<div class="empty">The template produces no output.</div>';
}

function setTemplate(src) {
  templateSource = src;
  if (tplInput.value !== src) tplInput.value = src;
  if (src === DEFAULT_TEMPLATE) store.remove(KEYS.template); else store.set(KEYS.template, src);
  template = compileTemplate(src);
  renderOutput();
  renderTemplatePanel();
}
tplInput.value = templateSource;
tplInput.addEventListener('input', () => setTemplate(tplInput.value));
$('tpl-reset').addEventListener('click', () => {
  if (templateSource === DEFAULT_TEMPLATE) return;
  const before = templateSource;
  setTemplate(DEFAULT_TEMPLATE);
  toast('Template reset to the default', () => setTemplate(before));
});

/* ---------- Start ---------- */

syncSettingsUI();
for (const ed of EDITORS) updateEmpty(ed);
recomputeDiff();
updateToolbars();
if (isEmpty(orig)) orig.focus();

})();
