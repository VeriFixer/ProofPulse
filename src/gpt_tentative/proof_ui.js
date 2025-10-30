// proof_ui.js
// DOM-only logic. Imports parsing/model code from proof_parser.js

import { parseReport, runTests } from './proof_parser.js';

// Dummy code text (you can replace with server-side string later)
const codeText = `method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  if(x == 0){
    y := 0; // Unused by proof  _USECASE_find_irrelevant_lines.dfy(6,5)-(6,11): assignment (or return)
  }

  if x < 0 {
    y := -x;
  } else {
    y := Id(x);
  }
}

function Id<T> (a : T) : T {
    a
}
`;

// sample report (same as before) - in production you will replace by server data
const reportText = `Results for Abs (correctness)
  Overall outcome: Correct

  Assertion batch 1:
    Assertions:
      _USECASE_find_irrelevant_lines_for_proof.dfy(2,20): this postcondition holds
    Proof dependencies:
      _USECASE_find_irrelevant_lines_for_proof.dfy(2,20)-(2,23): ensures clause
      _USECASE_find_irrelevant_lines_for_proof.dfy(12,5)-(12,15): assignment (or return)
      _USECASE_find_irrelevant_lines_for_proof.dfy(16,1)-(18,1): function definition for Id
    Unused by proof:
      _USECASE_find_irrelevant_lines_for_proof.dfy(6,5)-(6,11): assignment (or return)

  Assertion batch 2:
    Assertions:
      _USECASE_find_irrelevant_lines_for_proof.dfy(3,19): this postcondition holds
    Proof dependencies:
      _USECASE_find_irrelevant_lines_for_proof.dfy(3,19)-(3,24): ensures clause
      _USECASE_find_irrelevant_lines_for_proof.dfy(10,5)-(10,12): assignment (or return)
`;

// --- DOM helpers
const $ = s => document.querySelector(s);
const $$ = s => Array.from(document.querySelectorAll(s));

function buildUIModelAndRender() {
  // parse report into model
  const profile = parseReport(reportText);

  // determine uncovered element keys (present in any batch.unusedByProof)
  const uncoveredElementKeys = new Set();
  for (const pf of profile.files.values()) {
    for (const batch of pf.batches) {
      for (const k of batch.unusedByProof) uncoveredElementKeys.add(k);
    }
  }

  const uncoveredLinesByFile = new Map();
  for (const [fname, pf] of profile.files) {
    for (const el of pf.elements.values()) {
      if (uncoveredElementKeys.has(el._key)) {
        for (let L = el.start.line; L <= el.end.line; L++) {
          if (!uncoveredLinesByFile.has(fname)) uncoveredLinesByFile.set(fname, new Set());
          uncoveredLinesByFile.get(fname).add(L);
        }
      }
    }
  }

  // Render source (DOM-only)
  const sourceEl = $('#source');
  sourceEl.innerHTML = '';
  const codeLines = codeText.split(/\r?\n/);
  for (let i = 0; i < codeLines.length; i++) {
    const lineno = i + 1;
    const lineDiv = document.createElement('div');
    lineDiv.className = 'line';
    lineDiv.dataset.line = String(lineno);

    // status from uncoveredLinesByFile (best effort)
    let status = 'covered-complete';
    for (const setLines of uncoveredLinesByFile.values()) {
      if (setLines.has(lineno)) { status = 'uncovered'; break; }
    }
    lineDiv.dataset.status = status;

    const lnum = document.createElement('span'); lnum.className = 'lnum';
    lineDiv.appendChild(lnum);

    // simple tokenization, track approximate column
    const tokenContainer = document.createElement('span');
    tokenContainer.className = 'tokens';
    const rawTokens = codeLines[i].length ? codeLines[i].split(/(\s+)/) : [''];
    let charPos = 1;
    let tokenIndex = 0;
    for (const piece of rawTokens) {
      if (piece === '') continue;
      if (/^\s+$/.test(piece)) {
        tokenContainer.appendChild(document.createTextNode(piece));
        charPos += piece.length;
        continue;
      }
      const t = document.createElement('span');
      t.className = 'token';
      const tid = `ln${lineno}_t${tokenIndex++}`;
      t.dataset.id = tid;
      t.dataset.col = String(charPos);
      t.textContent = piece;
      t.dataset.status = status === 'uncovered' ? 'uncovered' : 'covered-complete';
      tokenContainer.appendChild(t);
      charPos += piece.length;
    }
    lineDiv.appendChild(tokenContainer);
    sourceEl.appendChild(lineDiv);
  }

  // fill gutters
  $$('#source .line').forEach((lnEl, idx) => {
    const raw = lnEl.dataset.line || (idx + 1);
    const num = String(raw).padStart(4, '0');
    const lnumEl = lnEl.querySelector('.lnum');
    if (lnumEl) lnumEl.textContent = num;
  });

  // build depsByElementKey for quick lookup (element-key -> info)
  const depsByElementKey = new Map();
  for (const [fname, pf] of profile.files) {
    for (const [key, el] of pf.elements) {
      const usesEls = el.uses(pf).filter(Boolean);
      const usedByEls = el.usedBy(pf).filter(Boolean);
      const proofReportBatches = [];
      for (const batch of pf.batches) {
        const inUnused = batch.unusedByProof.includes(key);
        const inDeps = batch.proofDependencies.includes(key);
        const inAssertions = batch.assertions.includes(key);
        if (inUnused || inDeps || inAssertions) {
          proofReportBatches.push({
            assertionStrings: batch.assertionStrings.slice(),
            proofDependencies: batch.proofDependencies.slice(),
            unusedByProof: batch.unusedByProof.slice()
          });
        }
      }
      depsByElementKey.set(key, {
        key,
        element: el,
        uses: usesEls.map(x => x ? x._key : null).filter(Boolean),
        usedBy: usedByEls.map(x => x ? x._key : null).filter(Boolean),
        proofReport: proofReportBatches.length ? { note: `Report fragments ${el.spanString()}`, batches: proofReportBatches } : null
      });
    }
  }

  // token->element mapping (span-first, containment fallback)
  function buildTokenToElementMap() {
    const map = new Map();
    const rev = new Map();
    $$('.token').forEach(t => {
      const parentLine = t.closest('.line');
      const lineNum = parentLine ? parseInt(parentLine.dataset.line || -1, 10) : -1;
      const col = t.dataset.col ? parseInt(t.dataset.col, 10) : 1;
      const tokenText = t.textContent.trim();

      let matched = null;
      for (const pf of profile.files.values()) {
        const el = pf.getElementAtPos(lineNum, col);
        if (el) { matched = el; break; }
      }
      if (!matched && tokenText) {
        for (const pf of profile.files.values()) {
          const els = pf.findElementsContainingToken(tokenText, lineNum);
          if (els && els.length) { matched = els[0]; break; }
        }
      }
      if (matched) {
        map.set(t.dataset.id, matched._key);
        if (!rev.has(matched._key)) rev.set(matched._key, []);
        rev.get(matched._key).push(t.dataset.id);
      }
    });
    return { map, rev };
  }

  let tokenToElem = new Map();
  let elemToTokens = new Map();
  function refreshMaps() {
    const m = buildTokenToElementMap();
    tokenToElem = m.map;
    elemToTokens = m.rev;
  }
  refreshMaps();

  // UI panel rendering using token->element mapping and depsByElementKey
  const panelTitle = document.getElementById('panel-title');
  const panelBody = document.getElementById('panel-body');

  function clearHighlights() { $$('.token').forEach(t => t.classList.remove('selected', 'related')); }

  function getDepsForTokenId(tokenId) {
    const elKey = tokenToElem.get(tokenId);
    if (elKey && depsByElementKey.has(elKey)) {
      const d = depsByElementKey.get(elKey);
      // convert element keys to first token mapped for UI highlighting (best-effort)
      const toTok = arr => arr.map(k => (elemToTokens.has(k) ? elemToTokens.get(k)[0] : k));
      return { uses: toTok(d.uses), usedBy: toTok(d.usedBy), proofReport: d.proofReport };
    }
    return { uses: [], usedBy: [], proofReport: null };
  }

  function renderPanel(tokenEl) {
    if (!tokenEl) return;
    const id = tokenEl.dataset.id;
    refreshMaps();
    const info = getDepsForTokenId(id);
    panelTitle.textContent = `Dependency tracker — ${tokenEl.textContent.trim()}`;
    clearHighlights();
    tokenEl.classList.add('selected');

    info.uses.forEach(uid => { const el = document.querySelector(`[data-id="${uid}"]`); if (el) el.classList.add('related'); });
    info.usedBy.forEach(uid => { const el = document.querySelector(`[data-id="${uid}"]`); if (el) el.classList.add('related'); });

    panelBody.innerHTML = '';
    const status = tokenEl.dataset.status || 'unknown';
    const p = document.createElement('p'); p.innerHTML = `<strong>Status:</strong> ${status}`; panelBody.appendChild(p);

    if (info.proofReport) {
      const note = document.createElement('div'); note.className = 'hint'; note.textContent = info.proofReport.note;
      panelBody.appendChild(note);
      info.proofReport.batches.forEach((b, idx) => {
        const box = document.createElement('div'); box.className = 'group';
        const assertionText = (b.assertionStrings && b.assertionStrings.length) ? b.assertionStrings.join('; ') : '(assertion)';
        box.innerHTML = `<strong>Assertion batch ${idx+1}:</strong><div style="margin-top:6px;font-size:13px">${assertionText}</div>`;
        const ul = document.createElement('ul');
        b.proofDependencies.forEach(d => { const li = document.createElement('li'); const text = (elemToTokens.has(d) ? elemToTokens.get(d)[0] : d); li.textContent = text; ul.appendChild(li); });
        box.appendChild(ul);
        panelBody.appendChild(box);
      });
      return;
    }

    // fallback lists
    const usesDiv = document.createElement('div'); usesDiv.className='group'; usesDiv.innerHTML = `<strong>Uses (${info.uses.length}):</strong>`;
    const ulU = document.createElement('ul');
    info.uses.forEach(u => { const li = document.createElement('li'); li.textContent = u; ulU.appendChild(li); });
    usesDiv.appendChild(ulU); panelBody.appendChild(usesDiv);

    const usedByDiv = document.createElement('div'); usedByDiv.className='group'; usedByDiv.innerHTML = `<strong>Used by (${info.usedBy.length}):</strong>`;
    const ulB = document.createElement('ul');
    info.usedBy.forEach(u => { const li = document.createElement('li'); li.textContent = u; ulB.appendChild(li); });
    usedByDiv.appendChild(ulB); panelBody.appendChild(usedByDiv);
  }

  // attach click handlers
  $$('.token').forEach(t => {
    t.tabIndex = 0;
    t.addEventListener('click', () => renderPanel(t));
    t.addEventListener('keydown', e => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); renderPanel(t); } });
  });

  // auto-select uncovered or first token
  const uncoveredLine = document.querySelector('[data-status="uncovered"]');
  if (uncoveredLine) {
    const tok = uncoveredLine.querySelector('.token');
    if (tok) renderPanel(tok);
  } else {
    const first = document.querySelector('.token');
    if (first) renderPanel(first);
  }

  // run parser tests and show result in panel (keeps tests available)
  try {
    const tRes = runTests();
    const ok = document.createElement('div'); ok.className = 'hint'; ok.textContent = 'Parser tests: ' + tRes.join(' | ');
    panelBody.appendChild(ok);
  } catch (err) {
    const fail = document.createElement('div'); fail.className = 'hint'; fail.textContent = 'Parser tests failed: ' + String(err);
    panelBody.appendChild(fail);
    console.error('Parser tests failed', err);
  }
}

// initialize on DOMContentLoaded
document.addEventListener('DOMContentLoaded', () => {
  try {
    buildUIModelAndRender();
    console.log('UI initialized (DOM separated from logic).');
  } catch (err) {
    console.error('UI init error', err);
    const pb = document.getElementById('panel-body');
    if (pb) pb.innerHTML = `<div class="hint">UI init error: ${String(err)}</div>`;
  }
});
