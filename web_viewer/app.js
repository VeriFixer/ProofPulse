const dollar = s => document.querySelector(s);
const dollarAll = s => Array.from(document.querySelectorAll(s));

const pre = dollar('#source');
const panelBody = dollar('#panel-body');
const panelTitle = dollar('#panel-title');

let provedByDepth = 2;
let provesDepth = 2;
let currentTokenEl = null;

function escapeHtml(s) {
    return String(s)
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;');
}

function typeBadge(type) {
  const colors = {
    Precondition: '#4fc3f7',
    Postcondition: '#ab47bc',
    AssertionManual: '#ff7043',
    AssertionAutomatic: '#66bb6a',
    CodeLine: '#78909c',
    Undefined: '#555',
  };
  return `<span class="type-badge" style="background:${colors[type] || '#555'}">${type}</span>`;
}

function buildSourceDomFromFragment(fragmentHtml, code, lineStatuses) {
    const linesHtml = fragmentHtml.split('\n');
    const linesText = code.split('\n');
    const container = document.createDocumentFragment();

    for (let i = 0; i < Math.max(linesHtml.length, linesText.length); i++) {
        const lineNum = i + 1;
        const status = (lineStatuses[i]) ? lineStatuses[i] : CovStatus.CovComplete;
        const div = document.createElement('div');
        div.className = 'line';
        div.dataset.line = String(lineNum);
        div.dataset.status = status;

        const lnum = document.createElement('span');
        lnum.className = 'lnum';
        lnum.textContent = String(lineNum).padStart(4, '0');
        div.appendChild(lnum);

        const contentHtml = linesHtml[i] !== undefined
            ? linesHtml[i]
            : escapeHtml(linesText[i] || '');

        const wrapper = document.createElement('span');
        wrapper.innerHTML = contentHtml;
        div.appendChild(wrapper);

        container.appendChild(div);
    }

    pre.innerHTML = '';
    pre.appendChild(container);
}

function clearHighlights() {
    dollarAll('.token').forEach(t => t.classList.remove('selected', 'related'));
}

/** Extract just Line:Col from a node id like "file.dfy:41,24-41,24" */
function shortLoc(node) {
  return `Line ${node.start.line}:${node.start.col}`;
}

/** Strip filename prefix from prooftext (e.g. "ensures clause at file.dfy(1,2)-(3,4)" → "ensures clause") */
function cleanProoftext(text) {
  if (!text) return '';
  return text.replace(/\s+at\s+[^\s(]+\(\d+,\d+\)-\(\d+,\d+\)/g, '').trim();
}

/** Get the actual source code text for a node's range from the loaded source.
 *  If the extracted text is very short (e.g. single char like "="), fall back to the full trimmed line. */
function getNodeSourceText(node) {
  const src = window.getSourceCode();
  if (!src) return null;
  const lines = src.split('\n');
  const sLine = node.start.line - 1;
  const eLine = node.end.line - 1;
  if (sLine < 0 || sLine >= lines.length) return null;

  let text;
  if (sLine === eLine) {
    const line = lines[sLine] || '';
    text = line.slice(Math.max(0, node.start.col - 1), node.end.col).trim();
  } else {
    const parts = [];
    parts.push((lines[sLine] || '').slice(Math.max(0, node.start.col - 1)));
    for (let i = sLine + 1; i < eLine && i < lines.length; i++) {
      parts.push(lines[i]);
    }
    if (eLine < lines.length) {
      parts.push((lines[eLine] || '').slice(0, node.end.col));
    }
    text = parts.join(' ').replace(/\s+/g, ' ').trim();
  }

  // If extracted text is too short (single char like "=" or ">"), use the full line trimmed
  if (text.length <= 2) {
    text = (lines[sLine] || '').trim();
  }
  return text || null;
}

/** Get display text for a node — prefers source code, falls back to DOM element text */
function getNodeDisplayText(node, maxLen) {
  const srcText = getNodeSourceText(node);
  const el = document.querySelector(`[data-id="${node.id}"]`);
  const raw = srcText || (el ? el.textContent.trim() : '…');
  if (!maxLen || raw.length <= maxLen) return raw;
  return raw.slice(0, maxLen - 3) + '...';
}

/** Context-aware status explanation based on token type + coverage status */
function statusExplanation(status, type) {
  if (status === 'Uncovered') {
    switch (type) {
      case 'Postcondition': return 'Postcondition not proven by any code path.';
      case 'Precondition': return 'Precondition not used in any proof obligation.';
      case 'AssertionManual': return 'Manual assertion not covered by proof dependencies.';
      case 'CodeLine': return 'Code line not contributing to any proof obligation.';
      default: return 'Not covered by any proof path.';
    }
  }
  if (status === 'CovTest') {
    switch (type) {
      case 'Postcondition': return 'Postcondition not used in calling code — only in test assertions.';
      case 'Precondition': return 'Precondition only used in calling tests, unnecessary to prove postconditions.';
      case 'CodeLine': return 'Code used only by test assertions, not by postcondition proofs.';
      default: return 'Covered only by test/non-postcondition assertions.';
    }
  }
  // CovComplete
  return 'Fully covered by postcondition proof dependencies.';
}

function statusColor(status) {
  if (status === 'Uncovered') return 'var(--color-uncovered-text)';
  if (status === 'CovTest') return 'var(--color-covtest-text)';
  return 'var(--color-covcomplete-text)';
}

function statusDot(status) {
  return `<span class="status-dot" style="background:${statusColor(status)}"></span>`;
}

function statusLabel(status) {
  return `<span class="status-label" style="color:${statusColor(status)}">${status}</span>`;
}

function renderDepSection({ title, results, depthValue, depthInputId, onDepthChange, proof }) {
    const section = document.createElement('div');
    section.className = 'dep-section';

    const header = document.createElement('div');
    header.className = 'dep-section-header';
    const total = results.length;
    header.innerHTML = `<span class="dep-section-title">${escapeHtml(title)} <span class="dep-count">${total}</span></span>` +
      `<div class="depth-control"><label>Depth:</label>` +
      `<input type="number" class="dep-depth-input" id="${depthInputId}" value="${depthValue}" min="1" />` +
      `<small>(0 = unlimited)</small></div>`;
    section.appendChild(header);

    const depthInput = header.querySelector(`#${depthInputId}`);
    if (depthInput) {
      depthInput.addEventListener('input', () => {
        const val = parseInt(depthInput.value, 10);
        onDepthChange(isNaN(val) ? 2 : val);
        if (currentTokenEl && proof) {
          renderPanel(currentTokenEl, proof);
        }
      });
    }

    // Group by depth
    const byDepth = new Map();
    results.forEach(r => {
      if (!byDepth.has(r.depth)) byDepth.set(r.depth, []);
      byDepth.get(r.depth).push(r.node);
    });

    const sortedDepths = Array.from(byDepth.keys()).sort((a, b) => a - b);
    sortedDepths.forEach(depth => {
      const nodes = byDepth.get(depth);
      const dh = document.createElement('div');
      dh.className = 'depth-header';
      dh.textContent = `Depth ${depth} (${nodes.length})`;
      section.appendChild(dh);

      const ul = document.createElement('ul');
      ul.className = 'dep-list';
      nodes.forEach(node => {
        const codeText = getNodeDisplayText(node, 60);
        const li = document.createElement('li');
        li.className = 'dep-item';
        li.innerHTML =
          `<div class="dep-item-main">${statusDot(node.covStatus)}${typeBadge(node.type)}<code class="dep-code">${escapeHtml(codeText)}</code></div>` +
          (node.prooftext ? `<div class="dep-item-proof">${escapeHtml(cleanProoftext(node.prooftext))}</div>` : '');
        ul.appendChild(li);
      });
      section.appendChild(ul);
    });

    if (sortedDepths.length === 0) {
      const empty = document.createElement('p');
      empty.className = 'hint';
      empty.textContent = `No ${title.toLowerCase()} found.`;
      section.appendChild(empty);
    }

    return section;
}

function renderPanel(tokenEl, proof) {
    currentTokenEl = tokenEl;
    const id = tokenEl.dataset.id;
    const token = proof.proofGraph.getNode(id);

    const displayCode = getNodeDisplayText(token, 60);

    // Panel title: type badge + top-assertion badge + code snippet
    const topBadge = token.isTopAssertion
      ? '<span class="top-badge">⬆ Top</span>'
      : '';
    panelTitle.innerHTML = typeBadge(token.type) + topBadge + `<code class="panel-title-code">${escapeHtml(displayCode)}</code>`;

    // Get directional neighbors
    const provedByResults = window.getProvedBy(id, proof, provedByDepth) || [];
    const provesResults = window.getProves(id, proof, provesDepth) || [];
    const allDepIds = [
      ...provedByResults.map(r => r.node.id),
      ...provesResults.map(r => r.node.id),
    ];

    clearHighlights();
    tokenEl.classList.add('selected');
    allDepIds.forEach(uid => { const el = document.querySelector(`[data-id="${uid}"]`); if (el) el.classList.add('related'); });

    panelBody.innerHTML = '';

    // ── Selected token info card ──
    const card = document.createElement('div');
    card.className = 'token-card';

    const internalStatus = token.covStatusInternal || token.covStatus;
    let statusHtml = `<div class="token-card-row">${statusDot(token.covStatus)} <strong>Status:</strong> ${statusLabel(token.covStatus)}</div>`;
    if (internalStatus !== token.covStatus) {
      statusHtml += `<div class="token-card-row">${statusDot(internalStatus)} <strong>Internal:</strong> ${statusLabel(internalStatus)}</div>`;
    }

    const explanation = statusExplanation(token.covStatus, token.type);
    const proofMsg = cleanProoftext(token.prooftext);

    card.innerHTML = statusHtml +
      `<p class="token-card-hint">${escapeHtml(explanation)}</p>` +
      (proofMsg ? `<div class="token-card-row"><strong>Message:</strong> <span class="token-card-proof">${escapeHtml(proofMsg)}</span></div>` : '');

    panelBody.appendChild(card);

    // ── Proved By section (things used to prove this node) ──
    panelBody.appendChild(renderDepSection({
      title: 'Proved By',
      results: provedByResults,
      depthValue: provedByDepth,
      depthInputId: 'provedby-depth-input',
      onDepthChange: (v) => { provedByDepth = v; },
      proof,
    }));

    // ── Proves section (things that use this node) ──
    panelBody.appendChild(renderDepSection({
      title: 'Proves',
      results: provesResults,
      depthValue: provesDepth,
      depthInputId: 'proves-depth-input',
      onDepthChange: (v) => { provesDepth = v; },
      proof,
    }));
  }

function attachHandlers(proof) {
  // Make tokens focusable so keyboard navigation still works:
  dollarAll('.token').forEach(t => t.tabIndex = 0);

  // Click delegation: choose the deepest .token
  pre.addEventListener('click', e => {
    const tokenEl = e.target.closest('.token');
    if (!tokenEl) return;
    renderPanel(tokenEl, proof);
  });

  // Keyboard: keep per-token keydown so focus + Enter/Space works reliably
  dollarAll('.token').forEach(t => {
    t.addEventListener('keydown', e => {
      if (e.key === 'Enter' || e.key === ' ') {
        e.preventDefault();
        renderPanel(e.currentTarget, proof);
      }
    });
  });
}

let currentProof = null;

async function loadCoverage() {
    pre.innerHTML = '';
    panelBody.innerHTML = '';
    panelTitle.textContent = 'Select a token';
    currentProof = null;
    currentTokenEl = null;

    const resp = await fetch('/api/coverage');
    const data = await resp.json();

    if (data.error) {
        pre.textContent = data.error;
        return;
    }

    currentProof = window.parseProof(data.source, data.log);
    const lineStatuses = currentProof.lineStatus;
    const src = window.getSourceCode();
    const fragment = window.generateSpansFragment(src, currentProof);
    buildSourceDomFromFragment(fragment, src, lineStatuses);
    attachHandlers(currentProof);

    const uncovered = document.querySelector('.token[data-status="uncovered"]');
    if (uncovered) renderPanel(uncovered, currentProof);
    else {
        const first = document.querySelector('.token');
        if (first) renderPanel(first, currentProof);
    }
}

async function bootstrap() {
    try {
        await loadCoverage();
    } catch (e) {
        pre.textContent = 'Failed to load coverage: ' + e.message;
    }
}

bootstrap();

// ── Resizable divider ──

(function initDivider() {
  const divider = document.getElementById('divider');
  const panel = document.getElementById('panel');
  const app = document.querySelector('.app');
  if (!divider || !panel || !app) return;

  let dragging = false;
  let startX = 0;
  let startWidth = 0;

  function onPointerDown(e) {
    e.preventDefault();
    dragging = true;
    startX = e.clientX;
    startWidth = panel.getBoundingClientRect().width;
    divider.classList.add('dragging');
    document.body.style.cursor = 'col-resize';
    document.body.style.userSelect = 'none';
  }

  function onPointerMove(e) {
    if (!dragging) return;
    // Panel is on the right, so dragging left increases its width
    const delta = startX - e.clientX;
    const newWidth = Math.max(200, Math.min(startWidth + delta, window.innerWidth - 300));
    panel.style.width = newWidth + 'px';
  }

  function onPointerUp() {
    if (!dragging) return;
    dragging = false;
    divider.classList.remove('dragging');
    document.body.style.cursor = '';
    document.body.style.userSelect = '';
  }

  divider.addEventListener('pointerdown', onPointerDown);
  document.addEventListener('pointermove', onPointerMove);
  document.addEventListener('pointerup', onPointerUp);

  // Keyboard: left/right arrows to resize
  divider.addEventListener('keydown', function(e) {
    const step = 20;
    const current = panel.getBoundingClientRect().width;
    if (e.key === 'ArrowLeft') {
      panel.style.width = Math.min(current + step, window.innerWidth - 300) + 'px';
    } else if (e.key === 'ArrowRight') {
      panel.style.width = Math.max(200, current - step) + 'px';
    }
  });
})();
