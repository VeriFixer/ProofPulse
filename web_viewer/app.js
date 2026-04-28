const dollar = s => document.querySelector(s);
const dollarAll = s => Array.from(document.querySelectorAll(s));

const pre = dollar('#source');
const panelBody = dollar('#panel-body');
const panelTitle = dollar('#panel-title');

let currentDepth = 2;
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

function renderPanel(tokenEl, proof) {
    currentTokenEl = tokenEl;
    const id = tokenEl.dataset.id;
    const token = proof.proofGraph.getNode(id);

    const displayCode = getNodeDisplayText(token, 40);
    panelTitle.textContent = `Dependency tracker: ${displayCode}`;

    const results = window.getDependsOn(id, proof, currentDepth) || [];
    const depIds = results.map(r => r.node.id);

    clearHighlights();
    tokenEl.classList.add('selected');
    depIds.forEach(uid => { const el = document.querySelector(`[data-id="${uid}"]`); if (el) el.classList.add('related'); });

    panelBody.innerHTML = '';

    // Engaging summary with colored kind badge and status explanation
    const statusStyle = token.covStatus === 'Uncovered' ? 'color: var(--color-uncovered-text)' :
                        token.covStatus === 'CovTest' ? 'color: var(--color-covtest-text)' :
                        'color: var(--color-covcomplete-text)';

    panelBody.insertAdjacentHTML('beforeend', `
    <p>${typeBadge(token.type)} <strong style="${statusStyle}">${String(token.covStatus)}</strong></p>
    <p class="hint">${escapeHtml(statusExplanation(token.covStatus, token.type))}</p>
    <p><strong>Message:</strong> ${escapeHtml(cleanProoftext(token.prooftext))}</p>
    <p><strong>Loc:</strong> Line ${token.start.line}:${token.start.col} — ${token.end.line}:${token.end.col}</p>
    `);

    // Group results by depth
    const byDepth = new Map();
    results.forEach(r => {
      if (!byDepth.has(r.depth)) byDepth.set(r.depth, []);
      byDepth.get(r.depth).push(r.node);
    });

    const depsDiv = document.createElement('div');
    depsDiv.className = 'deps';

    const sortedDepths = Array.from(byDepth.keys()).sort((a, b) => a - b);
    sortedDepths.forEach(depth => {
      const nodes = byDepth.get(depth);
      const header = document.createElement('div');
      header.className = 'depth-header';
      header.textContent = `Depth ${depth} (${nodes.length})`;
      depsDiv.appendChild(header);

      const ul = document.createElement('ul');
      nodes.forEach(node => {
        const codeText = getNodeDisplayText(node, 60);
        const li = document.createElement('li');
        li.innerHTML = typeBadge(node.type) +
          `<code>${escapeHtml(codeText)}</code>` +
          ` <small>(${escapeHtml(shortLoc(node))})</small>` +
          (node.prooftext ? ` <small class="hint">${escapeHtml(cleanProoftext(node.prooftext))}</small>` : '');
        ul.appendChild(li);
      });
      depsDiv.appendChild(ul);
    });

    if (sortedDepths.length === 0) {
      depsDiv.innerHTML = '<p class="hint">No dependencies found.</p>';
    }

    panelBody.appendChild(depsDiv);
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

    // Wire depth control
    const depthInput = document.getElementById('depth-input');
    if (depthInput) {
        depthInput.addEventListener('input', () => {
            const val = parseInt(depthInput.value, 10);
            currentDepth = isNaN(val) ? 2 : val;
            if (currentTokenEl && currentProof) {
                renderPanel(currentTokenEl, currentProof);
            }
        });
    }

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
