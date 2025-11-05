const $ = s => document.querySelector(s);
const $$ = s => Array.from(document.querySelectorAll(s));

const pre = $('#source');
const panelBody = $('#panel-body');
const panelTitle = $('#panel-title');

function escapeHtml(s) {
    return String(s)
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;');
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
    $$('.token').forEach(t => t.classList.remove('selected', 'related'));
}

function renderPanel(tokenEl, proof) {
    const id = tokenEl.dataset.id;
    console.log("Id read is ",id)


    const token =  proof.proofGraph.getNode(id);
    console.log("Token is", token);

    console.log("All elemnts are ", proof.proofGraph.getAllNodes());

    panelTitle.textContent = `Dependency tracker: ${tokenEl.textContent.trim()}`;
    

    let DepensOn = window.getDependsOn(id, proof, 1);
    let DepensOnIds = DepensOn.map(obj => obj.id);

    clearHighlights();

    tokenEl.classList.add('selected');
    DepensOnIds.forEach(uid => { const el = document.querySelector(`[data-id="${uid}"]`); if (el) el.classList.add('related'); });

    panelBody.innerHTML = '';

    panelBody.insertAdjacentHTML('beforeend', `
    <p><strong>Status:</strong> ${String(token.CovStatus)}</p>
    <p><strong>Message:</strong> ${String(token.prooftext)}</p>
    <p><strong>Loc:</strong> ${String(id)}</p>
    `);

    const usedByDiv = document.createElement('div'); usedByDiv.className = 'group';
    usedByDiv.innerHTML = `<strong>All Related (${DepensOnIds.length}):</strong>`;
    const usedByList = document.createElement('ul');
    DepensOnIds.forEach(uid => {
        const tokenbase =  proof.proofGraph.getNode(uid);
        const el = document.querySelector(`[data-id="${uid}"]`);
        const li = document.createElement('li');
        li.textContent = el ? `${el.textContent.trim()} (id=${uid}) (${tokenbase.prooftext})` : uid;
        usedByList.appendChild(li);
    });
    usedByDiv.appendChild(usedByList);
    panelBody.appendChild(usedByDiv);
    const graphDiv = document.createElement('div'); graphDiv.className = 'group';
  }

function attachHandlers(proof) {
  // Make tokens focusable so keyboard navigation still works:
  $$('.token').forEach(t => t.tabIndex = 0);

  // Click delegation: choose the deepest .token
  pre.addEventListener('click', e => {
    const tokenEl = e.target.closest('.token');
    if (!tokenEl) return;
    renderPanel(tokenEl, proof);
  });

  // Keyboard: keep per-token keydown so focus + Enter/Space works reliably
  $$('.token').forEach(t => {
    t.addEventListener('keydown', e => {
      if (e.key === 'Enter' || e.key === ' ') {
        e.preventDefault();
        renderPanel(e.currentTarget, proof);
      }
    });
  });
}

async function bootstrap() {
    const proofFile = "prover_log.txt";
    const sourceFile = "source_code.dfy";

    // Fetch file contents first
    const [dafnyCode, proofLog] = await Promise.all([
        fetch(sourceFile).then(r => r.text()),
        fetch(proofFile).then(r => r.text())
    ]);

    // Then pass the actual content strings to parseProof
    let proof = root.parseProof(dafnyCode, proofLog);
    
    const lineStatuses = proof.lineStatus;

    const src = window.getSourceCode();

    const fragment = window.generateSpansFragment(src, proof);
    buildSourceDomFromFragment(fragment, src, lineStatuses);

    attachHandlers(proof);

    const uncovered = document.querySelector('.token[data-status="uncovered"]');
    if (uncovered) renderPanel(uncovered, proof);
    else {
        const first = document.querySelector('.token');
        if (first) renderPanel(first, proof);
    }

}

bootstrap();
