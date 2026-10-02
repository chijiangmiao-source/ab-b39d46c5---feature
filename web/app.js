// 复核台前端逻辑：收集草稿 → Worker 穷尽 → 渲染结论 / 错误 / 最短见证。
import { EVT, EVT_LABEL, EVT_VERB } from '../src/core.mjs';

const $ = (sel) => document.querySelector(sel);
const els = {
  oldFp: $('#oldFp'),
  newFp: $('#newFp'),
  prog: $('#prog'),
  run: $('#btn-run'),
  clear: $('#btn-clear'),
  stop: $('#btn-stop'),
  counter: $('#counter'),
  progress: $('#progress'),
  errors: $('#errors'),
  result: $('#result'),
  placeholder: $('#placeholder'),
};

function moduleInputs() {
  return [0, 1].map((n) => {
    const panel = $(`#modpanel-${n}`);
    const get = (f) => panel.querySelector(`[data-f="${f}"]`);
    return { id: get('id').value, epoch: get('epoch').value, prep: get('prep').value, confirmed: get('confirmed').value };
  });
}

function collectDraft() {
  return {
    oldFp: els.oldFp.value,
    newFp: els.newFp.value,
    modules: moduleInputs(),
    instructionsText: els.prog.value,
  };
}

function clearConclusion() {
  els.errors.hidden = true;
  els.errors.innerHTML = '';
  els.result.hidden = true;
  els.result.innerHTML = '';
  els.progress.hidden = true;
  els.progress.textContent = '';
  els.placeholder.hidden = false;
}

function setRunning(running) {
  els.run.disabled = running;
  els.clear.disabled = running;
  els.stop.hidden = !running;
}

let worker = null;
let runSeq = 0;

function terminateWorker() {
  if (worker) {
    worker.terminate();
    worker = null;
  }
}

function runReview() {
  clearConclusion(); // 每次复核先清除旧结论
  const seq = ++runSeq;
  setRunning(true);
  els.placeholder.hidden = true;
  els.progress.hidden = false;
  els.progress.textContent = 'Worker 穷举中…';

  terminateWorker();
  worker = new Worker('/worker.mjs', { type: 'module' });
  worker.onmessage = (e) => {
    const msg = e.data;
    if (msg.type === 'progress') {
      els.progress.textContent =
        `Worker 穷举中…　深度 ${msg.depth} 层　已访问状态 ${msg.visited.toLocaleString()}　合并等价前缀 ${msg.merges.toLocaleString()}`;
      return;
    }
    if (msg.type !== 'done' || seq !== runSeq) return;
    setRunning(false);
    els.progress.hidden = true;
    terminateWorker();
    renderResult(msg.result);
  };
  worker.onerror = (ev) => {
    if (seq !== runSeq) return;
    setRunning(false);
    els.progress.hidden = true;
    terminateWorker();
    showErrors([`Worker 执行失败：${ev.message || ev.error || '未知错误'}`]);
  };
  worker.postMessage({ type: 'run', draft: collectDraft() });
}

function showErrors(errors) {
  clearConclusion();
  const h = document.createElement('h3');
  h.textContent = `复核未通过：发现 ${errors.length} 处问题（已一次列出并清除旧结论）`;
  const ol = document.createElement('ol');
  for (const err of errors) {
    const li = document.createElement('li');
    li.textContent = err;
    ol.appendChild(li);
  }
  els.errors.appendChild(h);
  els.errors.appendChild(ol);
  els.errors.hidden = false;
}

function renderResult(res) {
  if (!res.ok) {
    showErrors(res.errors || ['未知校验错误']);
    return;
  }
  const { model, report } = res;
  const root = document.createElement('div');
  root.appendChild(buildVerdict(model, report));
  root.appendChild(buildStats(report.summary));
  if (report.violation) {
    root.appendChild(buildTrace(model, report));
  } else {
    root.appendChild(buildTerminal(model, report.terminalSnapshot));
    root.appendChild(buildEventCoverage(report.summary.eventCounts));
  }
  els.result.appendChild(root);
  els.result.hidden = false;
}

function epochLabel(model, ep) {
  if (ep === -1) return { text: '未激活', cls: 'epochnone' };
  return { text: `纪元 ${ep === 0 ? '旧' : '新'}（${model.keys[ep]}）`, cls: `epoch-${ep}` };
}

function confirmedBitsHtml(model, confirmed) {
  if (!confirmed.length) return '<span class="epochnone">∅</span>';
  return confirmed
    .map((c) => {
      const which = c.bits === 3 ? 'both' : c.bits === 1 ? 'old' : c.bits === 2 ? 'new' : 'both';
      const keyTxt =
        c.bits === 3
          ? '旧+新'
          : c.bits === 1
            ? `旧 ${model.keys[0]}`
            : c.bits === 2
              ? `新 ${model.keys[1]}`
              : '?';
      return `<span class="badge ${which}">${escapeHtml(c.id)}：${escapeHtml(keyTxt)}</span>`;
    })
    .join(' ');
}

function authzHtml(model, authz) {
  if (!authz.length) return '<span class="epochnone">无授权</span>';
  return authz
    .map((a) => {
      const which = a.key === 0 ? 'old' : 'new';
      return `<span class="badge authz ${which}">${escapeHtml(a.id)}→仅${a.key === 0 ? '旧' : '新'} ${escapeHtml(model.keys[a.key])}</span>`;
    })
    .join(' ');
}

function moduleStateHtml(model, ms) {
  const ep = epochLabel(model, ms.epoch);
  const prep = ms.prep === -1 ? '无' : ms.prep === 0 ? '旧' : '新';
  const modeBadge = ms.mode === 'down'
    ? '<span class="badge down">断电</span>'
    : '<span class="badge online">在线</span>';
  return `<div class="modstate">${modeBadge}
    <span class="epoch ${ep.cls}">${ep.text}</span>
    <span class="epochnone">准备:${prep}</span>
    <div class="authzrow"><span class="rowlbl">持久授权</span> ${authzHtml(model, ms.authz)}</div>
    <div class="conf"><span class="rowlbl">确认</span> ${confirmedBitsHtml(model, ms.confirmed)}</div></div>`;
}

function buildVerdict(model, report) {
  const div = document.createElement('div');
  if (report.violation) {
    div.className = 'verdict unsafe';
    const m = report.conflictKeys
      .map((c) => {
        const keyTxt = c.bits === 1 ? `旧密钥 ${model.keys[0]}` : c.bits === 2 ? `新密钥 ${model.keys[1]}` : `位掩码 ${c.bits}`;
        const active = c.epoch === -1 ? '未激活' : `持久激活${c.epoch === 0 ? '旧' : '新'}密钥`;
        const bind =
          c.authzKey === -1
            ? '该令无持久授权（沿用原签发规则）'
            : `持久授权仅允许${c.authzKey === 0 ? '旧' : '新'}密钥 ${model.keys[c.authzKey]}`;
        return `${model.moduleIds[c.module]} 以 ${keyTxt}确认（${active}；${bind}）`;
      })
      .join('，');
    div.innerHTML =
      `<div class="big">⚠ 发现违约：发布令 <span class="cid">${escapeHtml(report.conflictId)}</span> 被双模块以不同纪元密钥共同确认</div>
       <div class="detail">${escapeHtml(m)}。以下交织动作数最短（${report.witnessActions.length} 步），同长度按（模块, 指令标识, 事件）稳定排序；逐步表中可对照两模块的持久授权、持久激活与确认状态，区分未授权签发被阻止与不同纪元共同确认。</div>`;
  } else {
    div.className = 'verdict safe';
    div.innerHTML =
      '<div class="big">✓ 安全：穷尽全部保持控制端顺序的投递 / 断电 / 恢复交织，不存在跨纪元密钥共同确认</div>' +
      `<div class="detail">已覆盖状态摘要见下，等价前缀已合并；授权仅在落盘后生效，恢复只重放落盘授权，未匹配持久授权的签发不能形成确认，迟到/重复确认不改变模块记录。</div>`;
  }
  return div;
}

function buildStats(summary) {
  const wrap = document.createElement('div');
  const items = [
    ['已访问状态', summary.visited],
    ['最大深度（动作数）', summary.depth],
    ['合并等价前缀', summary.merges],
    ['终态数', summary.terminals],
    ['规范联合状态', summary.distinctCanon],
  ];
  wrap.innerHTML =
    '<h3 class="section">覆盖状态摘要</h3><div class="summarygrid">' +
    items.map(([t, n]) => `<div class="stat"><div class="n">${Number(n).toLocaleString()}</div><div class="t">${t}</div></div>`).join('') +
    '</div>';
  return wrap;
}

const EVENT_CLS = {
  [EVT.FAULT_PRE]: 'kind-fault',
  [EVT.FAULT_POST]: 'kind-fault',
  [EVT.FAULT_ACK]: 'kind-fault',
  [EVT.DUP_ACK]: 'kind-dup',
};

function instructionLabel(model, idx) {
  if (idx === null || idx === undefined) return '';
  const ins = model.instructions[idx];
  const target = model.moduleIds[ins.target];
  let arg = '';
  if (ins.op === 'prepare') arg = ins.arg === 0 ? model.keys[0] : model.keys[1];
  if (ins.op === 'issue') arg = model.idTable[ins.arg];
  if (ins.op === 'authorize')
    arg = `${model.idTable[ins.arg.id]} ${model.keys[ins.arg.key]}`;
  return `#${ins.idx} ${EVT_VERB[ins.op]} ${target}${arg ? ' ' + arg : ''}`;
}

function buildTrace(model, report) {
  const wrap = document.createElement('div');
  const head =
    '<h3 class="section">最短违约完整交织（逐步双模块状态）</h3>' +
    `<div class="hint">动作序号从 1 开始；第 0 行为持久初态。指令编号 #n 即控制端发起顺序。</div>`;
  const rows = report.steps
    .map((step, n) => {
      let actionCell = '<span class="epochnone">初态</span>';
      if (step.action) {
        const a = step.action;
        const cls = EVENT_CLS[a.kind] ?? '';
        const modName = model.moduleIds[a.module];
        actionCell = `<div class="ev"><span class="kind ${cls}">${EVT_LABEL[a.kind]}</span></div>`
          + `<div class="hint">${escapeHtml(modName)} · ${escapeHtml(instructionLabel(model, a.index))}</div>`;
      }
      return `<tr class="${n === 0 ? 'step-initial' : ''}">
        <td class="stepno">${n}</td>
        <td>${actionCell}</td>
        <td>${moduleStateHtml(model, step.modules[0])}</td>
        <td>${moduleStateHtml(model, step.modules[1])}</td>
      </tr>`;
    })
    .join('');
  wrap.innerHTML =
    head +
    `<table class="trace"><thead><tr>
      <th>#</th><th>动作</th><th>${escapeHtml(model.moduleIds[0])} 状态</th><th>${escapeHtml(model.moduleIds[1])} 状态</th>
    </tr></thead><tbody>${rows}</tbody></table>`;
  return wrap;
}

function buildTerminal(model, snap) {
  const wrap = document.createElement('div');
  wrap.innerHTML =
    '<h3 class="section">代表性终态（全部指令耗尽后的双模块规范状态）</h3>' +
    `<table class="trace"><thead><tr><th>${escapeHtml(model.moduleIds[0])}</th><th>${escapeHtml(model.moduleIds[1])}</th></tr></thead>
     <tbody><tr><td>${moduleStateHtml(model, snap.modules[0])}</td><td>${moduleStateHtml(model, snap.modules[1])}</td></tr></tbody></table>`;
  return wrap;
}

function buildEventCoverage(counts) {
  const wrap = document.createElement('div');
  const names = [
    '投递', '持久写入', '断电(写入前)', '断电(写入后确认前)',
    '确认', '断电(确认后)', '迟到/重复确认',
  ];
  wrap.innerHTML =
    '<h3 class="section">事件枚举覆盖（穷举中出现的迁移数）</h3>' +
    '<div class="summarygrid">' +
    names
      .map((n, i) => `<div class="stat"><div class="n">${Number(counts[i]).toLocaleString()}</div><div class="t">${n}</div></div>`)
      .join('') +
    '</div>';
  return wrap;
}

function escapeHtml(s) {
  return String(s).replace(/[&<>"']/g, (ch) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[ch]));
}

// 事件绑定
els.run.addEventListener('click', runReview);
els.stop.addEventListener('click', () => {
  runSeq++;
  terminateWorker();
  setRunning(false);
  els.progress.hidden = true;
  els.placeholder.hidden = false;
  els.placeholder.textContent = '已停止穷举，可修改草稿后重新复核。';
});
els.clear.addEventListener('click', () => {
  terminateWorker();
  runSeq++;
  setRunning(false);
  els.oldFp.value = '';
  els.newFp.value = '';
  els.prog.value = '';
  document.querySelectorAll('.modpanel input[data-f]').forEach((i) => {
    if (i.tagName === 'INPUT') i.value = '';
  });
  document.querySelectorAll('.modpanel select[data-f]').forEach((s) => {
    s.value = '-1';
  });
  els.counter.textContent = '';
  clearConclusion();
  els.placeholder.textContent = '尚未复核。穷举在浏览器 Worker 中执行，不占用页面交互。';
});

// 指令计数
function updateCounter() {
  const n = els.prog.value.split(/\r?\n/).map((l) => l.trim()).filter((l) => l && !l.startsWith('#')).length;
  els.counter.textContent = `已录入 ${n} / 16 条指令${n > 16 ? '（超出上限）' : ''}`;
  els.counter.style.color = n > 16 ? 'var(--bad)' : '';
}
els.prog.addEventListener('input', updateCounter);
updateCounter();
