// 航电密钥轮换复核 —— 核心状态模型与穷尽交织搜索
//
// 两枚独立安全模块（控制端到模块为按发起顺序的 FIFO 通道）处理五类指令：
//   prepare   <模块> <密钥指纹>          准备（持久暂存）一枚纪元密钥
//   activate  <模块>                    将已暂存密钥提交为持久纪元
//   issue     <模块> <发布标识>          以当前持久纪元密钥确认一份发布令
//   authorize <模块> <发布标识> <密钥指纹> 为该模块的该发布令持久绑定允许签发的密钥
//   recover   <模块>                    断电恢复：仅重放已落盘记录
//
// 授权语义：某发布令一旦在某模块存在落盘授权，该模块仅在“已持久激活授权密钥且
// 存在匹配的持久授权”时才能形成该发布令的确认；从未配置授权的发布令继续沿用原签发
// 规则（当前持久纪元即签发密钥）。授权本身是持久记录：写入前断电不生效，写入后断电
// 的恢复仅从落盘授权重放；迟到/重复确认同样不得改写模块记录。
//
// 每条指令的生命周期：投递 -> 持久写入 -> 确认；三个边界都可能断电：
//   写入前断电：未落盘，指令丢失；写入后确认前断电：已落盘未确认，恢复后重放，
//   重传/迟到确认不得改变记录；确认后断电：记录已生效，等待恢复后续做。
//
// 模块规范状态（canonical state）仅由四部分构成：
//   持久纪元 ep(-1 未激活 / 0 旧 / 1 新)、准备密钥 prep、
//   持久授权 authz(发布标识 -> 0 旧 / 1 新)、已确认发布集合 bits[id]
// 等价前缀（同调度位置、同规范状态）在穷举中合并。

export const NONE = -1;

// 事件类型（序号即生命周期顺序，也用于同长度见证的稳定排序）
export const EVT = Object.freeze({
  DELIVER: 0, // 投递
  WRITE: 1, // 持久写入
  FAULT_PRE: 2, // 断电：持久写入前
  FAULT_POST: 3, // 断电：持久写入后、确认前
  ACK: 4, // 确认
  FAULT_ACK: 5, // 断电：确认后
  DUP_ACK: 6, // 恢复后到达的迟到/重复确认（必须幂等）
});

export const EVT_LABEL = Object.freeze({
  [EVT.DELIVER]: '投递',
  [EVT.WRITE]: '持久写入',
  [EVT.FAULT_PRE]: '断电（写入前）',
  [EVT.FAULT_POST]: '断电（写入后确认前）',
  [EVT.ACK]: '确认',
  [EVT.FAULT_ACK]: '断电（确认后）',
  [EVT.DUP_ACK]: '迟到/重复确认',
});

export const EVT_VERB = Object.freeze({
  prepare: '准备',
  activate: '激活',
  issue: '签发',
  authorize: '授权',
  recover: '恢复',
});

const OP_ALIASES = Object.freeze({
  prepare: 'prepare',
  activate: 'activate',
  issue: 'issue',
  authorize: 'authorize',
  recover: 'recover',
  准备: 'prepare',
  激活: 'activate',
  签发: 'issue',
  授权: 'authorize',
  恢复: 'recover',
});

// ---------- 输入解析与一次性校验（全部错误一次指出） ----------

// raw: {oldFp, newFp, modules:[{id, epoch:'-1'|'0'|'1', prep:'-1'|'0'|'1', confirmed}],
//        instructionsText}
export function parseModel(raw) {
  const errors = [];
  const oldFp = (raw.oldFp ?? '').trim();
  const newFp = (raw.newFp ?? '').trim();
  if (!oldFp) errors.push('未填写旧密钥指纹。');
  if (!newFp) errors.push('未填写新密钥指纹。');
  if (oldFp && newFp && oldFp === newFp)
    errors.push('旧、新密钥指纹不得相同（轮换必须指向不同纪元密钥）。');
  const fpRe = /^[A-Za-z0-9:_-]+$/;
  for (const [label, fp] of [['旧', oldFp], ['新', newFp]]) {
    if (fp && !fpRe.test(fp))
      errors.push(`${label}密钥指纹包含非法字符（仅允许字母、数字、: _ -）。`);
  }
  const keyOf = (fp) => (fp === oldFp ? 0 : fp === newFp ? 1 : NONE);
  const resolveFp = (token) => (token === '旧' ? oldFp : token === '新' ? newFp : token);

  // 模块标识
  const mods = raw.modules ?? [];
  const ids = [0, 1].map((n) => ((mods[n]?.id ?? '').trim()));
  if (!ids[0]) errors.push('未填写模块 1 的标识。');
  if (!ids[1]) errors.push('未填写模块 2 的标识。');
  if (ids[0] && ids[1] && ids[0] === ids[1])
    errors.push(`两枚模块标识重复：“${ids[0]}”，模块标识必须互不相同。`);
  const targetIndex = (token) => ids.findIndex((id) => id && id === token);

  // 发布标识 intern 表（初态与签发指令统一编号）
  const idTable = [];
  const internId = (id) => {
    let n = idTable.indexOf(id);
    if (n < 0) {
      n = idTable.length;
      idTable.push(id);
    }
    return n;
  };
  const idRe = /^[\w.\-]+$/;

  function parseInitial(m, label) {
    const init = { ep: NONE, prep: NONE, authz: new Map(), bits: new Map() };
    if (!ids[label]) return init;
    const ep = (m.epoch ?? '-1').toString();
    if (ep === '0' || ep === '1') init.ep = Number(ep);
    else if (ep !== '' && ep !== '-1')
      errors.push(`模块“${ids[label]}”的持久纪元初态非法（应为 旧/新/未激活）。`);

    const prep = (m.prep ?? '-1').toString();
    if (prep === '0' || prep === '1') init.prep = Number(prep);
    else if (prep !== '' && prep !== '-1')
      errors.push(`模块“${ids[label]}”的准备密钥初态非法（应为 旧/新/未激活）。`);

    const text = (m.confirmed ?? '').trim();
    for (let part of text ? text.split(',') : []) {
      part = part.trim();
      if (!part) continue;
      const seg = part.split(':');
      if (seg.length !== 2 || !seg[0].trim() || !seg[1].trim()) {
        errors.push(
          `模块“${ids[label]}”的已确认初态条目“${part}”格式非法，应为 发布标识:密钥指纹。`,
        );
        continue;
      }
      const pid = seg[0].trim();
      const fp = resolveFp(seg[1].trim());
      if (!idRe.test(pid)) {
        errors.push(
          `模块“${ids[label]}”初态发布标识“${pid}”含非法字符（允许字母数字 _ . -）。`,
        );
        continue;
      }
      const k = keyOf(fp);
      if (k === NONE) {
        errors.push(
          `模块“${ids[label]}”初态中的密钥指纹“${fp}”不是已声明的旧或新密钥。`,
        );
        continue;
      }
      const n = internId(pid);
      init.bits.set(n, (init.bits.get(n) ?? 0) | (1 << k));
    }
    return init;
  }

  const inits = [0, 1].map((n) => parseInitial(mods[n] ?? {}, n));

  // 指令解析（控制端发起顺序即行序，至多 16 条）
  const instructions = [];
  let lineNo = 0;
  for (const rawLine of (raw.instructionsText ?? '').split(/\r?\n/)) {
    lineNo += 1;
    const line = rawLine.trim();
    if (!line || line.startsWith('#')) continue; // 空行与 # 注释行不计入指令
    if (instructions.length >= 16) {
      errors.push(`第 ${lineNo} 行：指令数量超过上限 16 条，超出部分不予受理。`);
      break;
    }
    const tokens = line.split(/\s+/);
    const opToken = tokens[0];
    const op = OP_ALIASES[opToken.toLowerCase?.() ?? opToken] ?? OP_ALIASES[opToken];
    const where = `第 ${lineNo} 行指令“${line}”`;
    if (!op) {
      errors.push(
        `${where}：未知指令类型“${opToken}”，应为 prepare/activate/issue/authorize/recover（准备/激活/签发/授权/恢复）。`,
      );
      continue;
    }
    const targetTok = tokens[1] ?? '';
    if (!targetTok) {
      errors.push(`${where}：缺少指令目标模块标识。`);
      continue;
    }
    const mi = targetIndex(targetTok);
    if (mi < 0) {
      errors.push(`${where}：目标模块“${targetTok}”不是已声明的两枚模块之一。`);
      continue;
    }
    const arg = tokens[2] ?? '';
    const arg2 = tokens[3] ?? '';
    const extra = tokens[4];
    const rec = { idx: instructions.length, lineNo, op, target: mi, arg: null, text: line };
    if (op === 'prepare') {
      if (!arg || tokens[3]) {
        errors.push(`${where}：准备指令格式应为 prepare <模块> <密钥指纹>。`);
      } else {
        const k = keyOf(resolveFp(arg));
        if (k === NONE)
          errors.push(`${where}：密钥指纹“${arg}”不是已声明的旧或新密钥。`);
        rec.arg = k;
      }
    } else if (op === 'issue') {
      if (!arg || tokens[3]) {
        errors.push(`${where}：签发指令格式应为 issue <模块> <发布标识>。`);
      } else if (!idRe.test(arg)) {
        errors.push(`${where}：发布标识“${arg}”含非法字符（允许字母数字 _ . -）。`);
      } else {
        rec.arg = internId(arg);
      }
    } else if (op === 'authorize') {
      // authorize <模块> <发布标识> <密钥指纹>：落盘后该发布令只能由授权密钥确认
      if (!arg || !arg2 || extra) {
        errors.push(`${where}：授权指令格式应为 authorize <模块> <发布标识> <密钥指纹>。`);
      } else {
        let idOk = true;
        if (!idRe.test(arg)) {
          errors.push(`${where}：发布标识“${arg}”含非法字符（允许字母数字 _ . -）。`);
          idOk = false;
        }
        const k = keyOf(resolveFp(arg2));
        if (k === NONE)
          errors.push(
            `${where}：授权密钥指纹“${arg2}”不是已声明的旧或新密钥（授权只能绑定已声明的纪元密钥）。`,
          );
        if (idOk && k !== NONE) rec.arg = { id: internId(arg), key: k };
      }
    } else if (arg) {
      errors.push(`${where}：${op === 'activate' ? '激活' : '恢复'}指令不接受额外参数。`);
    }
    instructions.push(rec);
  }

  // 授权冲突一次性校验：同一模块同一发布令不得出现两条授权指令
  // （相同指纹＝重复授权；不同指纹＝改绑不同指纹）。
  const authzSeen = [new Map(), new Map()];
  for (const ins of instructions) {
    if (ins.op !== 'authorize' || !ins.arg) continue;
    const { id, key } = ins.arg;
    const seen = authzSeen[ins.target];
    const prev = seen.get(id);
    if (prev) {
      const pid = idTable[id];
      if (prev.key === key) {
        errors.push(
          `第 ${ins.lineNo} 行：模块“${ids[ins.target]}”对发布令“${pid}”的授权重复（第 ${prev.lineNo} 行已绑定${prev.key === 0 ? '旧' : '新'}密钥 ${[oldFp, newFp][key]}）；同一模块同一发布令只需授权一次。`,
        );
      } else {
        errors.push(
          `第 ${ins.lineNo} 行：模块“${ids[ins.target]}”对发布令“${pid}”改绑了与第 ${prev.lineNo} 行不同的密钥指纹（${[oldFp, newFp][prev.key]} → ${[oldFp, newFp][key]}）；已授权发布令不得改绑其他密钥。`,
        );
      }
    } else {
      seen.set(id, { key, lineNo: ins.lineNo });
    }
  }

  // 恢复前无故障：恢复指令之前，同模块必须存在可断电的在先指令。
  const seenTarget = [false, false];
  for (const ins of instructions) {
    if (ins.op === 'recover' && !seenTarget[ins.target]) {
      errors.push(
        `第 ${ins.lineNo} 行：模块“${ids[ins.target]}”在此恢复指令之前没有任何在先指令可能断电（恢复前无故障）。`,
      );
    }
    seenTarget[ins.target] = true;
  }

  if (errors.length) return { errors };

  // 统一补齐每个模块的持久授权数组与已确认位向量（按发布标识编号对齐）
  for (const init of inits) {
    const az = new Array(idTable.length).fill(NONE);
    for (const [n, k] of init.authz) az[n] = k;
    init.authz = az;
    const arr = new Array(idTable.length).fill(0);
    for (const [n, b] of init.bits) arr[n] = b;
    init.bits = arr;
  }

  return {
    model: {
      keys: [oldFp, newFp],
      moduleIds: [ids[0], ids[1]],
      inits,
      instructions,
      idTable,
      queues: [
        instructions.filter((x) => x.target === 0).map((x) => x.idx),
        instructions.filter((x) => x.target === 1).map((x) => x.idx),
      ],
    },
  };
}

// ---------- 规范状态与穷举搜索 ----------

function canonKey(c) {
  const parts = [];
  for (let i = 0; i < c.bits.length; i++) if (c.bits[i]) parts.push(`${i}:${c.bits[i]}`);
  const authz = [];
  for (let i = 0; i < c.authz.length; i++) if (c.authz[i] !== NONE) authz.push(`${i}:${c.authz[i]}`);
  return `${c.ep === NONE ? 2 : c.ep}/${c.prep === NONE ? 2 : c.prep}/A{${authz.join(',')}}/B{${parts.join(',')}}`;
}

function stateKey(s) {
  // 注意：late（可能到达的迟到确认集合）不进入状态键。
  // 迟到/重复确认纯无效果且不阻塞任何其他事件，其“何时消化”不影响规范状态与
  // 安全性（幂等不变量），故 DUP_ACK 在 BFS 中按自环吸收，避免消化时机组合爆炸。
  return [
    `${s.h[0]}.${s.h[1]}`,
    `${s.mode[0]}${s.mode[1]}`,
    s.infl[0] ? `${s.infl[0].i}.${s.infl[0].ph}` : '-',
    s.infl[1] ? `${s.infl[1].i}.${s.infl[1].ph}` : '-',
    canonKey(s.canon[0]),
    canonKey(s.canon[1]),
  ].join('|');
}

function initialState(model) {
  return {
    h: [0, 0],
    mode: [0, 0], // 0 在线  1 断电
    infl: [null, null], // 在途指令 {i, ph: 0已投递/1已落盘}
    // 各指令断电后可能晚到的确认（不论其写入是否落盘）；恢复后消化，必须全部幂等
    late: [[], []],
    canon: [
      {
        ep: model.inits[0].ep,
        prep: model.inits[0].prep,
        authz: model.inits[0].authz.slice(),
        bits: model.inits[0].bits.slice(),
      },
      {
        ep: model.inits[1].ep,
        prep: model.inits[1].prep,
        authz: model.inits[1].authz.slice(),
        bits: model.inits[1].bits.slice(),
      },
    ],
  };
}

function cloneState(s) {
  return {
    h: [s.h[0], s.h[1]],
    mode: [s.mode[0], s.mode[1]],
    infl: [s.infl[0] ? { ...s.infl[0] } : null, s.infl[1] ? { ...s.infl[1] } : null],
    late: [s.late[0].slice(), s.late[1].slice()],
    canon: [
      { ep: s.canon[0].ep, prep: s.canon[0].prep, authz: s.canon[0].authz, bits: s.canon[0].bits },
      { ep: s.canon[1].ep, prep: s.canon[1].prep, authz: s.canon[1].authz, bits: s.canon[1].bits },
    ],
  };
}

function writeEffect(ins, canon) {
  // 落盘对规范状态的效果；无效应写入（重复暂存/激活、无密钥激活、未激活签发、
  // 授权密钥不匹配的签发、重复授权、恢复）返回 false。
  switch (ins.op) {
    case 'prepare':
      if (canon.prep === ins.arg) return false;
      canon.prep = ins.arg;
      return true;
    case 'activate':
      if (canon.prep === NONE || canon.ep === canon.prep) return false;
      canon.ep = canon.prep;
      return true;
    case 'issue': {
      if (canon.ep === NONE) return false; // 未持久激活：签发不成立
      const bound = canon.authz[ins.arg];
      // 该发布令已存在持久授权：仅当持久激活的纪元密钥与授权指纹一致时确认才成立
      if (bound !== NONE && bound !== canon.ep) return false;
      canon.bits = canon.bits.slice();
      canon.bits[ins.arg] |= 1 << canon.ep;
      return true;
    }
    case 'authorize': {
      // 持久绑定允许签发的密钥；重复授权（含解析层漏网者）为无效应写入
      const { id, key } = ins.arg;
      if (canon.authz[id] === key) return false;
      canon.authz = canon.authz.slice();
      canon.authz[id] = key;
      return true;
    }
    case 'recover':
      return false; // 规范状态本就等于落盘记录的重放结果
  }
  return false;
}

// 从状态 s 出发的全部一步迁移，已按 (模块, 指令序号, 事件类型) 稳定排序。
function addLate(late, m, i) {
  // FIFO 保证插入序号单调递增；保持集合有序便于规范键稳定
  if (!late[m].includes(i)) late[m].push(i);
}

function transitions(s, model) {
  const out = [];
  for (let m = 0; m < 2; m++) {
    const head = s.h[m] < model.queues[m].length ? model.queues[m][s.h[m]] : null;

    // 恢复在线后，各断电指令的迟到/重复确认可任意顺序到达；不改变规范状态，也不阻塞投递
    if (s.mode[m] === 0) {
      for (const i of s.late[m]) {
        out.push({
          m,
          i,
          kind: EVT.DUP_ACK,
          build: (ns) => {
            ns.late[m] = ns.late[m].filter((x) => x !== i);
          },
        });
      }
    }

    // 投递队首：FIFO 保证该模块的控制端发起顺序。
    // 断电中正常指令也可到达模块，但尚未持久化即丢失（等价于写入前断电）；
    // 不落盘的内容恢复时不会重放。恢复指令在断电中同样可投递。
    if (s.infl[m] === null && head !== null) {
      out.push({
        m,
        i: head,
        kind: EVT.DELIVER,
        build: (ns) => {
          ns.h[m] += 1;
          ns.infl[m] = { i: head, ph: 0 };
        },
      });
    }

    const inf = s.infl[m];
    if (inf && inf.ph === 0) {
      const ins = model.instructions[inf.i];
      out.push({
        // 写入前断电：未落盘，指令丢失（断电期间到达同样落此结果），其确认标记为迟到
        m,
        i: inf.i,
        kind: EVT.FAULT_PRE,
        build: (ns) => {
          ns.infl[m] = null;
          ns.mode[m] = 1;
          addLate(ns.late, m, inf.i);
        },
      });
      if (s.mode[m] === 0 || ins.op === 'recover') {
        out.push({
          // 持久写入（在线写入；断电中仅恢复指令执行落盘重放并使模块恢复在线）
          m,
          i: inf.i,
          kind: EVT.WRITE,
          build: (ns) => {
            writeEffect(ins, ns.canon[m]);
            if (ins.op === 'recover') ns.mode[m] = 0;
            ns.infl[m] = { i: inf.i, ph: 1 };
          },
        });
      }
    } else if (inf && inf.ph === 1) {
      const ins = model.instructions[inf.i];
      out.push({
        // 写入后确认前断电：效果已落盘，确认丢失，恢复后该确认作为迟到确认重放
        m,
        i: inf.i,
        kind: EVT.FAULT_POST,
        build: (ns) => {
          ns.infl[m] = null;
          ns.mode[m] = 1;
          addLate(ns.late, m, inf.i);
        },
      });
      out.push({
        // 确认完成
        m,
        i: inf.i,
        kind: EVT.ACK,
        build: (ns) => {
          ns.infl[m] = null;
        },
      });
      out.push({
        // 确认后断电：记录已生效，对端/重传的确认在恢复后仍可能到达
        m,
        i: inf.i,
        kind: EVT.FAULT_ACK,
        build: (ns) => {
          ns.infl[m] = null;
          ns.mode[m] = 1;
          addLate(ns.late, m, inf.i);
        },
      });
    }
  }
  out.sort((a, b) => a.m - b.m || a.i - b.i || a.kind - b.kind);
  return out.map((t) => {
    const ns = cloneState(s);
    t.build(ns);
    return { m: t.m, i: t.i, kind: t.kind, ns };
  });
}

function isViolation(model, s) {
  // 同标识发布被两模块以不同纪元密钥确认（各自确认位掩码非空且不一致）
  const a = s.canon[0].bits;
  const b = s.canon[1].bits;
  for (let i = 0; i < model.idTable.length; i++) {
    if (a[i] && b[i] && a[i] !== b[i]) return i;
  }
  return null;
}

// 父边：{p: 父状态键, m, kind, i}；违约候选各自挂独立节点，避免覆盖。
function chainLess(parent, getParent, k1, k2) {
  const pull = (get, k) => {
    const seq = [];
    while (k !== null) {
      const e = get(k);
      if (!e || e.p === null) break;
      seq.push([e.m, e.i ?? -1, e.kind]);
      k = e.p;
    }
    return seq.reverse();
  };
  const a = pull(getParent, k1);
  const b = pull(getParent, k2);
  const n = Math.min(a.length, b.length);
  for (let d = 0; d < n; d++) {
    for (let c = 0; c < 3; c++) {
      if (a[d][c] !== b[d][c]) return a[d][c] < b[d][c];
    }
  }
  return a.length < b.length;
}

// onProgress({visited, depth, merges}) 可周期性返回 true 请求停止（UI 取消）。
export function explore(model, onProgress) {
  const start = initialState(model);
  const k0 = stateKey(start);
  const states = new Map([[k0, start]]);
  const parent = new Map([[k0, { p: null }]]);
  const visited = new Set([k0]);
  const canonJoint = new Set([`${canonKey(start.canon[0])}||${canonKey(start.canon[1])}`]);

  let merges = 0;
  let terminals = 0;
  let depth = 0;
  let cancelled = false;
  const eventCounts = new Array(7).fill(0); // 各事件类型在穷举中出现的迁移数

  const startBad = isViolation(model, start);
  let bestNode = startBad === null ? null : { key: k0, badParent: null, idIdx: startBad };

  let frontier = [k0];
  let representativeTerminal = null; // 任一耗尽全部队列的终态键（供安全摘要展示）
  let terminalBothOnline = false;
  while (!bestNode && frontier.length && !cancelled) {
    const nextLayer = new Map();
    const badNodes = []; // {key, edge:{p,m,kind,i}, idIdx}
    let badSeq = 0;
    for (const key of frontier) {
      const s = states.get(key);
      const ts = transitions(s, model);
      if (ts.length === 0) {
        terminals += 1;
        // 优先记录双模块均在线恢复的平静终态
        if (
          representativeTerminal === null ||
          (s.mode[0] === 0 && s.mode[1] === 0 && !terminalBothOnline)
        ) {
          representativeTerminal = key;
          terminalBothOnline = s.mode[0] === 0 && s.mode[1] === 0;
        }
      }
      for (const t of ts) {
        eventCounts[t.kind] += 1;
        const nk = stateKey(t.ns);
        const bad = isViolation(model, t.ns);
        if (bad !== null) {
          // 违约状态不再展开；每个候选独立挂节点，保留完整父链信息
          const bk = `bad#${badSeq++}`;
          badNodes.push({ key: bk, edge: { p: key, m: t.m, kind: t.kind, i: t.i }, idIdx: bad });
          continue;
        }
        if (visited.has(nk) || nextLayer.has(nk)) {
          merges += 1;
          continue;
        }
        nextLayer.set(nk, { from: key, m: t.m, kind: t.kind, i: t.i });
        states.set(nk, t.ns);
        canonJoint.add(`${canonKey(t.ns.canon[0])}||${canonKey(t.ns.canon[1])}`);
      }
    }
    if (badNodes.length) {
      // 首次出现违约的层即最短动作数；候选间按 (模块, 指令标识, 事件) 稳定序取最小
      const badParent = new Map();
      for (const b of badNodes) badParent.set(b.key, b.edge);
      const getEdge = (k) => badParent.get(k) ?? parent.get(k);
      let best = badNodes[0];
      for (const b of badNodes.slice(1)) {
        if (chainLess(null, getEdge, b.key, best.key)) best = b;
      }
      bestNode = { key: best.key, badParent, idIdx: best.idIdx };
      break;
    }
    for (const [nk, e] of nextLayer) {
      visited.add(nk);
      parent.set(nk, { p: e.from, m: e.m, kind: e.kind, i: e.i });
    }
    frontier = [...nextLayer.keys()];
    depth += 1;
    if (onProgress && depth % 2 === 0) {
      cancelled = !!onProgress({ visited: visited.size, depth, merges });
    }
  }

  if (cancelled) return { cancelled: true };

  const summary = {
    visited: visited.size,
    depth,
    merges,
    terminals,
    distinctCanon: canonJoint.size,
    eventCounts: eventCounts.slice(),
  };

  if (!bestNode) {
    const terminalState = representativeTerminal ? states.get(representativeTerminal) : start;
    return {
      violation: false,
      summary,
      terminalSnapshot: snapshot(model, terminalState, null),
    };
  }

  // 重建最短见证动作序列，并从初态逐步重放取得每步双模块快照
  const getEdge = (k) => (bestNode.badParent?.get(k) ?? parent.get(k));
  const actions = [];
  for (let k = bestNode.key; ; ) {
    const e = getEdge(k);
    if (!e || e.p === null) break;
    actions.push({ m: e.m, kind: e.kind, i: e.i });
    k = e.p;
  }
  actions.reverse();

  const steps = [snapshot(model, start, null)];
  let s = start;
  for (const a of actions) {
    const ts = transitions(s, model);
    const t = ts.find((x) => x.m === a.m && x.kind === a.kind && x.i === a.i);
    if (!t) throw new Error(`内部错误：见证重放失败 m=${a.m} i=${a.i} kind=${a.kind}`);
    s = t.ns;
    steps.push(snapshot(model, s, a));
  }

  const idIdx = bestNode.idIdx;
  const last = steps[steps.length - 1];
  const conflictKeys = [0, 1].map((m) => {
    const entry = last.modules[m].confirmed.find((x) => x.idIdx === idIdx);
    const az = last.modules[m].authz.find((x) => x.idIdx === idIdx);
    return {
      module: m,
      bits: entry.bits,
      epoch: last.modules[m].epoch,
      authzKey: az ? az.key : NONE, // NONE 表示该模块从未为该发布令落盘授权
    };
  });

  return {
    violation: true,
    conflictId: model.idTable[idIdx],
    conflictKeys,
    witnessActions: actions,
    steps,
    summary,
  };
}

function snapshot(model, s, action) {
  const fmt = (m) => ({
    mode: s.mode[m] === 0 ? 'online' : 'down',
    epoch: s.canon[m].ep,
    prep: s.canon[m].prep,
    authz: s.canon[m].authz
      .map((key, idIdx) => ({ idIdx, id: model.idTable[idIdx], key }))
      .filter((x) => x.key !== NONE),
    confirmed: s.canon[m].bits
      .map((bits, idIdx) => ({ idIdx, id: model.idTable[idIdx], bits }))
      .filter((x) => x.bits),
  });
  return {
    action: action ? { module: action.m, kind: action.kind, index: action.i } : null,
    modules: [fmt(0), fmt(1)],
  };
}

export function analyze(raw, onProgress) {
  const parsed = parseModel(raw);
  if (parsed.errors) return { ok: false, errors: parsed.errors };
  const report = explore(parsed.model, onProgress);
  if (report.cancelled) return { ok: false, cancelled: true };
  return {
    ok: true,
    model: {
      keys: parsed.model.keys,
      moduleIds: parsed.model.moduleIds,
      idTable: parsed.model.idTable,
      instructions: parsed.model.instructions.map((x) => ({
        idx: x.idx,
        lineNo: x.lineNo,
        op: x.op,
        target: x.target,
        arg: x.arg,
        text: x.text,
      })),
    },
    report,
  };
}
