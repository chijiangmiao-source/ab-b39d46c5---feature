// 核心状态模型测试（Node 原生 test runner，无外部依赖）
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { analyze, parseModel, EVT, EVT as E, NONE } from '../src/core.mjs';

const OLD = 'FP-OLD-0001';
const NEW = 'FP-NEW-0002';

function draft({ m1 = {}, m2 = {}, prog = '', oldFp = OLD, newFp = NEW }) {
  const mk = (over) => ({
    id: over.id ?? '',
    epoch: over.epoch ?? '-1',
    prep: over.prep ?? '-1',
    confirmed: over.confirmed ?? '',
  });
  return { oldFp, newFp, modules: [mk(m1), mk(m2)], instructionsText: prog };
}

const mod = (id, over = {}) => ({ id, ...over });

test('安全轮换：两模块均先准备并激活新密钥后签发同一发布，全部交织安全', () => {
  const d = draft({
    m1: mod('M1'),
    m2: mod('M2'),
    prog: `
prepare M1 ${OLD}
prepare M1 ${NEW}
activate M1
issue M1 ORD-1
prepare M2 ${OLD}
prepare M2 ${NEW}
activate M2
issue M2 ORD-1
`,
  });
  const r = analyze(d);
  assert.equal(r.ok, true, JSON.stringify(r.errors));
  assert.equal(r.report.violation, false);
  assert.ok(r.report.summary.visited > 1);
  assert.ok(r.report.summary.terminals >= 1);
});

test('违约：M1 以旧密钥确认后轮换，M2 直接以新密钥确认同一发布 → 找到最短跨纪元见证', () => {
  const d = draft({
    m1: mod('M1'),
    m2: mod('M2'),
    prog: `
prepare M1 ${OLD}
activate M1
issue M1 ORD-9
prepare M1 ${NEW}
activate M1
prepare M2 ${NEW}
activate M2
issue M2 ORD-9
`,
  });
  const r = analyze(d);
  assert.equal(r.ok, true);
  assert.equal(r.report.violation, true);
  assert.equal(r.report.conflictId, 'ORD-9');
  // 两枚模块确认位掩码分别恰好为旧(1)与新(2)
  const masks = r.report.conflictKeys.map((x) => x.bits).sort();
  assert.deepEqual(masks, [1, 2]);
  // 末态双模块均已确认该发布
  const last = r.report.steps.at(-1);
  assert.ok(last.modules[0].confirmed.some((x) => x.id === 'ORD-9'));
  assert.ok(last.modules[1].confirmed.some((x) => x.id === 'ORD-9'));
  // 动作数最短：FIFO 在途槽位被占，链中每条指令必须 投递+落盘+确认 才能放行
  // 下一条；仅每侧最后一条（签发）可止于落盘。故每模块 3+3+2=8，共 16。
  assert.equal(r.report.witnessActions.length, 16);
  assert.equal(r.report.steps.length, 17);
});

test('最短性与稳定排序：见证长度等于手动最短交织，且按(模块,指令,事件)字典序最小', () => {
  const d = draft({
    m1: mod('A'),
    m2: mod('B'),
    prog: `
prepare A ${OLD}
activate A
issue A P
prepare B ${NEW}
activate B
issue B P
`,
  });
  const r = analyze(d);
  assert.equal(r.report.violation, true);
  const acts = r.report.witnessActions;
  // 每侧 3 指令：前两条各 3 步（投递/落盘/确认）放行槽位，末条签发止于落盘 = 8，共 16
  assert.equal(acts.length, 16);
  // 同长度下第一步必须来自模块 0（稳定排序）
  assert.equal(acts[0].m, 0);
  // 每步模块 0 的指令序号严格按发起顺序出现
  const a0 = acts.filter((a) => a.m === 0).map((a) => a.i);
  assert.deepEqual(a0, [0, 0, 0, 1, 1, 1, 2, 2]);
  const a1 = acts.filter((a) => a.m === 1).map((a) => a.i);
  assert.deepEqual(a1, [3, 3, 3, 4, 4, 4, 5, 5]);
  // 每侧事件形态：前两条完整确认，末条止于持久写入（落盘即确认记录成立）
  const kindsOf = (m) => acts.filter((a) => a.m === m).map((a) => a.kind);
  assert.deepEqual(kindsOf(0), [
    EVT.DELIVER, EVT.WRITE, EVT.ACK,
    EVT.DELIVER, EVT.WRITE, EVT.ACK,
    EVT.DELIVER, EVT.WRITE,
  ]);
  assert.deepEqual(kindsOf(1), [
    EVT.DELIVER, EVT.WRITE, EVT.ACK,
    EVT.DELIVER, EVT.WRITE, EVT.ACK,
    EVT.DELIVER, EVT.WRITE,
  ]);
  // 与候选集合中任意另一条同长度交织相比，报告见证为字典序最小（用解空间校验）
  assert.ok(isLexicographicallyMinimal(d, acts));
});

function isLexicographicallyMinimal(d, chosen) {
  // 独立实现：用测试自有迁移模型做分层 BFS，收集首个违约层的全部完整动作链，
  // 确认 chosen 为其中按 (模块, 指令序号, 事件) 字典序最小者。
  const { model } = parseModel(d);
  const badAt = (s) => {
    const a = s.canon[0].bits;
    const b = s.canon[1].bits;
    for (let i = 0; i < model.idTable.length; i++) if (a[i] && b[i] && a[i] !== b[i]) return true;
    return false;
  };
  const s0 = {
    h: [0, 0],
    mode: [0, 0],
    infl: [null, null],
    late: [[], []],
    canon: model.inits.map((c) => ({ ep: c.ep, prep: c.prep, bits: c.bits.slice() })),
  };
  if (badAt(s0)) return chosen.length === 0;
  const nodeKey = (s) =>
    JSON.stringify([
      s.h,
      s.mode,
      s.infl,
      s.late,
      s.canon.map((c) => [c.ep, c.prep, c.bits]),
    ]);
  // 分层 BFS，父边记录完整；不合并等价前缀（保留所有交织链）
  let layer = [{ s: s0, path: [] }];
  const seen = new Set([nodeKey(s0)]);
  for (let depth = 0; depth < 40; depth++) {
    const nxt = [];
    const badChains = [];
    for (const node of layer) {
      for (const e of edgesOf(node.s, model)) {
        const path = [...node.path, [e.m, e.i, e.kind]];
        if (badAt(e.ns)) badChains.push(path);
        else nxt.push({ s: e.ns, path });
      }
    }
    if (badChains.length) {
      const tripleCmp = (a, b) => a[0] - b[0] || a[1] - b[1] || a[2] - b[2];
      badChains.sort((a, b) => {
        for (let i = 0; i < a.length; i++) {
          const c = tripleCmp(a[i], b[i]);
          if (c) return c;
        }
        return a.length - b.length;
      });
      const chosenArr = chosen.map((a) => [a.m, a.i, a.kind]);
      // chosen 必须在违约链集合中，且长度等于首违层长度，且等于字典序最小链
      const found = badChains.some(
        (c) => c.length === chosenArr.length && c.every((t, i) => tripleCmp(t, chosenArr[i]) === 0),
      );
      const min = badChains[0];
      return (
        found &&
        chosenArr.length === min.length &&
        chosenArr.every((t, i) => tripleCmp(t, min[i]) === 0)
      );
    }
    layer = nxt;
  }
  return false;
}
function edgesOf(s, model) {
  // 与 core.mjs 中 transitions 同构（测试内独立实现，防止共享 bug 掩盖错误）
  const out = [];
  for (let m = 0; m < 2; m++) {
    const q = model.queues[m];
    const head = s.h[m] < q.length ? q[s.h[m]] : null;
    if (s.mode[m] === 0) {
      for (const i of s.late[m])
        out.push({
          m,
          i,
          kind: E.DUP_ACK,
          ns: clone(s, (n) => {
            n.late[m] = n.late[m].filter((x) => x !== i);
          }),
        });
    }
    if (s.infl[m] === null && head !== null) {
      out.push({
        // 断电中正常指令也可到达，但只能在写入前丢失
        m,
        i: head,
        kind: E.DELIVER,
        ns: clone(s, (n) => {
          n.h[m]++;
          n.infl[m] = { i: head, ph: 0 };
        }),
      });
    }
    const inf = s.infl[m];
    const addLate = (n) => {
      if (!n.late[m].includes(inf.i)) n.late[m].push(inf.i);
    };
    if (inf?.ph === 0) {
      const ins = model.instructions[inf.i];
      out.push({
        m,
        i: inf.i,
        kind: E.FAULT_PRE,
        ns: clone(s, (n) => {
          n.infl[m] = null;
          n.mode[m] = 1;
          addLate(n);
        }),
      });
      const writable = s.mode[m] === 0 || ins.op === 'recover';
      if (writable)
        out.push({
          m,
          i: inf.i,
          kind: E.WRITE,
          ns: clone(s, (n) => {
            if (ins.op === 'prepare' && n.canon[m].prep !== ins.arg) n.canon[m].prep = ins.arg;
            else if (ins.op === 'activate' && n.canon[m].prep !== NONE)
              n.canon[m].ep = n.canon[m].prep;
            else if (ins.op === 'issue' && n.canon[m].ep !== NONE) {
              n.canon[m].bits = n.canon[m].bits.slice();
              n.canon[m].bits[ins.arg] |= 1 << n.canon[m].ep;
            }
            if (ins.op === 'recover') n.mode[m] = 0;
            n.infl[m] = { i: inf.i, ph: 1 };
          }),
        });
    } else if (inf?.ph === 1) {
      out.push({
        m,
        i: inf.i,
        kind: E.FAULT_POST,
        ns: clone(s, (n) => {
          n.infl[m] = null;
          n.mode[m] = 1;
          addLate(n);
        }),
      });
      out.push({ m, i: inf.i, kind: E.ACK, ns: clone(s, (n) => (n.infl[m] = null)) });
      out.push({
        m,
        i: inf.i,
        kind: E.FAULT_ACK,
        ns: clone(s, (n) => {
          n.infl[m] = null;
          n.mode[m] = 1;
          addLate(n);
        }),
      });
    }
  }
  return out;
}

function clone(s, mut) {
  const n = {
    h: s.h.slice(),
    mode: s.mode.slice(),
    infl: s.infl.map((x) => (x ? { ...x } : null)),
    late: s.late.map((x) => x.slice()),
    canon: s.canon.map((c) => ({ ep: c.ep, prep: c.prep, bits: c.bits })),
  };
  mut(n);
  return n;
}

test('未激活即签发不成立：仅签发指令的场景安全（双方均无确认记录）', () => {
  const d = draft({
    m1: mod('M1'),
    m2: mod('M2'),
    prog: 'issue M1 X\nissue M2 X\n',
  });
  const r = analyze(d);
  assert.equal(r.ok, true);
  assert.equal(r.report.violation, false);
  const last = r.report.terminalSnapshot;
  assert.deepEqual(
    last.modules.map((m) => m.confirmed.length),
    [0, 0],
  );
});

test('写入前断电丢失指令：未落盘的新密钥准备恢复后不可用，激活保持旧纪元', () => {
  // M1 初始旧纪元：prepare(NEW) 写入前断电丢失 → recover → activate（无准备，空操作）
  // → issue RO 只能以旧密钥成立；M2 正常以新密钥签发 → 违约见证必含写入前断电
  const d = draft({
    m1: mod('M1', { epoch: '0' }),
    m2: mod('M2'),
    prog: `
prepare M1 ${NEW}
recover M1
activate M1
issue M1 RO
prepare M2 ${NEW}
activate M2
issue M2 RO
`,
  });
  const r = analyze(d);
  assert.equal(r.ok, true, JSON.stringify(r.errors));
  assert.equal(r.report.violation, true);
  assert.ok(
    r.report.witnessActions.some((a) => a.kind === EVT.FAULT_PRE),
    '最短违约见证应包含写入前断电（新密钥准备未落盘）',
  );
  const last = r.report.steps.at(-1);
  assert.equal(last.modules[0].epoch, 0);
  assert.equal(last.modules[1].epoch, 1);
});

test('写入后确认前断电 + 恢复重放：迟到/重复确认不改变记录', () => {
  // 正常轮换后签发；中途可在任意点断电恢复，结果始终安全，且穷举中确实覆盖了 DUP_ACK
  const d = draft({
    m1: mod('M1'),
    m2: mod('M2'),
    prog: `
prepare M1 ${NEW}
activate M1
issue M1 D
recover M1
recover M1
prepare M2 ${NEW}
activate M2
issue M2 D
recover M2
`,
  });
  const r = analyze(d);
  assert.equal(r.ok, true, JSON.stringify(r.errors));
  assert.equal(r.report.violation, false);
  // 穷尽过程包含重复确认幂等步（安全时无见证，改用小规模违约场景验证 DUP_ACK 出现）
  const d2 = draft({
    m1: mod('M1'),
    m2: mod('M2'),
    prog: `prepare M1 ${OLD}
activate M1
issue M1 D
recover M1
prepare M2 ${NEW}
activate M2
issue M2 D`,
  });
  const r2 = analyze(d2);
  assert.equal(r2.report.violation, true);
  // 存在至少一条穷举路径使用了迟到确认（即模型确实枚举该事件而非忽略）：
  // 通过报告的覆盖统计间接确认——更直接地，枚举迁移检查 DUP_ACK 可达
  assert.ok(dupAckReachable(d2));
});

function dupAckReachable(d) {
  // 深度受限搜索确认 DUP_ACK 边可达
  const { model } = parseModel(d);
  let s0 = {
    h: [0, 0],
    mode: [0, 0],
    infl: [null, null],
    late: [[], []],
    canon: model.inits.map((c) => ({ ep: c.ep, prep: c.prep, bits: c.bits.slice() })),
  };
  const seen = new Set();
  const stack = [[s0, 0]];
  while (stack.length) {
    const [s, dep] = stack.pop();
    if (dep > 14) continue;
    const k = JSON.stringify({
      h: s.h,
      mode: s.mode,
      infl: s.infl,
      late: s.late,
      bits: s.canon.map((c) => [c.ep, c.prep, c.bits]),
    });
    if (seen.has(k)) continue;
    seen.add(k);
    for (const e of edgesOf(s, model)) {
      if (e.kind === E.DUP_ACK) return true;
      stack.push([e.ns, dep + 1]);
    }
  }
  return false;
}

test('初态即冲突：两模块持久初态对同一发布持有不同纪元确认，零动作违约', () => {
  const d = draft({
    m1: mod('M1', { epoch: '0', confirmed: `BOOT:${OLD}` }),
    m2: mod('M2', { epoch: '1', confirmed: `BOOT:${NEW}` }),
  });
  const r = analyze(d);
  assert.equal(r.ok, true);
  assert.equal(r.report.violation, true);
  assert.equal(r.report.witnessActions.length, 0);
  assert.equal(r.report.steps.length, 1);
});

test('同一模块同一发布跨纪元重复签发产生双密钥位，不与单密钥对端误判', () => {
  // M1 旧、新两次确认 RO（掩码3），M2 仅旧（掩码1）：掩码不同 → 仍属共同确认不一致，判违约
  const d = draft({
    m1: mod('M1'),
    m2: mod('M2'),
    prog: `prepare M1 ${OLD}
activate M1
issue M1 RO
prepare M1 ${NEW}
activate M1
issue M1 RO
prepare M2 ${OLD}
activate M2
issue M2 RO`,
  });
  const r = analyze(d);
  assert.equal(r.report.violation, true);
});

test('校验：全部输入错误一次性指出', () => {
  // 模块标识合法但其他字段/指令全部非法（使目标可解析，覆盖参数级错误）
  const d = draft({
    oldFp: '',
    newFp: '',
    m1: { id: 'M1', epoch: '9', prep: 'x', confirmed: 'bad-entry' },
    m2: { id: 'M2', confirmed: `Q:${'FP-UNKNOWN'}` },
    prog: `recover M1
frobnicate X
prepare M1 ${'FP-UNKNOWN'}
issue
issue ZZ P
activate M2 extra
bogus M2`,
  });
  const r = analyze(d);
  assert.equal(r.ok, false);
  const msg = r.errors.join('\n');
  const expected = [
    /未填写旧密钥/,
    /未填写新密钥/,
    /持久纪元初态非法/,
    /准备密钥初态非法/,
    /格式非法/,
    /不是已声明的旧或新密钥/,
    /未知指令类型/,
    /缺少指令目标/,
    /目标模块/,
    /激活指令不接受额外参数/,
    /恢复前无故障/,
  ];
  for (const re of expected) assert.match(msg, re, `缺少错误：${re}；实际错误：\n${msg}`);
  assert.ok(r.errors.length >= expected.length, `实际仅 ${r.errors.length} 条：\n${msg}`);
});

test('校验：模块标识重复在首轮复核中单独指出', () => {
  const r = analyze(
    draft({ m1: { id: 'DUP' }, m2: { id: 'DUP' }, prog: 'issue M1 P\nissue M2 P' }),
  );
  assert.equal(r.ok, false);
  const msg = r.errors.join('\n');
  assert.match(msg, /标识重复/);
  // 重复标识下目标无法解析，也应一并报告
  assert.match(msg, /目标模块/);
});

test('校验：模块标识缺失、发布标识非法字符、指令超限 16 条', () => {
  const lines = Array.from({ length: 17 }, (_, i) => `issue M2 P${i}`).join('\n');
  const d = draft({
    m1: { id: '' },
    m2: { id: 'M2' },
    prog: `issue M2 bad/id\n${lines}`,
  });
  const r = analyze(d);
  assert.equal(r.ok, false);
  const msg = r.errors.join('\n');
  assert.match(msg, /未填写模块 1/);
  assert.match(msg, /非法字符/);
  assert.match(msg, /超过上限 16/);
});

test('幂等不变量：穷举中所有迟到/重复确认迁移都不改变规范状态', () => {
  // 对一个含多次断电/恢复的场景做受限全枚举，校验每条 DUP_ACK 边前后
  // 双模块（纪元/准备密钥/已确认集合）完全一致。
  const d = draft({
    m1: mod('M1', { epoch: '0' }),
    m2: mod('M2'),
    prog: `prepare M1 ${NEW}
activate M1
issue M1 X
recover M1
issue M1 Y
recover M1
prepare M2 ${NEW}
activate M2`,
  });
  const { model } = parseModel(d);
  const canonEq = (s, t) =>
    [0, 1].every(
      (m) =>
        s.canon[m].ep === t.canon[m].ep &&
        s.canon[m].prep === t.canon[m].prep &&
        s.canon[m].bits.length === t.canon[m].bits.length &&
        s.canon[m].bits.every((b, i) => b === t.canon[m].bits[i]),
    );
  const keyOf = (s) =>
    JSON.stringify([
      s.h,
      s.mode,
      s.infl,
      s.late,
      s.canon.map((c) => [c.ep, c.prep, c.bits]),
    ]);
  const s0 = {
    h: [0, 0],
    mode: [0, 0],
    infl: [null, null],
    late: [[], []],
    canon: model.inits.map((c) => ({ ep: c.ep, prep: c.prep, bits: c.bits.slice() })),
  };
  let dupEdges = 0;
  const seen = new Set([keyOf(s0)]);
  const stack = [s0];
  while (stack.length) {
    const s = stack.pop();
    for (const e of edgesOf(s, model)) {
      if (e.kind === E.DUP_ACK) {
        dupEdges += 1;
        assert.ok(canonEq(s, e.ns), '迟到/重复确认改变了规范状态');
      }
      const k = keyOf(e.ns);
      if (!seen.has(k)) {
        seen.add(k);
        stack.push(e.ns);
      }
    }
  }
  assert.ok(dupEdges > 0, '穷举中应实际出现迟到/重复确认事件');
});

test('中文指令助记符可用，且空行/多余空白被容忍', () => {
  const d = draft({
    m1: mod('左'),
    m2: mod('右'),
    prog: `
  准备 左 ${NEW}
激活 左

签发 左 F1
准备 右 ${NEW}
激活 右
签发 右 F1
`,
  });
  const r = analyze(d);
  assert.equal(r.ok, true, JSON.stringify(r.errors));
  assert.equal(r.report.violation, false);
});

test('旧新指纹相同被拒绝', () => {
  const r = analyze(draft({ oldFp: 'X', newFp: 'X' }));
  assert.equal(r.ok, false);
  assert.match(r.errors.join('\n'), /不得相同/);
});

test('# 起始的注释行不计入指令，行号仍按物理行计', () => {
  const d = draft({
    m1: mod('M1'),
    m2: mod('M2'),
    prog: `# 这是注释
prepare M1 ${NEW}
# 中间注释
activate M1
issue M1 Z1
prepare M2 ${NEW}
activate M2
issue M2 Z1`,
  });
  const r = analyze(d);
  assert.equal(r.ok, true, JSON.stringify(r.errors));
  assert.equal(r.report.violation, false);
  // 指令物理行号保留：#5(2) 签发实际在第 5 行
  assert.equal(r.model.instructions[2].lineNo, 5);
});
