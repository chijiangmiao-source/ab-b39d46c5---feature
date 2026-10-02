// verify 服务：围绕本轮换场景依次运行
//   1) 核心状态测试（node --test）
//   2) 静态构建检查（所有被引用的前端/Worker/核心文件存在且语法可解析）
//   3) 页面与健康地址 HTTP 冒烟
// 全部通过退出码 0，任一步失败退出码 1。
import { spawn } from 'node:child_process';
import { readFile, access } from 'node:fs/promises';
import net from 'node:net';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import { createServer } from './server.mjs';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const PORT = Number(process.env.VERIFY_PORT || 8099);
const HOST = '127.0.0.1';

const log = (phase, msg) => console.log(`[verify:${phase}] ${msg}`);

function run(cmd, args) {
  return new Promise((resolve) => {
    const child = spawn(cmd, args, { cwd: ROOT, stdio: 'inherit' });
    child.on('close', (code) => resolve(code));
    child.on('error', (err) => {
      console.error(err);
      resolve(1);
    });
  });
}

async function coreTests() {
  log('test', '运行核心状态测试 node --test test/');
  const code = await run(process.execPath, ['--test', 'test/']);
  if (code !== 0) {
    log('test', `核心状态测试失败（退出码 ${code}）`);
    return false;
  }
  log('test', '核心状态测试通过');
  return true;
}

// 解析 HTML 中的 <script>/<link> 与 JS 中的相对 import，递归确认引用文件都存在、可被 Node 解析
async function staticBuildCheck() {
  log('build', '静态构建检查：引用完整性与语法解析');
  const checked = new Set();
  const queue = [
    { url: '/index.html', kind: 'html' },
    { url: '/app.js', kind: 'js' },
    { url: '/worker.mjs', kind: 'js' },
    { url: '/src/core.mjs', kind: 'js' },
    { url: '/src/server.mjs', kind: 'js' },
  ];
  const resolveToFile = (url) => {
    if (url.startsWith('/src/')) return path.join(ROOT, 'src', url.slice('/src/'.length));
    return path.join(ROOT, 'web', url.slice(1));
  };
  for (const item of queue) {
    if (checked.has(item.url)) continue;
    checked.add(item.url);
    const file = resolveToFile(item.url);
    try {
      await access(file);
    } catch {
      log('build', `缺失文件：${item.url}`);
      return false;
    }
    const src = await readFile(file, 'utf8');
    if (item.kind === 'html') {
      for (const m of src.matchAll(/(?:src|href)="([^"]+)"/g)) {
        const ref = m[1];
        if (ref.startsWith('/') && !ref.startsWith('//')) {
          const kind = ref.endsWith('.html') ? 'html' : ref.endsWith('.js') || ref.endsWith('.mjs') ? 'js' : 'asset';
          queue.push({ url: ref, kind });
        }
      }
    } else if (item.kind === 'js') {
      // 语法检查：node --check 仅解析不执行
      const code = await run(process.execPath, ['--check', file]);
      if (code !== 0) {
        log('build', `语法解析失败 ${item.url}`);
        return false;
      }
      // 相对 import 必须指向存在的文件
      for (const m of src.matchAll(/from\s+['"](\.[^'"]+)['"]/g)) {
        const target = path.normalize(path.join(path.dirname(file), m[1]));
        try {
          await access(target);
        } catch {
          log('build', `${item.url} 引用了不存在的模块：${m[1]}`);
          return false;
        }
      }
    }
  }
  log('build', `静态构建检查通过（${checked.size} 个入口文件）`);
  return true;
}

async function httpSmoke() {
  log('smoke', `启动临时服务 http://${HOST}:${PORT}`);
  const server = createServer();
  await new Promise((resolve) => server.listen(PORT, HOST, resolve));
  const expect = async (url, { status, contains, contentType }) => {
    const res = await fetch(`http://${HOST}:${PORT}${url}`);
    const text = await res.text();
    if (res.status !== status) {
      log('smoke', `${url} 状态码期望 ${status}，实际 ${res.status}`);
      return false;
    }
    if (contentType && !res.headers.get('content-type').includes(contentType)) {
      log('smoke', `${url} 内容类型异常：${res.headers.get('content-type')}`);
      return false;
    }
    if (contains && !text.includes(contains)) {
      log('smoke', `${url} 响应未包含期望内容：${contains}`);
      return false;
    }
    return true;
  };
  // 原始请求行冒烟：防目录穿越
  const rawExpect = (requestLine, wantStatus) =>
    new Promise((resolve) => {
      const sock = net.connect(PORT, HOST, () => {
        sock.write(`${requestLine}\r\nHost: ${HOST}:${PORT}\r\nConnection: close\r\n\r\n`);
      });
      let data = '';
      sock.on('data', (c) => (data += c));
      sock.on('close', () => {
        const status = Number((data.split('\r\n')[0] || '').split(' ')[1] || 0);
        if (status !== wantStatus) {
          log('smoke', `${requestLine} 期望 ${wantStatus}，实际 ${status}`);
          resolve(false);
        } else resolve(true);
      });
      sock.on('error', () => resolve(false));
    });

  let ok = true;
  ok = ok && (await expect('/healthz', { status: 200, contains: '"status":"ok"', contentType: 'application/json' }));
  ok = ok && (await expect('/', { status: 200, contains: '航电密钥轮换复核台', contentType: 'text/html' }));
  ok = ok && (await expect('/index.html', { status: 200, contains: '/app.js' }));
  ok = ok && (await expect('/app.js', { status: 200, contains: 'worker.mjs' }));
  ok = ok && (await expect('/worker.mjs', { status: 200, contains: 'analyze' }));
  ok = ok && (await expect('/src/core.mjs', { status: 200, contains: 'explore' }));
  ok = ok && (await expect('/styles.css', { status: 200, contentType: 'text/css' }));
  ok = ok && (await rawExpect('GET /../package.json HTTP/1.1', 403));
  ok = ok && (await rawExpect('GET /src/../../etc/passwd HTTP/1.1', 403));
  await new Promise((resolve) => server.close(resolve));
  if (ok) log('smoke', 'HTTP 冒烟通过（页面、健康地址、静态模块、越权路径）');
  else log('smoke', 'HTTP 冒烟失败');
  return ok;
}

async function workerSmoke() {
  log('worker', '在 worker_threads 中加载 web/worker.mjs（与浏览器模块 Worker 同入口）');
  const { Worker } = await import('node:worker_threads');
  const run = (draft) =>
    new Promise((resolve, reject) => {
      const w = new Worker(path.join(ROOT, 'web', 'worker.mjs'), { type: 'module' });
      let gotProgress = false;
      const timer = setTimeout(() => {
        w.terminate();
        reject(new Error('Worker 超时未返回'));
      }, 15000);
      w.on('message', (m) => {
        if (m.type === 'progress') {
          gotProgress = true;
          return;
        }
        clearTimeout(timer);
        w.terminate();
        resolve({ ...m.result, gotProgress });
      });
      w.on('error', (err) => {
        clearTimeout(timer);
        reject(err);
      });
      w.postMessage({ type: 'run', draft });
    });
  const mk = (id) => ({ id, epoch: '-1', prep: '-1', confirmed: '' });
  const unsafe = await run({
    oldFp: 'OLD-FP',
    newFp: 'NEW-FP',
    modules: [mk('M1'), mk('M2')],
    instructionsText:
      'prepare M1 OLD-FP\nactivate M1\nissue M1 R\nprepare M2 NEW-FP\nactivate M2\nissue M2 R',
  });
  if (!unsafe.ok || !unsafe.report.violation || unsafe.report.conflictId !== 'R') {
    log('worker', `违约场景结果异常：${JSON.stringify(unsafe).slice(0, 300)}`);
    return false;
  }
  if (!unsafe.gotProgress) {
    log('worker', '未收到任何进度消息');
    return false;
  }
  const safe = await run({
    oldFp: 'OLD-FP',
    newFp: 'NEW-FP',
    modules: [mk('M1'), mk('M2')],
    instructionsText: 'prepare M1 NEW-FP\nactivate M1\nissue M1 S\nprepare M2 NEW-FP\nactivate M2\nissue M2 S',
  });
  if (!safe.ok || safe.report.violation) {
    log('worker', `安全场景结果异常：${JSON.stringify(safe).slice(0, 300)}`);
    return false;
  }
  log('worker', 'Worker 运行时冒烟通过（违约检出 / 安全结论 / 进度回传）');
  return true;
}

async function main() {
  const t1 = await coreTests();
  const t2 = t1 ? await staticBuildCheck() : false;
  const t3 = t1 && t2 ? await workerSmoke() : false;
  const t4 = t1 && t2 && t3 ? await httpSmoke() : false;
  console.log('----------------------------------------');
  console.log(
    `[verify] 核心状态测试: ${t1 ? 'PASS' : 'FAIL'} | 静态构建检查: ${t2 ? 'PASS' : 'FAIL'} | Worker 冒烟: ${t3 ? 'PASS' : 'FAIL'} | HTTP 冒烟: ${t4 ? 'PASS' : 'FAIL'}`,
  );
  process.exit(t1 && t2 && t3 && t4 ? 0 : 1);
}

main().catch((err) => {
  console.error('[verify] 异常终止：', err);
  process.exit(1);
});
