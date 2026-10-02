// Web Worker：在后台线程执行穷尽穷举，定期回传进度，支持取消。
// 浏览器环境使用 self.onmessage/postMessage；Node worker_threads（verify 冒烟）
// 通过 parentPort 适配同一收发接口。
import { analyze } from '../src/core.mjs';

function handleMessage(e) {
  const { type, draft } = e.data || {};
  if (type !== 'run') return;
  const result = analyze(draft, ({ visited, depth, merges }) => {
    postMessage({ type: 'progress', visited, depth, merges });
    // 同步穷举很快（最坏约 1~2 万状态、百毫秒内），进度消息已足以反馈。
    return false;
  });
  postMessage({ type: 'done', result });
}

if (typeof self === 'undefined' || typeof postMessage === 'undefined') {
  const { parentPort } = await import('node:worker_threads');
  parentPort.on('message', (data) => handleMessage({ data }));
  globalThis.postMessage = (msg) => parentPort.postMessage(msg);
} else {
  self.onmessage = handleMessage;
}
