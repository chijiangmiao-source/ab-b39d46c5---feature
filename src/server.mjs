// 零依赖静态服务：提供复核台页面、Worker、前端脚本与核心模块，以及 /healthz。
import http from 'node:http';
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import path from 'node:path';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const WEB = path.join(ROOT, 'web');
const SRC = path.join(ROOT, 'src');

const HOST = process.env.HOST || '0.0.0.0';
const PORT = Number(process.env.PORT || 8080);

const MIME = {
  '.html': 'text/html; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.mjs': 'text/javascript; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.svg': 'image/svg+xml',
  '.ico': 'image/x-icon',
};

// 仅暴露两份只读目录
const MOUNTS = [
  { prefix: '/', dir: WEB },
  { prefix: '/src/', dir: SRC },
];

async function serveStatic(urlPath) {
  let rel = decodeURIComponent(urlPath.split('?')[0]);
  if (rel === '/') rel = '/index.html';
  let baseDir = null;
  let basePrefix = null;
  for (const m of MOUNTS) {
    if ((rel === m.prefix || rel.startsWith(m.prefix)) &&
        (basePrefix === null || m.prefix.length > basePrefix.length)) {
      baseDir = m.dir;
      basePrefix = m.prefix;
    }
  }
  if (!baseDir) return null;
  // 去除挂载前缀（'/' 挂载保留完整路径，'/src/' 挂载去掉 '/src'）
  const relInMount = basePrefix === '/' ? rel : '/' + rel.slice(basePrefix.length);
  const filePath = path.normalize(path.join(baseDir, relInMount));
  if (!filePath.startsWith(baseDir)) return null; // 防目录穿越
  try {
    const data = await readFile(filePath);
    const ext = path.extname(filePath);
    return { status: 200, type: MIME[ext] || 'application/octet-stream', data };
  } catch {
    return { status: 404, type: 'text/plain; charset=utf-8', data: Buffer.from('not found') };
  }
}

export function createServer() {
  return http.createServer(async (req, res) => {
    try {
      if (req.method !== 'GET' && req.method !== 'HEAD') {
        res.writeHead(405, { 'content-type': 'text/plain; charset=utf-8' });
        res.end('method not allowed');
        return;
      }
      const url = req.url || '/';
      if (url === '/healthz' || url.startsWith('/healthz?')) {
        const body = JSON.stringify({ status: 'ok', service: 'key-rotation-review', time: new Date().toISOString() });
        res.writeHead(200, { 'content-type': 'application/json; charset=utf-8' });
        res.end(req.method === 'HEAD' ? undefined : body);
        return;
      }
      const file = await serveStatic(url);
      if (!file) {
        res.writeHead(403, { 'content-type': 'text/plain; charset=utf-8' });
        res.end('forbidden');
        return;
      }
      res.writeHead(file.status, { 'content-type': file.type });
      res.end(req.method === 'HEAD' ? undefined : file.data);
    } catch (err) {
      res.writeHead(500, { 'content-type': 'text/plain; charset=utf-8' });
      res.end(`server error: ${err.message}`);
    }
  });
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const server = createServer();
  server.listen(PORT, HOST, () => {
    console.log(`[web] 航电密钥轮换复核台监听 http://${HOST}:${PORT}（健康检查 /healthz）`);
  });
}
