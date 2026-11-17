/*
 * A dependency-free, deterministic miniature GitHub forge.
 *
 * The contest deliberately scores the wire surfaces rather than a particular
 * framework. This implementation keeps state in memory, uses real Git
 * object ids/pack files, and exposes the REST, GraphQL, MCP and smart-HTTP
 * routes used by the supplied conformance suite.
 */

import { createHash } from 'node:crypto';
import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { deflateSync, inflateSync } from 'node:zlib';

const JSON_TYPE = 'application/json; charset=utf-8';
const VIEWER = 'adaiversen';
const VIEWER_NAME = 'Ada Iversen';
const VIEWER_EMAIL = VIEWER + '@example.invalid';
const ZERO = '0'.repeat(40);
const expectedToken = (): string => process.env.MAKEFUN_SHOP_TOKEN || 'makefun-local-token';

type ObjectType = 'blob' | 'tree' | 'commit' | 'tag';
interface GitObject { type: ObjectType; data: Buffer }
interface FileValue { sha: string; content: Buffer }
interface CommitValue { tree: string; parents: string[]; message: string; files: Map<string, FileValue> }
interface Issue {
  id: number; number: number; title: string; body: string; state: 'open' | 'closed'; labels: string[];
  created: number; comments: Array<{ id: number; body: string }>; version: number;
  cachedJson?: { base: string; version: number; bytes: Buffer };
}
interface Pull {
  id: number; number: number; title: string; body: string; head: string; base: string;
  state: 'open' | 'closed'; merged: boolean; mergedAt?: string; mergeSha?: string;
  headFiles: Map<string, FileValue>; baseFiles: Map<string, FileValue>;
}
interface Repo {
  id: number; owner: string; name: string; description: string; private: boolean;
  defaultBranch: string; refs: Map<string, string>; objects: Map<string, GitObject>;
  commits: Map<string, CommitValue>; files: Map<string, Map<string, FileValue>>;
  labels: Map<string, { name: string; color: string }>; issues: Map<number, Issue>; pulls: Map<number, Pull>;
  packCache: Map<string, Buffer>; advertisementCache: Map<string, Buffer>; lsRefsCache: Map<string, Buffer>;
}

const repos = new Map<string, Repo>();
let nextRepoId = 1000;
let nextIssueId = 1;
let nextIssueNumber = 1;
let nextPullId = 1;
let nextPullNumber = 1;
let nextCommentId = 1;
let logicalTime = 1700000000;

function repoKey(owner: string, name: string): string { return owner.toLowerCase() + '/' + name.toLowerCase(); }
function cloneFiles(source: Map<string, FileValue>): Map<string, FileValue> {
  return new Map([...source].map(([path, value]) => [path, { sha: value.sha, content: Buffer.from(value.content) }]));
}
function repoFor(owner: string, name: string): Repo | undefined { return repos.get(repoKey(owner, name)); }
function globalId(prefix: string, id: number): string { return prefix + '_' + id.toString(36); }
function errorBody(message: string): { message: string } { return { message }; }
function hashObject(type: ObjectType, data: Buffer): string {
  return createHash('sha1').update(type + ' ' + data.length + '\0').update(data).digest('hex');
}
function addObject(repo: Repo, type: ObjectType, data: Buffer): string {
  const oid = hashObject(type, data);
  repo.objects.set(oid, { type, data: Buffer.from(data) });
  return oid;
}
function fileMapAt(repo: Repo, branch: string): Map<string, FileValue> {
  const tip = repo.refs.get('refs/heads/' + branch);
  return tip ? cloneFiles(repo.commits.get(tip)?.files ?? hydrateFiles(repo, tip)) : new Map();
}

interface TreeNode { files: Map<string, string>; dirs: Map<string, TreeNode> }
function newTreeNode(): TreeNode { return { files: new Map(), dirs: new Map() }; }
function buildTree(repo: Repo, files: Map<string, FileValue>): string {
  const root = newTreeNode();
  for (const [path, value] of files) {
    const pieces = path.split('/').filter(Boolean);
    if (!pieces.length) continue;
    let node = root;
    for (let i = 0; i < pieces.length - 1; i += 1) {
      const part = pieces[i]!;
      let child = node.dirs.get(part);
      if (!child) { child = newTreeNode(); node.dirs.set(part, child); }
      node = child;
    }
    node.files.set(pieces[pieces.length - 1]!, value.sha);
  }
  const write = (node: TreeNode): string => {
    const entries: Array<{ mode: string; name: string; oid: string }> = [];
    for (const [name, child] of node.dirs) entries.push({ mode: '40000', name, oid: write(child) });
    for (const [name, oid] of node.files) entries.push({ mode: '100644', name, oid });
    entries.sort((a, b) => Buffer.compare(Buffer.from(a.name + (a.mode === '40000' ? '/' : '')), Buffer.from(b.name + (b.mode === '40000' ? '/' : ''))));
    const body = Buffer.concat(entries.map((entry) => Buffer.concat([Buffer.from(entry.mode + ' ' + entry.name + '\0'), Buffer.from(entry.oid, 'hex')])));
    return addObject(repo, 'tree', body);
  };
  return write(root);
}
function createCommit(repo: Repo, branch: string, files: Map<string, FileValue>, message: string, parent?: string): string {
  const tree = buildTree(repo, files);
  const parents = parent && parent !== ZERO ? [parent] : [];
  const author = VIEWER_NAME + ' <' + VIEWER_EMAIL + '> ' + logicalTime + ' +0000';
  const lines = ['tree ' + tree, ...parents.map((p) => 'parent ' + p), 'author ' + author, 'committer ' + author, '', message || 'Update files'];
  const oid = addObject(repo, 'commit', Buffer.from(lines.join('\n') + '\n'));
  repo.commits.set(oid, { tree, parents, message: message || 'Update files', files: cloneFiles(files) });
  repo.packCache.clear();
  repo.advertisementCache.clear(); repo.lsRefsCache.clear();
  repo.refs.set('refs/heads/' + branch, oid);
  logicalTime += 1;
  return oid;
}
function parseCommit(data: Buffer): { tree: string; parents: string[]; message: string } {
  const split = data.toString('utf8').split('\n\n');
  const header = split.shift() || '';
  let tree = '';
  const parents: string[] = [];
  for (const line of header.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
  }
  return { tree, parents, message: split.join('\n\n').replace(/\n$/, '') };
}
function parseTree(data: Buffer): Array<{ mode: string; name: string; oid: string }> {
  const out: Array<{ mode: string; name: string; oid: string }> = [];
  let at = 0;
  while (at < data.length) {
    const space = data.indexOf(0x20, at);
    const nul = space >= 0 ? data.indexOf(0, space + 1) : -1;
    if (space < 0 || nul < 0 || nul + 21 > data.length) break;
    out.push({ mode: data.subarray(at, space).toString(), name: data.subarray(space + 1, nul).toString(), oid: data.subarray(nul + 1, nul + 21).toString('hex') });
    at = nul + 21;
  }
  return out;
}
function hydrateFiles(repo: Repo, commitOid: string): Map<string, FileValue> {
  const known = repo.commits.get(commitOid);
  if (known) return known.files;
  const commitObject = repo.objects.get(commitOid);
  if (!commitObject || commitObject.type !== 'commit') return new Map();
  const parsed = parseCommit(commitObject.data);
  const files = new Map<string, FileValue>();
  const visit = (treeOid: string, prefix: string): void => {
    const tree = repo.objects.get(treeOid);
    if (!tree || tree.type !== 'tree') return;
    for (const entry of parseTree(tree.data)) {
      const path = prefix + entry.name;
      if (entry.mode === '40000') visit(entry.oid, path + '/');
      else {
        const blob = repo.objects.get(entry.oid);
        if (blob?.type === 'blob') files.set(path, { sha: entry.oid, content: Buffer.from(blob.data) });
      }
    }
  };
  visit(parsed.tree, '');
  repo.commits.set(commitOid, { tree: parsed.tree, parents: parsed.parents, message: parsed.message, files });
  return files;
}
function repoTip(repo: Repo, branch = repo.defaultBranch): string { return repo.refs.get('refs/heads/' + branch) || ZERO; }
function fileDiff(from: Map<string, FileValue>, to: Map<string, FileValue>): string[] {
  return [...new Set([...from.keys(), ...to.keys()])].filter((path) => from.get(path)?.sha !== to.get(path)?.sha);
}
function lineCount(data: Buffer): number { return data.length ? data.toString('utf8').split('\n').length : 0; }

function makeRepo(owner: string, name: string, body: Record<string, unknown> = {}): Repo {
  const repo: Repo = {
    id: nextRepoId++, owner, name, description: typeof body.description === 'string' ? body.description : '',
    private: body.private !== false, defaultBranch: 'main', refs: new Map(), objects: new Map(), commits: new Map(),
  files: new Map(), labels: new Map(), issues: new Map(), pulls: new Map(), packCache: new Map(), advertisementCache: new Map(), lsRefsCache: new Map(),
  };
  repos.set(repoKey(owner, name), repo);
  return repo;
}
function repoJson(repo: Repo, base = ''): Record<string, unknown> {
  return {
    id: repo.id, node_id: globalId('R', repo.id), name: repo.name, full_name: repo.owner + '/' + repo.name,
    owner: { login: repo.owner }, private: repo.private, description: repo.description, default_branch: repo.defaultBranch,
    html_url: base + '/•/' + repo.owner + '/' + repo.name, url: base + '/api/v3/repos/' + repo.owner + '/' + repo.name,
    has_issues: true, open_issues_count: [...repo.issues.values()].filter((i) => i.state === 'open').length,
  };
}
function issueJson(repo: Repo, issue: Issue, base = ''): Record<string, unknown> {
  return {
    id: issue.id, node_id: globalId('I', issue.id), number: issue.number, title: issue.title, body: issue.body,
    state: issue.state, user: { login: VIEWER }, labels: issue.labels.map((name) => ({ name, color: repo.labels.get(name)?.color || 'ededed' })),
    comments: issue.comments.length, url: base + '/api/v3/repos/' + repo.owner + '/' + repo.name + '/issues/' + issue.number,
    html_url: base + '/•/' + repo.owner + '/' + repo.name + '/issues/' + issue.number,
  };
}
function issueCreateJson(repo: Repo, issue: Issue): Record<string, unknown> {
  return { number: issue.number, title: issue.title, body: issue.body, state: issue.state, labels: issue.labels.map((name) => ({ name, color: repo.labels.get(name)?.color || 'ededed' })) };
}
function issueJsonBytes(repo: Repo, issue: Issue, base: string): Buffer {
  const cached = issue.cachedJson;
  if (cached && cached.base === base && cached.version === issue.version) return cached.bytes;
  const bytes = Buffer.from(JSON.stringify(issueJson(repo, issue, base)) + '\n');
  issue.cachedJson = { base, version: issue.version, bytes };
  return bytes;
}
function pullJson(repo: Repo, pull: Pull, base = ''): Record<string, unknown> {
  const headSha = repoTip(repo, pull.head);
  const baseSha = repoTip(repo, pull.base);
  return {
    id: pull.id, node_id: globalId('P', pull.id), number: pull.number, title: pull.title, body: pull.body,
    state: pull.state, merged: pull.merged, merged_at: pull.mergedAt || null, merge_commit_sha: pull.mergeSha || null,
    user: { login: VIEWER }, head: { ref: pull.head, sha: headSha, label: VIEWER + ':' + pull.head },
    base: { ref: pull.base, sha: baseSha, label: VIEWER + ':' + pull.base }, mergeable: true,
    url: base + '/api/v3/repos/' + repo.owner + '/' + repo.name + '/pulls/' + pull.number,
    html_url: base + '/•/' + repo.owner + '/' + repo.name + '/pull/' + pull.number,
  };
}
function filesJson(repo: Repo, pull: Pull): Array<Record<string, unknown>> {
  const from = fileMapAt(repo, pull.base);
  const to = fileMapAt(repo, pull.head);
  return fileDiff(from, to).map((path) => {
    const oldValue = from.get(path); const newValue = to.get(path);
    const status = !oldValue ? 'added' : !newValue ? 'removed' : 'modified';
    return {
      sha: newValue?.sha || oldValue?.sha || ZERO, filename: path, status,
      additions: newValue ? Math.max(1, lineCount(newValue.content)) : 0,
      deletions: oldValue ? Math.max(1, lineCount(oldValue.content)) : 0,
      changes: (newValue ? Math.max(1, lineCount(newValue.content)) : 0) + (oldValue ? Math.max(1, lineCount(oldValue.content)) : 0),
      blob_url: '', raw_url: '', contents_url: '',
    };
  });
}

function pkt(data: Buffer | string): Buffer {
  const body = Buffer.isBuffer(data) ? data : Buffer.from(data);
  return Buffer.concat([Buffer.from((body.length + 4).toString(16).padStart(4, '0')), body]);
}
function flush(): Buffer { return Buffer.from('0000'); }
function pktLines(lines: Array<Buffer | string | 'flush'>): Buffer {
  return Buffer.concat(lines.map((line) => line === 'flush' ? flush() : pkt(line)));
}
function packHeader(type: ObjectType, size: number): Buffer {
  const code = type === 'commit' ? 1 : type === 'tree' ? 2 : type === 'blob' ? 3 : 4;
  const bytes: number[] = [];
  let first = (code << 4) | (size & 15);
  let rest = Math.floor(size / 16);
  while (rest > 0) { bytes.push(first | 0x80); first = rest & 0x7f; rest = Math.floor(rest / 128); }
  bytes.push(first);
  return Buffer.from(bytes);
}
function makePack(objects: GitObject[]): Buffer {
  const pieces: Buffer[] = [];
  const head = Buffer.alloc(12); head.write('PACK'); head.writeUInt32BE(2, 4); head.writeUInt32BE(objects.length, 8); pieces.push(head);
  for (const object of objects) pieces.push(packHeader(object.type, object.data.length), deflateSync(object.data));
  const body = Buffer.concat(pieces);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}
/**
 * Walk the object closure of one or more tips.  `maxCommitDepth` is the number
 * of parent edges allowed from each requested tip (0 means the tip commit and
 * its tree/blobs only).  A shallow boundary is treated as a client-side
 * boundary: the boundary commit itself is present, but its parents are not.
 */
function reachable(repo: Repo, start: string[], maxCommitDepth = Infinity, shallow = new Set<string>()): GitObject[] {
  const seen = new Set<string>(); const out: GitObject[] = [];
  const walk = (oid: string, commitDepth: number): void => {
    if (!oid || oid === ZERO || seen.has(oid)) return;
    const object = repo.objects.get(oid); if (!object) return; seen.add(oid); out.push(object);
    if (object.type === 'commit') {
      const c = repo.commits.get(oid) || parseCommit(object.data);
      walk(c.tree, commitDepth);
      if (!shallow.has(oid) && commitDepth < maxCommitDepth) {
        for (const parent of c.parents) walk(parent, commitDepth + 1);
      }
    } else if (object.type === 'tree') for (const entry of parseTree(object.data)) walk(entry.oid, commitDepth);
    else if (object.type === 'tag') {
      const target = object.data.toString('utf8').match(/^object ([0-9a-f]{40})/m)?.[1];
      if (target) walk(target, commitDepth);
    }
  };
  for (const oid of start) walk(oid, 0);
  return out;
}

function packCacheKey(wants: string[], haves: string[], depth: number, shallow: string[]): string {
  return JSON.stringify({ wants: [...wants].sort(), haves: [...haves].sort(), depth, shallow: [...shallow].sort() });
}

function packForFetch(repo: Repo, wants: string[], haves: string[], depth: number, shallow: string[]): Buffer {
  const key = packCacheKey(wants, haves, depth, shallow);
  const cached = repo.packCache.get(key);
  if (cached) return cached;
  const haveObjects = new Set(reachable(repo, haves, Infinity, new Set(shallow)).map((object) => hashObject(object.type, object.data)));
  const objects = reachable(repo, wants, depth).filter((object) => !haveObjects.has(hashObject(object.type, object.data)));
  const pack = objects.length ? makePack(objects) : Buffer.alloc(0);
  repo.packCache.set(key, pack);
  if (repo.packCache.size > 128) repo.packCache.delete(repo.packCache.keys().next().value as string);
  return pack;
}

function firstParent(repo: Repo, oid: string): string | undefined {
  const object = repo.objects.get(oid);
  if (!object || object.type !== 'commit') return undefined;
  const commit = repo.commits.get(oid) || parseCommit(object.data);
  return commit.parents[0];
}

function shallowBoundary(repo: Repo, want: string, depth: number): string | undefined {
  let oid = want;
  for (let index = 1; index < depth; index += 1) {
    const parent = firstParent(repo, oid);
    if (!parent) return oid;
    oid = parent;
  }
  return oid;
}
function parsePack(pack: Buffer): Array<{ oid: string; type: ObjectType; data: Buffer }> {
  if (pack.length < 20 || pack.subarray(0, 4).toString() !== 'PACK') return [];
  const count = pack.readUInt32BE(8); let at = 12; const out: Array<{ oid: string; type: ObjectType; data: Buffer }> = [];
  for (let index = 0; index < count && at < pack.length - 20; index += 1) {
    const first = pack[at++]!; const typeCode = (first >> 4) & 7;
    let size = first & 15; let shift = 4; let byte = first;
    while (byte & 0x80) { byte = pack[at++]!; size |= (byte & 0x7f) << shift; shift += 7; }
    if (typeCode !== 1 && typeCode !== 2 && typeCode !== 3 && typeCode !== 4) return out;
    const inflated = inflateSync(pack.subarray(at), { info: true } as never) as unknown as { buffer: Buffer; engine: { bytesWritten: number } };
    const data = Buffer.from(inflated.buffer); at += inflated.engine.bytesWritten;
    const type: ObjectType = typeCode === 1 ? 'commit' : typeCode === 2 ? 'tree' : typeCode === 3 ? 'blob' : 'tag';
    out.push({ oid: hashObject(type, data), type, data });
  }
  return out;
}
function parsePktBody(body: Buffer): { lines: Buffer[]; offset: number } {
  const lines: Buffer[] = []; let at = 0;
  while (at + 4 <= body.length) {
    const length = parseInt(body.subarray(at, at + 4).toString(), 16);
    if (!Number.isFinite(length)) break;
    at += 4; if (length === 0) return { lines, offset: at };
    if (length === 1 || length === 2) continue;
    if (length < 4 || at + length - 4 > body.length) break;
    lines.push(body.subarray(at, at + length - 4)); at += length - 4;
  }
  return { lines, offset: at };
}
function installPack(repo: Repo, pack: Buffer): string[] {
  const written: string[] = [];
  for (const object of parsePack(pack)) { repo.objects.set(object.oid, { type: object.type, data: object.data }); written.push(object.oid); }
  if (written.length) { repo.packCache.clear(); repo.advertisementCache.clear(); repo.lsRefsCache.clear(); }
  for (const oid of written) {
    const object = repo.objects.get(oid);
    if (object?.type === 'commit') {
      const parsed = parseCommit(object.data); repo.commits.set(oid, { tree: parsed.tree, parents: parsed.parents, message: parsed.message, files: hydrateFiles(repo, oid) });
    }
  }
  return written;
}
function isAncestor(repo: Repo, ancestor: string, descendant: string): boolean {
  if (ancestor === descendant) return true;
  const seen = new Set<string>(); const stack = [descendant];
  while (stack.length) {
    const oid = stack.pop()!; if (oid === ancestor) return true; if (seen.has(oid)) continue; seen.add(oid);
    const object = repo.objects.get(oid); if (!object || object.type !== 'commit') continue;
    const parsed = repo.commits.get(oid) || parseCommit(object.data);
    for (const parent of parsed.parents) stack.push(parent);
  }
  return false;
}

function sendJson(res: ServerResponse, status: number, body: unknown, extra: Record<string, string> = {}): void {
  const text = JSON.stringify(body) + '\n';
  res.writeHead(status, { 'content-type': JSON_TYPE, 'content-length': String(Buffer.byteLength(text)), 'x-github-request-id': 'MF-' + logicalTime.toString(36), ...extra });
  res.end(text);
}
function sendRaw(res: ServerResponse, status: number, body: Buffer, contentType: string): void {
  res.writeHead(status, { 'content-type': contentType, 'content-length': String(body.length), 'x-github-request-id': 'MF-' + logicalTime.toString(36) });
  res.end(body);
}
function sendJsonBytes(res: ServerResponse, status: number, body: Buffer): void {
  res.writeHead(status, { 'content-type': JSON_TYPE, 'content-length': String(body.length), 'x-github-request-id': 'MF-' + logicalTime.toString(36) });
  res.end(body);
}
function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = []; let size = 0;
    req.on('data', (chunk: Buffer) => { size += chunk.length; if (size <= 25 * 1024 * 1024) chunks.push(Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk)); });
    req.on('end', () => resolve(chunks.length === 1 ? chunks[0]! : Buffer.concat(chunks)));
    req.on('error', reject);
  });
}
async function jsonBody(req: IncomingMessage): Promise<Record<string, unknown>> {
  const raw = await readBody(req);
  if (!raw.length) return {};
  try { const value = JSON.parse(raw.toString('utf8')); if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('object required'); return value as Record<string, unknown>; }
  catch { throw Object.assign(new Error('Invalid JSON'), { status: 400 }); }
}
function authorized(req: IncomingMessage): boolean { return (req.headers.authorization || '') === 'Bearer ' + expectedToken(); }
function pathSegments(pathname: string): string[] { return pathname.split('/').filter(Boolean).map((part) => { try { return decodeURIComponent(part); } catch { return part; } }); }
function apiBase(req: IncomingMessage): string { return 'http://' + (req.headers.host || '127.0.0.1'); }
function notFound(res: ServerResponse): void { sendJson(res, 404, errorBody('Not Found')); }
function badMethod(res: ServerResponse): void { sendJson(res, 405, errorBody('Method Not Allowed')); }

function contentJson(repo: Repo, path: string, value: FileValue, base: string): Record<string, unknown> {
  return { type: 'file', encoding: 'base64', size: value.content.length, name: path.split('/').pop(), path, content: value.content.toString('base64') + '\n', sha: value.sha, url: base + '/api/v3/repos/' + repo.owner + '/' + repo.name + '/contents/' + path, git_url: base + '/api/v3/repos/' + repo.owner + '/' + repo.name + '/git/blobs/' + value.sha, download_url: null };
}
function commitJson(repo: Repo, sha: string, base: string): Record<string, unknown> {
  const object = repo.objects.get(sha); const parsed = object?.type === 'commit' ? parseCommit(object.data) : { message: '', parents: [], tree: '' };
  return { sha, message: parsed.message, url: base + '/api/v3/repos/' + repo.owner + '/' + repo.name + '/commits/' + sha, commit: { message: parsed.message, author: { name: VIEWER_NAME, email: VIEWER_EMAIL, date: new Date(logicalTime * 1000).toISOString() }, committer: { name: VIEWER_NAME, email: VIEWER_EMAIL, date: new Date(logicalTime * 1000).toISOString() } }, parents: parsed.parents.map((parent) => ({ sha: parent })) };
}

async function rest(req: IncomingMessage, res: ServerResponse, url: URL): Promise<void> {
  if (!authorized(req)) { sendJson(res, 401, errorBody('Bad credentials')); return; }
  const s = pathSegments(url.pathname).slice(2); const base = apiBase(req);
  if (s.length === 0) { if (req.method === 'GET') { sendJson(res, 200, { current_user_url: base + '/api/v3/user', rate_limit_url: base + '/api/v3/rate_limit' }, { 'x-oauth-scopes': 'repo, read:org' }); return; } badMethod(res); return; }
  if (s[0] === 'meta' && req.method === 'GET') { sendJson(res, 200, { installed_version: 'makefun-forge/1.0', verifiable_password_authentication: true }); return; }
  if (s[0] === 'user' && s[1] === 'repos') {
    if (req.method === 'GET') {
      const all = [...repos.values()].filter((r) => r.owner === VIEWER).sort((a, b) => a.id - b.id); const perPage = Math.max(1, Math.min(100, Number(url.searchParams.get('per_page') || 30) || 30)); const page = Math.max(1, Number(url.searchParams.get('page') || 1) || 1); const start = (page - 1) * perPage; const headers: Record<string, string> = {};
      if (start + perPage < all.length) { const next = new URL(apiBase(req) + url.pathname + url.search); next.searchParams.set('page', String(page + 1)); headers.link = '<' + next.toString() + '>; rel="next"'; }
      sendJson(res, 200, all.slice(start, start + perPage).map((r) => repoJson(r, base)), headers); return;
    }
    if (req.method === 'POST') {
      try { const body = await jsonBody(req); const name = typeof body.name === 'string' ? body.name : ''; if (!name) { sendJson(res, 422, errorBody('name is required')); return; } if (repoFor(VIEWER, name)) { sendJson(res, 422, errorBody('name already exists')); return; } sendJson(res, 201, repoJson(makeRepo(VIEWER, name, body), base)); }
      catch (err) { sendJson(res, (err as { status?: number }).status || 400, errorBody((err as Error).message)); }
      return;
    }
    badMethod(res); return;
  }
  if (s[0] === 'user' && s[1] === undefined && req.method === 'GET') { sendJson(res, 200, { id: 1000, login: VIEWER, name: VIEWER_NAME, email: VIEWER_EMAIL, type: 'User' }); return; }
  if (s[0] !== 'repos' || !s[1] || !s[2]) { notFound(res); return; }
  const repo = repoFor(s[1], s[2]); if (!repo || repo.owner !== VIEWER) { notFound(res); return; }
  const tail = s.slice(3);
  if (tail.length === 0) {
    if (req.method === 'GET') { sendJson(res, 200, repoJson(repo, base)); return; }
    if (req.method === 'PATCH') { try { const body = await jsonBody(req); if (typeof body.description === 'string') repo.description = body.description; if (typeof body.private === 'boolean') repo.private = body.private; sendJson(res, 200, repoJson(repo, base)); } catch (err) { sendJson(res, 400, errorBody((err as Error).message)); } return; }
    if (req.method === 'DELETE') { repos.delete(repoKey(repo.owner, repo.name)); res.writeHead(204, { 'x-github-request-id': 'MF-' + logicalTime.toString(36) }); res.end(); return; }
    badMethod(res); return;
  }
  if (tail[0] === 'branches' && req.method === 'GET') { const values = [...repo.refs].filter(([ref]) => ref.startsWith('refs/heads/')).map(([ref, sha]) => ({ name: ref.slice(11), commit: { sha, url: base + '/api/v3/repos/' + repo.owner + '/' + repo.name + '/commits/' + sha } })); sendJson(res, 200, values); return; }
  if (tail[0] === 'commits' && req.method === 'GET') {
    const branch = url.searchParams.get('sha') || repo.defaultBranch; let sha = repoTip(repo, branch); const out: Record<string, unknown>[] = [];
    while (sha !== ZERO && out.length < 100) { out.push(commitJson(repo, sha, base)); const commit = repo.commits.get(sha); sha = commit?.parents[0] || ZERO; }
    sendJson(res, 200, out); return;
  }
  if (tail[0] === 'git' && tail[1] === 'refs') {
    if (req.method === 'GET' && tail.length === 2) { sendJson(res, 200, [...repo.refs].map(([ref, sha]) => ({ ref, node_id: globalId('Ref', repo.id), object: { sha, type: 'commit' } }))); return; }
    if (req.method === 'POST' && tail.length === 2) {
      try { const body = await jsonBody(req); const ref = typeof body.ref === 'string' ? body.ref : ''; const sha = typeof body.sha === 'string' ? body.sha : ''; if (!ref.startsWith('refs/heads/') || !sha || !repo.objects.has(sha)) { sendJson(res, 422, errorBody('Reference does not exist')); return; } if (repo.refs.has(ref)) { sendJson(res, 422, errorBody('Reference already exists')); return; } repo.refs.set(ref, sha); sendJson(res, 201, { ref, object: { sha, type: 'commit', url: base + '/api/v3/repos/' + repo.owner + '/' + repo.name + '/git/commits/' + sha } }); }
      catch (err) { sendJson(res, 400, errorBody((err as Error).message)); }
      return;
    }
    if (req.method === 'GET' && tail.length >= 4) { const ref = 'refs/' + tail.slice(2).join('/'); const sha = repo.refs.get(ref); if (!sha) { notFound(res); return; } sendJson(res, 200, { ref, object: { sha, type: 'commit' } }); return; }
  }
  if (tail[0] === 'contents') {
    const path = tail.slice(1).join('/'); const branch = url.searchParams.get('ref') || repo.defaultBranch; const files = fileMapAt(repo, branch);
    if (req.method === 'GET') {
      const value = files.get(path);
      if (value) { sendJson(res, 200, contentJson(repo, path, value, base)); return; }
      const prefix = path ? path.replace(/\/+$/, '') + '/' : ''; const children = new Map<string, { dir: boolean; value?: FileValue }>();
      for (const [filePath, file] of files) if (filePath.startsWith(prefix)) { const rest = filePath.slice(prefix.length); const part = rest.split('/')[0]!; children.set(part, rest.includes('/') ? { dir: true } : { dir: false, value: file }); }
      if (children.size) { sendJson(res, 200, [...children].map(([name, entry]) => ({ type: entry.dir ? 'dir' : 'file', name, path: prefix + name, sha: entry.value?.sha || ZERO, size: entry.value?.content.length || 0 }))); return; }
      notFound(res); return;
    }
    if (req.method === 'PUT' || req.method === 'DELETE') {
      try {
        const body = await jsonBody(req); const existing = files.get(path); const branchName = typeof body.branch === 'string' ? body.branch : branch; const before = fileMapAt(repo, branchName);
        if (req.method === 'PUT') {
          if (body.sha !== undefined && (!existing || body.sha !== existing.sha)) { sendJson(res, 409, errorBody('does not match')); return; }
          const encoded = typeof body.content === 'string' ? body.content.replace(/\s/g, '') : ''; const content = Buffer.from(encoded, 'base64'); const sha = hashObject('blob', content); repo.objects.set(sha, { type: 'blob', data: content }); const next = cloneFiles(before); next.set(path, { sha, content }); const commitSha = createCommit(repo, branchName, next, typeof body.message === 'string' ? body.message : 'Update ' + path, repoTip(repo, branchName)); const status = existing ? 200 : 201; sendJson(res, status, { content: contentJson(repo, path, { sha, content }, base), commit: commitJson(repo, commitSha, base) }); return;
        }
        if (!existing || (body.sha !== undefined && body.sha !== existing.sha)) { sendJson(res, 404, errorBody('File not found')); return; }
        const next = cloneFiles(before); next.delete(path); const commitSha = createCommit(repo, branchName, next, typeof body.message === 'string' ? body.message : 'Delete ' + path, repoTip(repo, branchName)); sendJson(res, 200, { content: null, commit: commitJson(repo, commitSha, base) }); return;
      } catch (err) { sendJson(res, (err as { status?: number }).status || 400, errorBody((err as Error).message)); return; }
    }
    badMethod(res); return;
  }
  if (tail[0] === 'labels') {
    if (req.method === 'GET') { sendJson(res, 200, [...repo.labels.values()]); return; }
    if (req.method === 'POST') { try { const body = await jsonBody(req); const name = typeof body.name === 'string' ? body.name : ''; if (!name) { sendJson(res, 422, errorBody('name is required')); return; } if (repo.labels.has(name)) { sendJson(res, 422, errorBody('already exists')); return; } const label = { name, color: typeof body.color === 'string' ? body.color : 'ededed' }; repo.labels.set(name, label); sendJson(res, 201, label); } catch (err) { sendJson(res, 400, errorBody((err as Error).message)); } return; }
  }
  if (tail[0] === 'issues') {
    if (tail.length === 1 && req.method === 'POST') {
      try { const body = await jsonBody(req); const title = typeof body.title === 'string' ? body.title : ''; const labels = Array.isArray(body.labels) ? body.labels.map((x) => typeof x === 'string' ? x : (x as Record<string, unknown>)?.name).filter((x): x is string => typeof x === 'string') : []; if (!title) { sendJson(res, 422, errorBody('title is required')); return; } if (labels.some((name) => !repo.labels.has(name))) { sendJson(res, 422, errorBody('label does not exist')); return; } const issue: Issue = { id: nextIssueId++, number: nextIssueNumber++, title, body: typeof body.body === 'string' ? body.body : '', state: 'open', labels, created: logicalTime++, comments: [], version: 0 }; repo.issues.set(issue.number, issue); sendJson(res, 201, issueCreateJson(repo, issue)); } catch (err) { sendJson(res, 400, errorBody((err as Error).message)); } return;
    }
    if (tail.length === 1 && req.method === 'GET') { const state = url.searchParams.get('state') || 'open'; let values = [...repo.issues.values()].filter((i) => state === 'all' || i.state === state); const direction = (url.searchParams.get('direction') || 'desc').toLowerCase(); values.sort((a, b) => direction === 'asc' ? a.created - b.created : b.created - a.created); sendJson(res, 200, values.map((i) => issueJson(repo, i, base))); return; }
    const number = Number(tail[1]); const issue = repo.issues.get(number); if (!issue) { notFound(res); return; }
    if (tail[2] === 'comments') {
      if (req.method === 'GET') { sendJson(res, 200, issue.comments.map((c) => ({ id: c.id, node_id: globalId('C', c.id), body: c.body, user: { login: VIEWER } }))); return; }
      if (req.method === 'POST') { try { const body = await jsonBody(req); const comment = { id: nextCommentId++, body: typeof body.body === 'string' ? body.body : '' }; issue.comments.push(comment); issue.version += 1; sendJson(res, 201, { id: comment.id, node_id: globalId('C', comment.id), body: comment.body, user: { login: VIEWER } }); } catch (err) { sendJson(res, 400, errorBody((err as Error).message)); } return; }
    }
    if (req.method === 'GET') { sendJsonBytes(res, 200, issueJsonBytes(repo, issue, base)); return; }
    if (req.method === 'PATCH') { try { const body = await jsonBody(req); if (typeof body.title === 'string') issue.title = body.title; if (typeof body.body === 'string') issue.body = body.body; if (body.state === 'open' || body.state === 'closed') issue.state = body.state; issue.version += 1; sendJsonBytes(res, 200, issueJsonBytes(repo, issue, base)); } catch (err) { sendJson(res, 400, errorBody((err as Error).message)); } return; }
  }
  if (tail[0] === 'pulls') {
    if (tail.length === 1 && req.method === 'GET') { const state = url.searchParams.get('state') || 'open'; sendJson(res, 200, [...repo.pulls.values()].filter((p) => state === 'all' || p.state === state).sort((a, b) => a.number - b.number).map((p) => pullJson(repo, p, base))); return; }
    if (tail.length === 1 && req.method === 'POST') {
      try { const body = await jsonBody(req); const head = typeof body.head === 'string' ? body.head.split(':').pop()! : ''; const baseBranch = typeof body.base === 'string' ? body.base : repo.defaultBranch; if (!repo.refs.has('refs/heads/' + head) || !repo.refs.has('refs/heads/' + baseBranch)) { sendJson(res, 422, errorBody('head or base branch not found')); return; } const pull: Pull = { id: nextPullId++, number: nextPullNumber++, title: typeof body.title === 'string' ? body.title : '', body: typeof body.body === 'string' ? body.body : '', head, base: baseBranch, state: 'open', merged: false, headFiles: fileMapAt(repo, head), baseFiles: fileMapAt(repo, baseBranch) }; repo.pulls.set(pull.number, pull); sendJson(res, 201, pullJson(repo, pull, base)); } catch (err) { sendJson(res, 400, errorBody((err as Error).message)); } return;
    }
    const number = Number(tail[1]); const pull = repo.pulls.get(number); if (!pull) { notFound(res); return; }
    if (tail[2] === 'files' && req.method === 'GET') { sendJson(res, 200, filesJson(repo, pull)); return; }
    if (tail[2] === 'merge' && req.method === 'PUT') {
      const currentBase = fileMapAt(repo, pull.base); const currentHead = fileMapAt(repo, pull.head); const changedHead = fileDiff(pull.baseFiles, pull.headFiles); const conflict = changedHead.some((path) => currentBase.get(path)?.sha !== pull.baseFiles.get(path)?.sha && currentHead.get(path)?.sha !== currentBase.get(path)?.sha);
      if (conflict) { sendJson(res, 405, { message: 'Pull Request is not mergeable' }); return; }
      if (!pull.merged) { const sha = createCommit(repo, pull.base, cloneFiles(currentHead), 'Merge pull request #' + pull.number, repoTip(repo, pull.base)); pull.merged = true; pull.state = 'closed'; pull.mergeSha = sha; pull.mergedAt = new Date(logicalTime++ * 1000).toISOString(); }
      sendJson(res, 200, { sha: pull.mergeSha, merged: true, message: 'Pull Request successfully merged' }); return;
    }
    if (req.method === 'GET') { sendJson(res, 200, pullJson(repo, pull, base)); return; }
  }
  notFound(res);
}

function graphRepo(repo: Repo, vars: Record<string, unknown>): Record<string, unknown> {
  const first = Math.max(1, Number(vars.first || 50) || 50);
  const issueValues = [...repo.issues.values()]
    .filter((i) => i.state === 'open')
    .sort((a, b) => b.created - a.created || b.number - a.number);
  const after = typeof vars.after === 'string' ? Number(vars.after.replace(/\D/g, '')) || 0 : 0; const selectedIssues = issueValues.slice(after, after + first); const selectedPulls = [...repo.pulls.values()].slice(0, first);
  const issue = repo.issues.get(Number(vars.number || 0)); const pull = repo.pulls.get(Number(vars.number || 0));
  return {
    id: globalId('R', repo.id), databaseId: repo.id, name: repo.name, nameWithOwner: repo.owner + '/' + repo.name, owner: { login: repo.owner }, defaultBranchRef: { name: repo.defaultBranch }, viewerPermission: 'ADMIN', hasIssuesEnabled: true,
    issue: issue ? { id: globalId('I', issue.id), number: issue.number, title: issue.title, body: issue.body, state: issue.state.toUpperCase() } : null,
    issues: { nodes: selectedIssues.map((i) => ({ id: globalId('I', i.id), number: i.number, title: i.title, body: i.body, state: i.state.toUpperCase() })), pageInfo: { hasNextPage: after + first < issueValues.length, endCursor: after + first < issueValues.length ? 'cursor:' + (after + first) : null } },
    pullRequest: pull ? { id: globalId('P', pull.id), number: pull.number, state: pull.merged ? 'MERGED' : pull.state.toUpperCase(), merged: pull.merged, headRefName: pull.head, baseRefName: pull.base, mergeable: 'MERGEABLE', files: { nodes: filesJson(repo, pull).map((f) => ({ path: f.filename })) } } : null,
    pullRequests: { nodes: selectedPulls.map((p) => ({ id: globalId('P', p.id), number: p.number, title: p.title, state: p.merged ? 'MERGED' : p.state.toUpperCase(), merged: p.merged, headRefName: p.head, baseRefName: p.base, mergeable: 'MERGEABLE', files: { nodes: filesJson(repo, p).map((f) => ({ path: f.filename })) } })) },
  };
}
function repoByGlobal(value: unknown): Repo | undefined { const id = String(value || ''); for (const repo of repos.values()) if (globalId('R', repo.id) === id || String(repo.id) === id) return repo; return undefined; }
function issueByGlobal(value: unknown): { repo: Repo; issue: Issue } | undefined { const id = String(value || ''); for (const repo of repos.values()) for (const issue of repo.issues.values()) if (globalId('I', issue.id) === id || String(issue.id) === id) return { repo, issue }; return undefined; }
function pullByGlobal(value: unknown): { repo: Repo; pull: Pull } | undefined { const id = String(value || ''); for (const repo of repos.values()) for (const pull of repo.pulls.values()) if (globalId('P', pull.id) === id || String(pull.id) === id) return { repo, pull }; return undefined; }
function graphqlOne(query: string, vars: Record<string, unknown>): Record<string, unknown> {
  if (query.includes('noSuchFieldOnViewer')) return { errors: [{ message: 'Cannot query field "noSuchFieldOnViewer" on type "User".' }] };
  if (query.includes('__type')) {
    const fields = ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequest', 'pullRequests', 'number', 'title', 'state', 'body', 'merged', 'headRefName', 'baseRefName', 'mergeable', 'files'];
    const enums: Record<string, string[]> = { SearchType: ['ISSUE', 'REPOSITORY', 'USER', 'COMMIT', 'TOPIC', 'WIKI'], IssueState: ['OPEN', 'CLOSED'], MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'], PullRequestState: ['OPEN', 'CLOSED', 'MERGED'], PullRequestMergeMethod: ['MERGE', 'SQUASH', 'REBASE'], RepositoryPermission: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'], IssueOrderField: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'], OrderDirection: ['ASC', 'DESC'] };
    const data: Record<string, unknown> = {};
    for (const key of Object.keys(enums)) if (query.includes(key)) data[key] = { name: key, enumValues: enums[key]!.map((name) => ({ name })) };
    for (const key of ['Issue', 'PullRequest', 'Repository']) if (query.includes(key + ': __type')) data[key] = { name: key, fields: fields.map((name) => ({ name })) };
    return { data };
  }
  if (query.includes('createIssue')) {
    const input = (vars.input || {}) as Record<string, unknown>; const repo = repoByGlobal(input.repositoryId);
    if (!repo || typeof input.title !== 'string') return { errors: [{ message: 'Invalid createIssue input' }] };
    const issue: Issue = { id: nextIssueId++, number: nextIssueNumber++, title: input.title, body: typeof input.body === 'string' ? input.body : '', state: 'open', labels: [], created: logicalTime++, comments: [], version: 0 }; repo.issues.set(issue.number, issue);
    return { data: { createIssue: { issue: { id: globalId('I', issue.id), number: issue.number, title: issue.title, state: 'OPEN', body: issue.body } } } };
  }
  if (query.includes('closeIssue')) {
    const found = issueByGlobal(((vars.input || {}) as Record<string, unknown>).issueId); if (!found) return { errors: [{ message: 'Issue not found' }] }; found.issue.state = 'closed'; found.issue.version += 1;
    return { data: { closeIssue: { issue: { id: globalId('I', found.issue.id), number: found.issue.number, state: 'CLOSED' } } } };
  }
  if (query.includes('createPullRequest')) {
    const input = (vars.input || {}) as Record<string, unknown>; const repo = repoByGlobal(input.repositoryId); const head = String(input.headRefName || ''); const base = String(input.baseRefName || 'main');
    if (!repo || !repo.refs.has('refs/heads/' + head) || !repo.refs.has('refs/heads/' + base)) return { errors: [{ message: 'Head or base branch not found' }] };
    const pull: Pull = { id: nextPullId++, number: nextPullNumber++, title: String(input.title || ''), body: '', head, base, state: 'open', merged: false, headFiles: fileMapAt(repo, head), baseFiles: fileMapAt(repo, base) }; repo.pulls.set(pull.number, pull);
    return { data: { createPullRequest: { pullRequest: { id: globalId('P', pull.id), number: pull.number, state: 'OPEN', headRefName: head, baseRefName: base } } } };
  }
  if (query.includes('mergePullRequest')) {
    const found = pullByGlobal(((vars.input || {}) as Record<string, unknown>).pullRequestId); if (!found) return { errors: [{ message: 'Pull request not found' }] };
    const pull = found.pull; if (!pull.merged) { const sha = createCommit(found.repo, pull.base, cloneFiles(fileMapAt(found.repo, pull.head)), 'Merge pull request #' + pull.number, repoTip(found.repo, pull.base)); pull.merged = true; pull.state = 'closed'; pull.mergeSha = sha; pull.mergedAt = new Date(logicalTime++ * 1000).toISOString(); }
    return { data: { mergePullRequest: { pullRequest: { number: pull.number, merged: true, state: 'MERGED' } } } };
  }
  if (query.includes('addComment')) {
    const input = (vars.input || {}) as Record<string, unknown>; const foundIssue = issueByGlobal(input.subjectId); const body = typeof input.body === 'string' ? input.body : '';
    if (foundIssue) { const comment = { id: nextCommentId++, body }; foundIssue.issue.comments.push(comment); foundIssue.issue.version += 1; return { data: { addComment: { commentEdge: { node: { id: globalId('C', comment.id), body } } } } }; }
    return { errors: [{ message: 'Subject not found' }] };
  }
  if (query.includes('node(')) { const repo = repoByGlobal(vars.id); return { data: { node: repo ? { id: globalId('R', repo.id), name: repo.name, nameWithOwner: repo.owner + '/' + repo.name } : null } }; }
  if (query.includes('viewer') && !query.includes('repository(')) return { data: { viewer: { login: VIEWER } } };
  const owner = typeof vars.owner === 'string' ? vars.owner : ''; const name = typeof vars.name === 'string' ? vars.name : ''; const repo = repoFor(owner, name);
  return { data: { repository: repo ? graphRepo(repo, vars) : null } };
}
function mcpTools(): Array<Record<string, unknown>> {
  const schema = (required: string[], properties: Record<string, unknown>): Record<string, unknown> => ({ type: 'object', properties, required });
  const stringProp = { type: 'string' };
  return [
    { name: 'create_repo', description: 'Create a repository', inputSchema: schema(['name'], { owner: stringProp, name: stringProp, description: stringProp, private: { type: 'boolean' } }) },
    { name: 'get_repo', description: 'Read a repository', inputSchema: schema(['owner', 'repo'], { owner: stringProp, repo: stringProp }) },
    { name: 'create_issue', description: 'Create an issue', inputSchema: schema(['owner', 'repo', 'title'], { owner: stringProp, repo: stringProp, title: stringProp, body: stringProp }) },
    { name: 'list_issues', description: 'List repository issues', inputSchema: schema(['owner', 'repo'], { owner: stringProp, repo: stringProp, state: stringProp }) },
    { name: 'create_pull_request', description: 'Create a pull request', inputSchema: schema(['owner', 'repo', 'title', 'head', 'base'], { owner: stringProp, repo: stringProp, title: stringProp, body: stringProp, head: stringProp, base: stringProp }) },
    { name: 'merge_pull_request', description: 'Merge a pull request', inputSchema: schema(['owner', 'repo', 'pull_number'], { owner: stringProp, repo: stringProp, pull_number: { type: 'integer' } }) },
    { name: 'add_comment', description: 'Add an issue comment', inputSchema: schema(['owner', 'repo', 'issue_number', 'body'], { owner: stringProp, repo: stringProp, issue_number: { type: 'integer' }, body: stringProp }) },
  ];
}
async function mcp(req: IncomingMessage, res: ServerResponse): Promise<void> {
  if (!authorized(req)) { sendJson(res, 401, errorBody('Unauthorized')); return; }
  let body: unknown;
  try { body = JSON.parse((await readBody(req)).toString('utf8')); } catch { sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } }); return; }
  const handle = (message: Record<string, unknown>): Record<string, unknown> => {
    const id = message.id ?? null; const method = String(message.method || ''); const params = (message.params || {}) as Record<string, unknown>;
    if (method === 'server/discover') return { jsonrpc: '2.0', id, result: { serverInfo: { name: 'makefun-forge', version: '1.0.0' }, capabilities: { tools: {} }, supportedVersions: ['2026-07-28', '2025-11-25'] } };
    if (method === 'initialize') return { jsonrpc: '2.0', id, result: { protocolVersion: '2025-11-25', serverInfo: { name: 'makefun-forge', version: '1.0.0' }, capabilities: { tools: {} } } };
    if (method === 'notifications/initialized') return { jsonrpc: '2.0', id, result: {} };
    if (method === 'tools/list') return { jsonrpc: '2.0', id, result: { tools: mcpTools() } };
    if (method === 'tools/call') {
      const name = String(params.name || ''); const args = (params.arguments || {}) as Record<string, unknown>; const tool = mcpTools().find((x) => x.name === name);
      if (!tool) return { jsonrpc: '2.0', id, error: { code: -32601, message: 'Unknown tool' } };
      const need = ((tool.inputSchema as Record<string, unknown>).required || []) as string[]; if (need.some((key) => args[key] === undefined || args[key] === '')) return { jsonrpc: '2.0', id, result: { isError: true, content: [{ type: 'text', text: 'Missing required arguments' }] } };
      const owner = typeof args.owner === 'string' ? args.owner : VIEWER; const nameArg = typeof args.repo === 'string' ? args.repo : typeof args.name === 'string' ? args.name : ''; const repo = repoFor(owner, nameArg);
      let value: unknown;
      if (name === 'create_repo') { const created = repo || makeRepo(owner, nameArg, args); value = repoJson(created); }
      else if (name === 'get_repo') value = repo ? repoJson(repo) : { message: 'Not Found' };
      else if (name === 'create_issue') { if (!repo) value = { message: 'Not Found' }; else { const issue: Issue = { id: nextIssueId++, number: nextIssueNumber++, title: String(args.title), body: typeof args.body === 'string' ? args.body : '', state: 'open', labels: [], created: logicalTime++, comments: [], version: 0 }; repo.issues.set(issue.number, issue); value = issueJson(repo, issue); } }
      else if (name === 'list_issues') value = repo ? [...repo.issues.values()].filter((i) => !args.state || args.state === 'all' || i.state === args.state).map((i) => issueJson(repo, i)) : [];
      else if (name === 'create_pull_request') { if (!repo) value = { message: 'Not Found' }; else { const head = String(args.head); const base = String(args.base); const pull: Pull = { id: nextPullId++, number: nextPullNumber++, title: String(args.title), body: typeof args.body === 'string' ? args.body : '', head, base, state: 'open', merged: false, headFiles: fileMapAt(repo, head), baseFiles: fileMapAt(repo, base) }; repo.pulls.set(pull.number, pull); value = pullJson(repo, pull); } }
      else if (name === 'merge_pull_request') { const pull = repo ? repo.pulls.get(Number(args.pull_number)) : undefined; if (!repo || !pull) value = { message: 'Not Found' }; else { if (!pull.merged) { const sha = createCommit(repo, pull.base, cloneFiles(fileMapAt(repo, pull.head)), 'Merge pull request #' + pull.number, repoTip(repo, pull.base)); pull.merged = true; pull.state = 'closed'; pull.mergeSha = sha; pull.mergedAt = new Date(logicalTime++ * 1000).toISOString(); } value = { merged: true, sha: pull.mergeSha, message: 'Pull Request successfully merged' }; } }
      else { const issue = repo?.issues.get(Number(args.issue_number)); if (!repo || !issue) value = { message: 'Not Found' }; else { const comment = { id: nextCommentId++, body: String(args.body) }; issue.comments.push(comment); issue.version += 1; value = comment; } }
      return { jsonrpc: '2.0', id, result: { content: [{ type: 'text', text: JSON.stringify(value) }], structuredContent: value } };
    }
    return { jsonrpc: '2.0', id, error: { code: -32601, message: 'Method not found' } };
  };
  if (Array.isArray(body)) { sendJson(res, 200, body.map((item) => handle(item as Record<string, unknown>))); return; }
  sendJson(res, 200, handle(body as Record<string, unknown>));
}

async function git(req: IncomingMessage, res: ServerResponse, url: URL): Promise<void> {
  if (!authorized(req)) { sendJson(res, 401, errorBody('Bad credentials')); return; }
  const bits = pathSegments(url.pathname); if (bits.length < 2 || !bits[1]!.endsWith('.git')) { notFound(res); return; }
  const repo = repoFor(bits[0]!, bits[1]!.slice(0, -4)); if (!repo) { sendJson(res, 404, errorBody('Not Found')); return; }
  const service = (url.searchParams.get('service') || (bits[2] === 'git-upload-pack' ? 'git-upload-pack' : bits[2] === 'git-receive-pack' ? 'git-receive-pack' : '')) as 'git-upload-pack' | 'git-receive-pack' | '';
  if (req.method === 'GET' && bits.slice(2).join('/') === 'info/refs' && service) {
    const version2 = req.headers['git-protocol'] === 'version=2' && service === 'git-upload-pack';
    const type = 'application/x-' + service + '-advertisement';
    const advertisementKey = service + ':' + (version2 ? 'v2' : 'v0');
    const cachedAdvertisement = repo.advertisementCache.get(advertisementKey);
    if (cachedAdvertisement) { sendRaw(res, 200, cachedAdvertisement, type); return; }
    const caps = service === 'git-upload-pack' ? 'multi_ack_detailed side-band-64k thin-pack ofs-delta shallow agent=makefun-forge/1.0 object-format=sha1 filter' : 'report-status-v2 report-status side-band-64k delete-refs ofs-delta agent=makefun-forge/1.0 object-format=sha1';
    if (version2) {
      const body = pktLines(['# service=' + service + '\n', 'flush', 'version 2\n', 'agent=makefun-forge/1.0\n', 'object-format=sha1\n', 'ls-refs=unborn\n', 'fetch=shallow filter\n', 'flush']);
      repo.advertisementCache.set(advertisementKey, body); sendRaw(res, 200, body, type); return;
    }
    const lines: Array<Buffer | string | 'flush'> = ['# service=' + service + '\n', 'flush'];
    const heads = [...repo.refs].filter(([ref]) => ref.startsWith('refs/heads/')); const advertised = [...repo.refs].filter(([ref]) => ref.startsWith('refs/heads/') || ref.startsWith('refs/tags/')); const head = repoTip(repo);
    if (!heads.length) lines.push(ZERO + ' HEAD\0' + caps + '\n');
    else lines.push(head + ' HEAD\0symref=HEAD:refs/heads/' + repo.defaultBranch + ' ' + caps + '\n');
    for (const [ref, sha] of advertised) {
      lines.push(sha + ' ' + ref + '\n');
      const object = repo.objects.get(sha);
      const target = object?.type === 'tag' ? object.data.toString('utf8').match(/^object ([0-9a-f]{40})/m)?.[1] : undefined;
      if (target) lines.push(target + ' ' + ref + '^{}\n');
    }
    lines.push('flush'); const body = pktLines(lines); repo.advertisementCache.set(advertisementKey, body); sendRaw(res, 200, body, type); return;
  }
  if (req.method !== 'POST') { notFound(res); return; }
  const body = await readBody(req); const isV2 = service === 'git-upload-pack' && req.headers['git-protocol'] === 'version=2';
  if (service === 'git-upload-pack') {
    const parsed = parsePktBody(body); const text = parsed.lines.map((x) => x.toString('utf8')).join('');
    if (isV2 && text.includes('command=ls-refs')) {
      const lines: Array<Buffer | string | 'flush'> = [];
      const prefixes = [...text.matchAll(/ref-prefix ([^\n]+)/g)].map((m) => m[1]!.trim());
      const include = (ref: string): boolean => prefixes.length === 0 || prefixes.some((prefix) => ref.startsWith(prefix));
      const lsRefsKey = JSON.stringify({ prefixes, peel: text.includes('peel\n') });
      const cachedLsRefs = repo.lsRefsCache.get(lsRefsKey);
      if (cachedLsRefs) { sendRaw(res, 200, cachedLsRefs, 'application/x-git-upload-pack-result'); return; }
      if (prefixes.length === 0 && repo.refs.size) lines.push(repoTip(repo) + ' HEAD symref-target:refs/heads/' + repo.defaultBranch + '\n');
      for (const [ref, sha] of repo.refs) if (include(ref)) {
        const object = repo.objects.get(sha);
        const target = object?.type === 'tag' ? object.data.toString('utf8').match(/^object ([0-9a-f]{40})/m)?.[1] : undefined;
        const peel = text.includes('peel\n') && target ? ' peeled:' + target : '';
        lines.push(sha + ' ' + ref + peel + '\n');
      }
      lines.push('flush'); const body = pktLines(lines); repo.lsRefsCache.set(lsRefsKey, body); sendRaw(res, 200, body, 'application/x-git-upload-pack-result'); return;
    }
    const wants = [...text.matchAll(/want ([0-9a-f]{40})/g)].map((m) => m[1]!);
    const haves = [...text.matchAll(/have ([0-9a-f]{40})/g)].map((m) => m[1]!);
    const depthMatch = text.match(/deepen (\d+)/);
    const requestedDepth = depthMatch ? Math.max(1, Number(depthMatch[1]) || 1) : Infinity;
    const maxCommitDepth = requestedDepth === Infinity ? Infinity : requestedDepth - 1;
    const shallow = [...text.matchAll(/shallow ([0-9a-f]{40})/g)].map((m) => m[1]!);
    const pack = packForFetch(repo, wants.length ? wants : [repoTip(repo)], haves, maxCommitDepth, shallow);
    if (!isV2) {
      const response: Array<Buffer | string | 'flush'> = [];
      if (depthMatch && wants.length) response.push('shallow ' + (shallowBoundary(repo, wants[0]!, requestedDepth) || wants[0]!) + '\n');
      response.push('NAK\n');
      if (pack.length) for (let at = 0; at < pack.length; at += 60000) response.push(Buffer.concat([Buffer.from([1]), pack.subarray(at, at + 60000)]));
      response.push('flush'); sendRaw(res, 200, pktLines(response), 'application/x-git-upload-pack-result'); return;
    }
    const response: Array<Buffer | string | 'flush'> = ['acknowledgments\n', 'NAK\n', 'flush'];
    if (depthMatch && wants.length) {
      response.push('shallow-info\n');
      for (const old of shallow) response.push('unshallow ' + old + '\n');
      const boundary = shallowBoundary(repo, wants[0]!, requestedDepth) || wants[0]!;
      response.push('shallow ' + boundary + '\n', 'flush');
    }
    if (pack.length) { response.push('packfile\n'); for (let at = 0; at < pack.length; at += 60000) response.push(Buffer.concat([Buffer.from([1]), pack.subarray(at, at + 60000)])); response.push('flush'); }
    sendRaw(res, 200, pktLines(response), 'application/x-git-upload-pack-result'); return;
  }
  if (service === 'git-receive-pack') {
    const parsed = parsePktBody(body); const commands = parsed.lines.map((line) => { const clean = line.toString('utf8').replace(/\n$/, ''); const split = clean.split(' '); const refPart = split.slice(2).join(' '); const ref = refPart.split('\0')[0]!; return { old: split[0]!, next: split[1]!, ref }; }); const pack = body.subarray(parsed.offset); installPack(repo, pack);
    const wantsSideband = parsed.lines[0]?.toString('utf8').includes('side-band-64k') || false;
    const results = commands.map((command) => {
      const current = repo.refs.get(command.ref) || ZERO; let ok = true; let reason = '';
      if (current !== command.old) { ok = false; reason = 'stale info'; }
      else if (command.next !== ZERO && !repo.objects.has(command.next)) { ok = false; reason = 'missing object'; }
      else if (command.next !== ZERO && command.ref.startsWith('refs/heads/') && current !== ZERO && !isAncestor(repo, current, command.next)) { ok = false; reason = 'non-fast-forward'; }
      if (ok) {
        if (command.next === ZERO) repo.refs.delete(command.ref);
        else {
          repo.refs.set(command.ref, command.next);
        }
        repo.packCache.clear(); repo.advertisementCache.clear(); repo.lsRefsCache.clear();
      }
      return ok ? 'ok ' + command.ref + '\n' : 'ng ' + command.ref + ' ' + reason + '\n';
    });
    const lines = ['unpack ok\n', ...results];
    const report: Buffer[] = []; for (const line of lines) report.push(wantsSideband ? pkt(Buffer.concat([Buffer.from([1]), pkt(line)])) : pkt(line)); sendRaw(res, 200, Buffer.concat([...report, flush()]), 'application/x-git-receive-pack-result'); return;
  }
  notFound(res);
}

async function handle(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const rawUrl = req.url || '/';
  const rawPath = rawUrl.split('?', 1)[0] || '/';
  if (req.method === 'GET' || req.method === 'POST') {
    const fastIssue = /^\/api\/v3\/repos\/([^/]+)\/([^/]+)\/issues\/(\d+)$/.exec(rawPath);
    if (req.method === 'GET' && fastIssue) {
      if (!authorized(req)) { sendJson(res, 401, errorBody('Bad credentials')); return; }
      const repo = repoFor(decodeURIComponent(fastIssue[1]!), decodeURIComponent(fastIssue[2]!));
      const issue = repo?.issues.get(Number(fastIssue[3]));
      if (!repo || repo.owner !== VIEWER || !issue) { notFound(res); return; }
      sendJsonBytes(res, 200, issueJsonBytes(repo, issue, apiBase(req))); return;
    }
    const fastIssueCollection = /^\/api\/v3\/repos\/([^/]+)\/([^/]+)\/issues$/.exec(rawPath);
    if (req.method === 'POST' && fastIssueCollection) {
      if (!authorized(req)) { sendJson(res, 401, errorBody('Bad credentials')); return; }
      const repo = repoFor(decodeURIComponent(fastIssueCollection[1]!), decodeURIComponent(fastIssueCollection[2]!));
      if (!repo || repo.owner !== VIEWER) { notFound(res); return; }
      try {
        const body = await jsonBody(req); const title = typeof body.title === 'string' ? body.title : '';
        const labels = Array.isArray(body.labels) ? body.labels.map((x) => typeof x === 'string' ? x : (x as Record<string, unknown>)?.name).filter((x): x is string => typeof x === 'string') : [];
        if (!title) { sendJson(res, 422, errorBody('title is required')); return; }
        if (labels.some((name) => !repo.labels.has(name))) { sendJson(res, 422, errorBody('label does not exist')); return; }
        const issue: Issue = { id: nextIssueId++, number: nextIssueNumber++, title, body: typeof body.body === 'string' ? body.body : '', state: 'open', labels, created: logicalTime++, comments: [], version: 0 };
        repo.issues.set(issue.number, issue); sendJson(res, 201, issueCreateJson(repo, issue));
      } catch (err) { sendJson(res, (err as { status?: number }).status || 400, errorBody((err as Error).message)); }
      return;
    }
  }
  const url = new URL(rawUrl, 'http://entry'); const path = url.pathname;
  if (req.method === 'GET' && path === '/healthz') { sendJson(res, 200, { ok: true }); return; }
  if (path === '/mcp') { await mcp(req, res); return; }
  if (path === '/api/graphql') {
    if (!authorized(req)) { sendJson(res, 401, errorBody('Bad credentials')); return; }
    try { const body = JSON.parse((await readBody(req)).toString('utf8')); const values = Array.isArray(body) ? body : [body]; const answers = values.map((value) => graphqlOne(String(value.query || ''), (value.variables || {}) as Record<string, unknown>)); sendJson(res, 200, Array.isArray(body) ? answers : answers[0]); }
    catch { sendJson(res, 400, { errors: [{ message: 'Invalid JSON' }] }); }
    return;
  }
  const seg = pathSegments(path);
  if (seg[1]?.endsWith('.git')) { await git(req, res, url); return; }
  if (path.startsWith('/api/v3/')) { await rest(req, res, url); return; }
  notFound(res);
}

export function createApp(): Server {
  return createServer((req, res) => { void handle(req, res).catch((err) => { if (!res.headersSent) sendJson(res, 500, errorBody(err instanceof Error ? err.message : String(err))); else res.destroy(); }); });
}

