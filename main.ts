// main.ts is mend, the CLI SPEC.md specifies, and this is the kit's starting point for it (MIT). It does sections 1 to 4, 9 and 10 of SPEC.md: the command line, the output and
// exit codes, safe paths, format detection, JSON edits and the all-or-nothing write. The other three formats are
// detected and then read as holding no edit, so they answer `error: parse 1`: reading unified diffs (section 6),
// SEARCH/REPLACE blocks (section 7) and V4A patches (section 8), and matching lines at three tiers (section 5), are
// yours to write. Node 22, the standard library alone; run it as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

/** Move intents recorded by edits that moved a file (SPEC section 2): the run() output turns a
 *  qualifying pair into one `R <old> -> <new>` row instead of a D and an A row. */
const movePairs: Array<{ old: string; nw: string }> = [];
function recordMove(oldP: string, newP: string): void {
  movePairs.push({ old: oldP, nw: newP });
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// ---------------------------------------------------------------------------
// Files and lines (SPEC section 3) and line matching (SPEC section 5).
// ---------------------------------------------------------------------------

/** A file as lines, its own line break and whether it ends with one. */
interface Doc {
  lines: string[];
  br: string;
  ends: boolean;
}

function splitDoc(text: string): Doc {
  if (text === '') return { lines: [], br: '\n', ends: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const ends = text.endsWith(br);
  const parts = text.split(br);
  if (ends) parts.pop();
  return { lines: parts, br, ends };
}

function joinDoc(d: Doc): string {
  if (d.lines.length === 0) return '';
  return d.lines.join(d.br) + (d.ends ? d.br : '');
}

function leadWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
}
function stripTrail(s: string): string {
  return s.replace(/[ \t]+$/, '');
}
function stripBoth(s: string): string {
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}
function lineEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return stripTrail(a) === stripTrail(b);
  return stripBoth(a) === stripBoth(b);
}

/** Positions at which O occurs in `file` at `tier`, at or after `from`. Occurrences may overlap. */
function occurrencesAt(file: string[], o: string[], tier: number, from: number): number[] {
  const out: number[] = [];
  if (o.length === 0) return out;
  for (let i = from; i + o.length <= file.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (!lineEq(file[i + j]!, o[j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier (0, 1, 2 — or only 0 when strict) at which O occurs at or after `from`. */
function findTier(file: string[], o: string[], strict: boolean, from = 0): { tier: number; occ: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const occ = occurrencesAt(file, o, t, from);
    if (occ.length > 0) return { tier: t, occ };
  }
  return null;
}

/** One line of N: `oIdx` is the index into O when it is a context line, else -1. */
interface NItem {
  text: string;
  oIdx: number;
}

/**
 * The lines N writes when it replaces O at `pos` in `file`. Context lines are written as the
 * file's own matched lines; at tier 2 every other line is re-indented from O's first line's
 * leading whitespace to the file's first matched line's.
 */
function buildN(file: string[], pos: number, o: string[], n: NItem[], tier: number): string[] {
  const first = file[pos];
  const f = first === undefined ? '' : leadWs(first);
  const p = o.length > 0 ? leadWs(o[0]!) : '';
  const out: string[] = [];
  for (const it of n) {
    if (it.oIdx >= 0) {
      out.push(file[pos + it.oIdx]!);
      continue;
    }
    let t = it.text;
    if (tier === 2 && /[^ \t]/.test(t) && t.startsWith(p)) t = f + t.slice(p.length);
    out.push(t);
  }
  return out;
}

// ---------------------------------------------------------------------------
// Unified diffs (SPEC section 6).
// ---------------------------------------------------------------------------

interface UHunk {
  a: number;
  o: string[];
  n: NItem[];
  /** A `\` line follows the hunk's last context or `+` line. */
  noNlCtxNew: boolean;
  /** A `\` line follows the hunk's last `+` line. */
  noNlNew: boolean;
}

interface USection {
  oldPath: string | null; // null: /dev/null, no file
  newPath: string | null;
  create: boolean; // new file mode
  del: boolean; // deleted file mode
  hunks: UHunk[];
}

const HUNK_RE = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/;
const DIFF_GIT_RE = /^diff --git a\/(\S+) b\/(\S+)$/;

/** The path a `--- ` or `+++ ` line names: after the four characters, up to the first tab, trimmed; a leading a/ or b/ removed; /dev/null means no file. */
function diffPath(line: string): string | null {
  let p = line.slice(4).split('\t')[0]!.trim();
  if (p === '/dev/null') return null;
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  if (p === '/dev/null') return null;
  return p;
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const n = lines.length;
  const sections: USection[] = [];
  let cur: USection | null = null;
  let inHeader = false;
  let hasPair = false;
  let i = 0;

  const parseHunk = (h: number, a: number): { hunk: UHunk; next: number } => {
    const body: Array<{ kind: 'ctx' | 'old' | 'new' | 'bs'; text: string }> = [];
    let j = h + 1;
    while (j < n) {
      const l = lines[j]!;
      // The body ends at a `--- ` line followed by a `+++ ` line: a new section
      // starts there, so the line is not an old line of this hunk.
      if (l.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
      if (l.startsWith(' ')) {
        body.push({ kind: 'ctx', text: l.slice(1) });
        j++;
      } else if (l.startsWith('-')) {
        body.push({ kind: 'old', text: l.slice(1) });
        j++;
      } else if (l.startsWith('+')) {
        body.push({ kind: 'new', text: l.slice(1) });
        j++;
      } else if (l.startsWith('\\')) {
        body.push({ kind: 'bs', text: l });
        j++;
      } else if (l === '') {
        body.push({ kind: 'ctx', text: '' });
        j++;
      } else break;
    }
    // Empty lines at the end of a body are not part of it.
    while (body.length > 0 && body[body.length - 1]!.kind === 'ctx' && body[body.length - 1]!.text === '') body.pop();
    const o: string[] = [];
    const nn: NItem[] = [];
    for (const e of body) {
      if (e.kind === 'ctx') {
        const idx = o.length;
        o.push(e.text);
        nn.push({ text: e.text, oIdx: idx });
      } else if (e.kind === 'old') o.push(e.text);
      else if (e.kind === 'new') nn.push({ text: e.text, oIdx: -1 });
    }
    let noNlCtxNew = false;
    let noNlNew = false;
    for (let k = body.length - 1; k >= 0; k--) {
      if (body[k]!.kind === 'ctx' || body[k]!.kind === 'new') {
        noNlCtxNew = k + 1 < body.length && body[k + 1]!.kind === 'bs';
        break;
      }
    }
    for (let k = body.length - 1; k >= 0; k--) {
      if (body[k]!.kind === 'new') {
        noNlNew = k + 1 < body.length && body[k + 1]!.kind === 'bs';
        break;
      }
    }
    return { hunk: { a, o, n: nn, noNlCtxNew, noNlNew }, next: j };
  };

  while (i < n) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ')) {
      const m = DIFF_GIT_RE.exec(l);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      cur = { oldPath: m[1]!, newPath: m[2]!, create: false, del: false, hunks: [] };
      sections.push(cur);
      inHeader = true;
      hasPair = false;
      i++;
      continue;
    }
    if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur !== null && inHeader && !hasPair) {
        cur.oldPath = diffPath(l);
        cur.newPath = diffPath(lines[i + 1]!);
        hasPair = true;
        i += 2;
        continue;
      }
      cur = { oldPath: diffPath(l), newPath: diffPath(lines[i + 1]!), create: false, del: false, hunks: [] };
      sections.push(cur);
      inHeader = true;
      hasPair = true;
      i += 2;
      continue;
    }
    if (l.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = HUNK_RE.exec(l);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      const { hunk, next } = parseHunk(i, Number(m[1]));
      cur.hunks.push(hunk);
      inHeader = false;
      i = next;
      continue;
    }
    if (cur !== null && inHeader) {
      if (l.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
      if (l.startsWith('+++ ')) {
        cur.newPath = diffPath(l);
        i++;
        continue;
      }
      if (l.startsWith('rename from ')) {
        if (!hasPair) cur.oldPath = l.slice('rename from '.length).trim();
        i++;
        continue;
      }
      if (l.startsWith('rename to ')) {
        if (!hasPair) cur.newPath = l.slice('rename to '.length).trim();
        i++;
        continue;
      }
      if (l.startsWith('new file mode')) {
        cur.create = true;
        i++;
        continue;
      }
      if (l.startsWith('deleted file mode')) {
        cur.del = true;
        i++;
        continue;
      }
    }
    // Prose, code fences and any other header line: ignored.
    i++;
  }

  return sections.map((sec) => unifiedEdit(sec, strict));
}

function applyUnifiedHunk(doc: Doc, h: UHunk, d: number, strict: boolean, path: string): Doc {
  if (h.o.length === 0) {
    const idx = Math.max(0, Math.min(h.a + d, doc.lines.length));
    const lines = [...doc.lines];
    lines.splice(idx, 0, ...h.n.map((it) => it.text));
    const atEnd = idx === doc.lines.length;
    return { lines, br: doc.br, ends: atEnd ? !h.noNlCtxNew : doc.ends };
  }
  const found = findTier(doc.lines, h.o, strict);
  if (!found) throw new Fail('no-match', path);
  const target = h.a - 1 + d;
  let best = found.occ[0]!;
  let bestDist = Math.abs(best - target);
  for (const p of found.occ) {
    const dist = Math.abs(p - target);
    if (dist < bestDist) {
      best = p;
      bestDist = dist;
    }
  }
  const atEnd = best + h.o.length === doc.lines.length;
  const rep = buildN(doc.lines, best, h.o, h.n, found.tier);
  const lines = [...doc.lines];
  lines.splice(best, h.o.length, ...rep);
  return { lines, br: doc.br, ends: atEnd ? !h.noNlCtxNew : doc.ends };
}

function unifiedEdit(sec: USection, strict: boolean): Edit {
  return (tree) => {
    const oldP = sec.oldPath;
    const newP = sec.newPath;
    if (oldP !== null && !safe(oldP)) throw new Fail('unsafe', oldP);
    if (newP !== null && !safe(newP)) throw new Fail('unsafe', newP);
    const isCreate = (oldP === null || sec.create) && newP !== null;
    const isDelete = !isCreate && (newP === null || sec.del) && oldP !== null;
    if (isCreate) {
      const np = newP!;
      if (tree.get(np) !== null) throw new Fail('exists', np);
      const lines: string[] = [];
      for (const h of sec.hunks) for (const it of h.n) if (it.oIdx < 0) lines.push(it.text);
      let noNl = false;
      for (let hi = sec.hunks.length - 1; hi >= 0; hi--) {
        const h = sec.hunks[hi]!;
        if (h.n.some((it) => it.oIdx < 0)) {
          noNl = h.noNlNew;
          break;
        }
      }
      tree.now.set(np, lines.length === 0 ? '' : lines.join('\n') + (noNl ? '' : '\n'));
      return;
    }
    if (isDelete) {
      const op = oldP!;
      if (tree.get(op) === null) throw new Fail('missing', op);
      tree.now.set(op, null);
      return;
    }
    if (oldP === null || newP === null) return; // both /dev/null: nothing to do
    const isMove = oldP !== newP;
    if (isMove) {
      if (tree.get(oldP) === null) throw new Fail('missing', oldP);
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
    } else if (tree.get(oldP) === null) throw new Fail('missing', oldP);
    let doc = splitDoc(tree.get(oldP)!);
    let d = 0;
    for (const h of sec.hunks) {
      doc = applyUnifiedHunk(doc, h, d, strict, oldP);
      d += h.n.length - h.o.length;
    }
    const after = joinDoc(doc);
    if (isMove) {
      recordMove(oldP, newP);
      tree.now.set(oldP, null);
      tree.now.set(newP, after);
    } else {
      tree.now.set(oldP, after);
    }
  };
}

// ---------------------------------------------------------------------------
// SEARCH/REPLACE blocks (SPEC section 7).
// ---------------------------------------------------------------------------

function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevEnd = -1;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchIdx = i;
    let path: string | null = null;
    for (let j = searchIdx - 1; j > prevEnd; j--) {
      const l = lines[j]!;
      if (blank(l)) continue;
      const t = l.trim();
      if (t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchIdx + 1}`);
      path = prevPath;
    }
    let eq = -1;
    for (let j = searchIdx + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') break;
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
    }
    if (eq < 0) throw new Exit2(`error: parse ${searchIdx + 1}`);
    let rep = -1;
    for (let j = eq + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') break;
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (rep < 0) throw new Exit2(`error: parse ${searchIdx + 1}`);
    const oldLines = lines.slice(searchIdx + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    edits.push(srEdit(path, oldLines, newLines, strict));
    prevPath = path;
    prevEnd = rep;
    i = rep + 1;
  }
  return edits;
}

function srEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const cur = tree.get(path);
    if (cur === null) throw new Fail('missing', path);
    const doc = splitDoc(cur);
    const found = findTier(doc.lines, oldLines, strict);
    if (!found) throw new Fail('no-match', path);
    if (found.occ.length > 1) throw new Fail('ambiguous', path);
    const pos = found.occ[0]!;
    const rep = buildN(doc.lines, pos, oldLines, newLines.map((t) => ({ text: t, oIdx: -1 })), found.tier);
    const lines = [...doc.lines];
    lines.splice(pos, oldLines.length, ...rep);
    tree.now.set(path, joinDoc({ lines, br: doc.br, ends: doc.ends }));
  };
}

// ---------------------------------------------------------------------------
// V4A patches (SPEC section 8).
// ---------------------------------------------------------------------------

interface VChunk {
  anchor: string | null;
  eof: boolean;
  body: Array<{ kind: 'ctx' | 'old' | 'new'; text: string }>;
}

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k--) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  let i = first + 1;
  const isSectionStart = (l: string): boolean =>
    l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ');
  while (i < last) {
    const l = lines[i]!;
    if (blank(l)) {
      i++;
      continue;
    }
    if (l.startsWith('*** Add File: ')) {
      const path = l.slice('*** Add File: '.length).trim();
      const secLines: string[] = [];
      const secStart = i + 1;
      i++;
      while (i < last && !isSectionStart(lines[i]!)) {
        secLines.push(lines[i]!);
        i++;
      }
      while (secLines.length > 0 && blank(secLines[secLines.length - 1]!)) secLines.pop();
      const fileLines: string[] = [];
      for (let k = 0; k < secLines.length; k++) {
        const sl = secLines[k]!;
        if (sl.startsWith('+')) fileLines.push(sl.slice(1));
        else if (sl === '') fileLines.push('');
        else throw new Exit2(`error: parse ${secStart + k + 1}`);
      }
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) !== null) throw new Fail('exists', path);
        tree.now.set(path, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
      });
      continue;
    }
    if (l.startsWith('*** Delete File: ')) {
      const path = l.slice('*** Delete File: '.length).trim();
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) === null) throw new Fail('missing', path);
        tree.now.set(path, null);
      });
      i++;
      continue;
    }
    if (l.startsWith('*** Update File: ')) {
      const path = l.slice('*** Update File: '.length).trim();
      const updateLine = i + 1;
      const secLines: string[] = [];
      const secStart = i + 1;
      i++;
      while (i < last && !isSectionStart(lines[i]!)) {
        secLines.push(lines[i]!);
        i++;
      }
      while (secLines.length > 0 && blank(secLines[secLines.length - 1]!)) secLines.pop();
      edits.push(v4aUpdateEdit(path, secLines, secStart, updateLine, strict));
      continue;
    }
    throw new Exit2(`error: parse ${i + 1}`);
  }
  return edits;
}

/** The first line at or after `from` equal to the anchor at the first tier where one is. */
function findAnchor(file: string[], anchor: string, strict: boolean, from: number): number | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    for (let k = from; k < file.length; k++) {
      if (lineEq(file[k]!, anchor, t)) return k;
    }
  }
  return null;
}

/** The first occurrence of O at or after `from` at the first tier with one; an end-of-file chunk takes only an occurrence ending at the file's last line. */
function findChunkOcc(file: string[], o: string[], strict: boolean, from: number, eof: boolean): { tier: number; pos: number } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const occ = occurrencesAt(file, o, t, from);
    for (const p of occ) {
      if (!eof || p + o.length === file.length) return { tier: t, pos: p };
    }
  }
  return null;
}

function v4aUpdateEdit(path: string, secLines: string[], secStart: number, updateLine: number, strict: boolean): Edit {
  let moveTo: string | null = null;
  let idx = 0;
  if (secLines[0] !== undefined && secLines[0]!.startsWith('*** Move to: ')) {
    moveTo = secLines[0]!.slice('*** Move to: '.length).trim();
    idx = 1;
  }
  const chunks: VChunk[] = [];
  while (idx < secLines.length) {
    const l = secLines[idx]!;
    let anchor: string | null = null;
    if (l.startsWith('@@')) {
      anchor = l.slice(2).trim();
      if (anchor === '') anchor = null;
      idx++;
    }
    const body: VChunk['body'] = [];
    let eof = false;
    while (idx < secLines.length) {
      const b = secLines[idx]!;
      if (b.startsWith('@@') || b === '*** End of File') break;
      if (b.startsWith(' ')) {
        body.push({ kind: 'ctx', text: b.slice(1) });
        idx++;
      } else if (b.startsWith('-')) {
        body.push({ kind: 'old', text: b.slice(1) });
        idx++;
      } else if (b.startsWith('+')) {
        body.push({ kind: 'new', text: b.slice(1) });
        idx++;
      } else if (b === '') {
        body.push({ kind: 'ctx', text: '' });
        idx++;
      } else throw new Exit2(`error: parse ${secStart + idx + 1}`);
    }
    if (idx < secLines.length && secLines[idx] === '*** End of File') {
      eof = true;
      idx++;
    }
    chunks.push({ anchor, eof, body });
  }
  if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${updateLine}`);
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const cur = tree.get(path);
    if (cur === null) throw new Fail('missing', path);
    if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    let doc = splitDoc(cur);
    let cursor = 0;
    for (const ch of chunks) {
      if (ch.anchor !== null) {
        const at = findAnchor(doc.lines, ch.anchor, strict, cursor);
        if (at === null) throw new Fail('no-match', path);
        cursor = at + 1;
      }
      const o: string[] = [];
      const nn: NItem[] = [];
      for (const b of ch.body) {
        if (b.kind === 'ctx') {
          const k = o.length;
          o.push(b.text);
          nn.push({ text: b.text, oIdx: k });
        } else if (b.kind === 'old') o.push(b.text);
        else nn.push({ text: b.text, oIdx: -1 });
      }
      if (o.length === 0) {
        const at = ch.eof ? doc.lines.length : cursor;
        const lines = [...doc.lines];
        lines.splice(at, 0, ...nn.map((it) => it.text));
        doc = { lines, br: doc.br, ends: doc.ends };
        cursor = at + nn.length;
      } else {
        const found = findChunkOcc(doc.lines, o, strict, cursor, ch.eof);
        if (!found) throw new Fail('no-match', path);
        const rep = buildN(doc.lines, found.pos, o, nn, found.tier);
        const lines = [...doc.lines];
        lines.splice(found.pos, o.length, ...rep);
        doc = { lines, br: doc.br, ends: doc.ends };
        cursor = found.pos + rep.length;
      }
    }
    const after = joinDoc(doc);
    if (moveTo !== null) {
      recordMove(path, moveTo);
      tree.now.set(path, null);
      tree.now.set(moveTo, after);
    } else {
      tree.now.set(path, after);
    }
  };
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

function run(args: string[]): { code: number; out: string[] } {
  movePairs.length = 0;
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits =
      kind === 'json'
        ? jsonEdits(text, lines)
        : kind === 'unified'
          ? unifiedEdits(lines, strict)
          : kind === 'search-replace'
            ? searchReplaceEdits(lines, strict)
            : v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const changed = new Map<string, { was: string | null; now: string | null }>();
  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    changed.set(p, { was, now });
  }
  const rows: Array<{ key: string; text: string }> = [];
  const consumed = new Set<string>();
  for (const mv of movePairs) {
    const o = changed.get(mv.old);
    const n = changed.get(mv.nw);
    if (o !== undefined && n !== undefined && o.was !== null && o.now === null && n.was === null && n.now !== null) {
      rows.push({ key: mv.nw, text: `R ${mv.old} -> ${mv.nw}` });
      consumed.add(mv.old);
      consumed.add(mv.nw);
    }
  }
  for (const [p, c] of changed) {
    if (consumed.has(p)) continue;
    rows.push({ key: p, text: `${c.was === null ? 'A' : c.now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  if (!check) {
    for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...rows.map((r) => r.text), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
