// mend: one patch tool for every AI edit format.
//
// Applies a patch written as a unified diff, SEARCH/REPLACE blocks, a V4A
// patch, or JSON tool calls, to the tree of text files in the working
// directory. Every edit applies or the patch reports its failures and
// writes nothing. Node standard library only; no clock, no randomness,
// no network, so two runs on the same input are byte-identical.

import { existsSync, mkdirSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';

// ---------------------------------------------------------------------------
// Small text helpers
// ---------------------------------------------------------------------------

function trimEndWs(s: string): string {
  return s.replace(/[ \t]+$/, '');
}

function isBlank(s: string): boolean {
  return s.trim() === '';
}

function leadingWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
}

function stripOneCr(s: string): string {
  return s.endsWith('\r') ? s.slice(0, -1) : s;
}

// The patch's lines: split at \n, one trailing \r removed from each, and
// the empty piece after a final \n dropped. Line numbers count from 1.
function splitPatch(text: string): string[] {
  const parts = text.split('\n').map(stripOneCr);
  if (text.endsWith('\n')) parts.pop();
  return parts;
}

// Lines of an inserted text (JSON insert): an empty text has no lines.
function splitInserted(text: string): string[] {
  if (text === '') return [];
  const parts = text.split('\n').map(stripOneCr);
  if (text.endsWith('\n')) parts.pop();
  return parts;
}

function byteOrder(a: string, b: string): number {
  return Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8'));
}

// ---------------------------------------------------------------------------
// Files: a file is its lines plus the line break it uses and whether its
// text ends with that break. An empty file has no lines and no final break.
// ---------------------------------------------------------------------------

interface FileShape {
  lines: string[];
  br: string;
  ends: boolean;
}

function shapeOf(raw: string): FileShape {
  if (raw === '') return { lines: [], br: '\n', ends: false };
  const at = raw.indexOf('\n');
  const br = at > 0 && raw[at - 1] === '\r' ? '\r\n' : '\n';
  const ends = raw.endsWith(br);
  const body = ends ? raw.slice(0, -br.length) : raw;
  return { lines: body.split(br), br, ends };
}

function rawOf(shape: FileShape): string {
  if (shape.lines.length === 0) return '';
  return shape.lines.join(shape.br) + (shape.ends ? shape.br : '');
}

function isSafePath(p: string): boolean {
  if (p === '' || p.startsWith('/') || p.includes('\\')) return false;
  for (const seg of p.split('/')) {
    if (seg === '' || seg === '.' || seg === '..') return false;
  }
  return true;
}

// ---------------------------------------------------------------------------
// Matching (SPEC section 5): three tiers, exact, then trailing whitespace
// ignored, then leading and trailing whitespace ignored.
// ---------------------------------------------------------------------------

function linesMatch(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  const ta = trimEndWs(a);
  const tb = trimEndWs(b);
  if (tier === 1) return ta === tb;
  return ta.replace(/^[ \t]+/, '') === tb.replace(/^[ \t]+/, '');
}

function findOccurrences(oldLines: string[], fileLines: string[], tier: number): number[] {
  const found: number[] = [];
  if (oldLines.length === 0) return found;
  for (let i = 0; i + oldLines.length <= fileLines.length; i += 1) {
    let ok = true;
    for (let j = 0; j < oldLines.length; j += 1) {
      if (!linesMatch(oldLines[j], fileLines[i + j], tier)) {
        ok = false;
        break;
      }
    }
    if (ok) found.push(i);
  }
  return found;
}

function firstTierWith(oldLines: string[], fileLines: string[], strict: boolean): { tier: number; at: number[] } | null {
  const top = strict ? 0 : 2;
  for (let tier = 0; tier <= top; tier += 1) {
    const at = findOccurrences(oldLines, fileLines, tier);
    if (at.length > 0) return { tier, at };
  }
  return null;
}

// One new line of an edit: either a context line, written as the file's own
// matched line, or an added line, re-indented at tier 2.
interface NewPiece {
  ctx: boolean;
  text: string;
  oldIdx: number;
}

function renderNew(pieces: NewPiece[], fileLines: string[], at: number, tier: number, oldFirst: string): string[] {
  const out: string[] = [];
  const fileFirst = fileLines[at] ?? '';
  const fromLead = leadingWs(oldFirst);
  const toLead = leadingWs(fileFirst);
  for (const piece of pieces) {
    if (piece.ctx) {
      out.push(fileLines[at + piece.oldIdx]);
      continue;
    }
    let line = piece.text;
    if (tier === 2 && line !== '' && !/^[ \t]+$/.test(line) && line.startsWith(fromLead)) {
      line = toLead + line.slice(fromLead.length);
    }
    out.push(line);
  }
  return out;
}

// ---------------------------------------------------------------------------
// Parse failures and edit failures
// ---------------------------------------------------------------------------

class ParseFault extends Error {
  lineNo: number;
  constructor(lineNo: number) {
    super(`parse ${lineNo}`);
    this.lineNo = lineNo;
  }
}

interface EditFailure {
  code: string;
  path: string;
}

function fail(code: string, path: string): EditFailure {
  return { code, path };
}

// An edit, once parsed, applied against the working tree. On success it
// mutates the tree and may record a move; on failure it changes nothing.
type Tree = Map<string, string>;

interface ApplyOut {
  failure: EditFailure | null;
  move: { oldPath: string; newPath: string } | null;
}

function okOut(move: { oldPath: string; newPath: string } | null = null): ApplyOut {
  return { failure: null, move };
}

function badOut(code: string, path: string): ApplyOut {
  return { failure: fail(code, path), move: null };
}

function checkSafe(paths: (string | null | undefined)[]): EditFailure | null {
  for (const p of paths) {
    if (p === null || p === undefined) continue;
    if (!isSafePath(p)) return fail('unsafe', p);
  }
  return null;
}

// ---------------------------------------------------------------------------
// Format detection (SPEC section 4)
// ---------------------------------------------------------------------------

function detectFormat(lines: string[]): string | null {
  const first = lines.find((l) => !isBlank(l));
  if (first !== undefined && first.trim() === '*** Begin Patch') return 'v4a';
  if (first !== undefined) {
    const ch = first.trimStart()[0];
    if (ch === '[' || ch === '{') return 'json';
  }
  if (lines.some((l) => trimEndWs(l) === '<<<<<<< SEARCH')) return 'search-replace';
  for (let i = 0; i < lines.length; i += 1) {
    if (lines[i].startsWith('diff --git ')) return 'unified';
    if (lines[i].startsWith('--- ') && i + 1 < lines.length && lines[i + 1].startsWith('+++ ')) return 'unified';
  }
  return null;
}

// ---------------------------------------------------------------------------
// Unified diffs (SPEC section 6)
// ---------------------------------------------------------------------------

interface HunkLine {
  kind: ' ' | '-' | '+' | '\\';
  text: string;
}

interface Hunk {
  oldStart: number;
  body: HunkLine[];
}

interface UniSection {
  oldPath: string | null;
  newPath: string | null;
  create: boolean;
  remove: boolean;
  hunks: Hunk[];
}

function pathField(field: string): string | null {
  const cut = field.split('\t')[0].trim();
  if (cut === '/dev/null') return null;
  if (cut.startsWith('a/') || cut.startsWith('b/')) return cut.slice(2);
  return cut;
}

function parseHunkHead(line: string, lineNo: number): number {
  const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@(?: .*)?$/.exec(line);
  if (m === null) throw new ParseFault(lineNo);
  return Number(m[1]);
}

function parseUnified(lines: string[]): UniSection[] {
  const sections: UniSection[] = [];
  let cur: UniSection | null = null;
  let curPair = false;
  let curGitOld: string | null = null;
  let curGitNew: string | null = null;
  let curRenameOld: string | null = null;
  let curRenameNew: string | null = null;
  let inHead = false;

  const finishSection = (): void => {
    if (cur === null) return;
    if (curPair) {
      // oldPath/newPath already set from the ---/+++ pair.
    } else if (curRenameOld !== null || curRenameNew !== null) {
      cur.oldPath = curRenameOld !== null ? curRenameOld : curGitOld;
      cur.newPath = curRenameNew !== null ? curRenameNew : curGitNew;
    } else {
      cur.oldPath = curGitOld;
      cur.newPath = curGitNew;
    }
    sections.push(cur);
  };

  const startSection = (gitOld: string | null, gitNew: string | null): void => {
    finishSection();
    cur = { oldPath: null, newPath: null, create: false, remove: false, hunks: [] };
    curPair = false;
    curGitOld = gitOld;
    curGitNew = gitNew;
    curRenameOld = null;
    curRenameNew = null;
    inHead = true;
  };

  let i = 0;
  while (i < lines.length) {
    const line = lines[i];
    if (line.startsWith('diff --git ')) {
      const rest = line.slice('diff --git '.length);
      if (!rest.startsWith('a/')) throw new ParseFault(i + 1);
      const sep = rest.indexOf(' b/');
      if (sep < 0) throw new ParseFault(i + 1);
      startSection(rest.slice(2, sep), rest.slice(sep + 3));
      i += 1;
      continue;
    }
    if (line.startsWith('--- ') && i + 1 < lines.length && lines[i + 1].startsWith('+++ ')) {
      const oldP = pathField(line.slice(4));
      const newP = pathField(lines[i + 1].slice(4));
      if (cur === null || !inHead || curPair) startSection(null, null);
      cur!.oldPath = oldP;
      cur!.newPath = newP;
      curPair = true;
      i += 2;
      continue;
    }
    if (line.startsWith('--- ')) {
      if (cur !== null && inHead) throw new ParseFault(i + 2);
      i += 1;
      continue;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new ParseFault(i + 1);
      const oldStart = parseHunkHead(line, i + 1);
      const body: HunkLine[] = [];
      let j = i + 1;
      while (j < lines.length) {
        const bl = lines[j];
        // The body also ends at a `diff --git` line and at a `--- ` line
        // followed by a `+++ ` line, even though the latter starts with `-`.
        if (bl.startsWith('diff --git ')) break;
        if (bl.startsWith('--- ') && j + 1 < lines.length && lines[j + 1].startsWith('+++ ')) break;
        if (bl === '') {
          body.push({ kind: ' ', text: '' });
          j += 1;
        } else if (bl[0] === ' ' || bl[0] === '-' || bl[0] === '+' || bl[0] === '\\') {
          body.push({ kind: bl[0] as HunkLine['kind'], text: bl.slice(1) });
          j += 1;
        } else {
          break;
        }
      }
      while (body.length > 0) {
        const last = body[body.length - 1];
        if (last.kind === ' ' && last.text === '') body.pop();
        else break;
      }
      cur.hunks.push({ oldStart, body });
      inHead = false;
      i = j;
      continue;
    }
    if (cur !== null && inHead) {
      if (line.startsWith('rename from ')) curRenameOld = line.slice('rename from '.length).trim();
      else if (line.startsWith('rename to ')) curRenameNew = line.slice('rename to '.length).trim();
      else if (line.startsWith('new file mode')) cur.create = true;
      else if (line.startsWith('deleted file mode')) cur.remove = true;
      i += 1;
      continue;
    }
    i += 1;
  }
  finishSection();
  return sections;
}

// Does a `\` line follow the hunk's last context or `+` line?
function hunkDropsFinalBreak(hunk: Hunk): boolean {
  for (let k = hunk.body.length - 1; k >= 0; k -= 1) {
    if (hunk.body[k].kind === ' ' || hunk.body[k].kind === '+') {
      return k + 1 < hunk.body.length && hunk.body[k + 1].kind === '\\';
    }
  }
  return false;
}

function applyUnified(sec: UniSection, tree: Tree, strict: boolean): ApplyOut {
  const unsafe = checkSafe([sec.oldPath, sec.newPath]);
  if (unsafe !== null) return { failure: unsafe, move: null };
  const oldPath = sec.oldPath;
  const newPath = sec.newPath;
  const isCreate = oldPath === null || sec.create;
  const isDelete = !isCreate && (newPath === null || sec.remove);
  if (isCreate) {
    if (newPath === null) return badOut('unsafe', '');
    if (tree.has(newPath)) return badOut('exists', newPath);
    const made: string[] = [];
    for (const hunk of sec.hunks) {
      for (let k = 0; k < hunk.body.length; k += 1) {
        if (hunk.body[k].kind === '+') made.push(hunk.body[k].text);
      }
    }
    // The drop flag belongs to the last `+` line of the whole section.
    let dropBreak = false;
    for (let h = sec.hunks.length - 1; h >= 0; h -= 1) {
      const hunk = sec.hunks[h];
      let lastPlus = -1;
      for (let k = 0; k < hunk.body.length; k += 1) if (hunk.body[k].kind === '+') lastPlus = k;
      if (lastPlus >= 0) {
        dropBreak = lastPlus + 1 < hunk.body.length && hunk.body[lastPlus + 1].kind === '\\';
        break;
      }
    }
    const shape: FileShape = { lines: made, br: '\n', ends: made.length > 0 && !dropBreak };
    tree.set(newPath, rawOf(shape));
    return okOut();
  }
  if (isDelete) {
    if (oldPath === null) return badOut('unsafe', '');
    if (!tree.has(oldPath)) return badOut('missing', oldPath);
    tree.delete(oldPath);
    return okOut();
  }
  if (oldPath === null || newPath === null) return badOut('unsafe', '');
  if (!tree.has(oldPath)) return badOut('missing', oldPath);
  const isMove = oldPath !== newPath;
  if (isMove && tree.has(newPath)) return badOut('exists', newPath);
  const shape = shapeOf(tree.get(oldPath) as string);
  let drift = 0;
  for (const hunk of sec.hunks) {
    const oldLines: string[] = [];
    const pieces: NewPiece[] = [];
    for (const bl of hunk.body) {
      if (bl.kind === ' ') {
        oldLines.push(bl.text);
        pieces.push({ ctx: true, text: bl.text, oldIdx: oldLines.length - 1 });
      } else if (bl.kind === '-') {
        oldLines.push(bl.text);
      } else if (bl.kind === '+') {
        pieces.push({ ctx: false, text: bl.text, oldIdx: -1 });
      }
    }
    if (oldLines.length === 0) {
      const pos = Math.min(hunk.oldStart + drift, shape.lines.length);
      const atEnd = pos === shape.lines.length;
      const made = renderNew(pieces, shape.lines, pos, 0, '');
      shape.lines.splice(pos, 0, ...made);
      if (atEnd) shape.ends = !hunkDropsFinalBreak(hunk);
      drift += made.length;
      continue;
    }
    const found = firstTierWith(oldLines, shape.lines, strict);
    if (found === null) return badOut('no-match', oldPath);
    const target = hunk.oldStart - 1 + drift;
    let best = found.at[0];
    for (const cand of found.at) {
      if (Math.abs(cand - target) < Math.abs(best - target)) best = cand;
    }
    const atEnd = best + oldLines.length === shape.lines.length;
    const made = renderNew(pieces, shape.lines, best, found.tier, oldLines[0]);
    shape.lines.splice(best, oldLines.length, ...made);
    if (atEnd) shape.ends = !hunkDropsFinalBreak(hunk);
    drift += made.length - oldLines.length;
  }
  const result = rawOf(shape);
  if (isMove) {
    tree.delete(oldPath);
    tree.set(newPath, result);
    return okOut({ oldPath, newPath });
  }
  tree.set(oldPath, result);
  return okOut();
}

// ---------------------------------------------------------------------------
// SEARCH/REPLACE blocks (SPEC section 7)
// ---------------------------------------------------------------------------

interface SrBlock {
  path: string;
  oldLines: string[];
  newLines: string[];
}

function parseSearchReplace(lines: string[]): SrBlock[] {
  const blocks: SrBlock[] = [];
  let prevEnd = 0;
  let i = 0;
  while (i < lines.length) {
    if (trimEndWs(lines[i]) !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    const searchAt = i;
    let path: string | null = null;
    for (let j = searchAt - 1; j >= prevEnd; j -= 1) {
      const cand = lines[j];
      if (isBlank(cand)) continue;
      if (cand.trim().startsWith('```')) continue;
      path = cand.trim();
      break;
    }
    if (path === null) {
      if (blocks.length === 0) throw new ParseFault(searchAt + 1);
      path = blocks[blocks.length - 1].path;
    }
    let eq = -1;
    for (let j = searchAt + 1; j < lines.length; j += 1) {
      if (trimEndWs(lines[j]) === '=======') {
        eq = j;
        break;
      }
    }
    if (eq < 0) throw new ParseFault(searchAt + 1);
    let rep = -1;
    for (let j = eq + 1; j < lines.length; j += 1) {
      if (trimEndWs(lines[j]) === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (rep < 0) throw new ParseFault(searchAt + 1);
    blocks.push({ path, oldLines: lines.slice(searchAt + 1, eq), newLines: lines.slice(eq + 1, rep) });
    prevEnd = rep + 1;
    i = rep + 1;
  }
  return blocks;
}

function applySearchReplace(block: SrBlock, tree: Tree, strict: boolean): ApplyOut {
  const unsafe = checkSafe([block.path]);
  if (unsafe !== null) return { failure: unsafe, move: null };
  if (block.oldLines.length === 0) {
    if (tree.has(block.path)) return badOut('exists', block.path);
    const shape: FileShape = { lines: block.newLines.slice(), br: '\n', ends: block.newLines.length > 0 };
    tree.set(block.path, rawOf(shape));
    return okOut();
  }
  if (!tree.has(block.path)) return badOut('missing', block.path);
  const shape = shapeOf(tree.get(block.path) as string);
  const found = firstTierWith(block.oldLines, shape.lines, strict);
  if (found === null) return badOut('no-match', block.path);
  if (found.at.length > 1) return badOut('ambiguous', block.path);
  const at = found.at[0];
  const pieces: NewPiece[] = block.newLines.map((text) => ({ ctx: false, text, oldIdx: -1 }));
  const made = renderNew(pieces, shape.lines, at, found.tier, block.oldLines[0]);
  shape.lines.splice(at, block.oldLines.length, ...made);
  tree.set(block.path, rawOf(shape));
  return okOut();
}

// ---------------------------------------------------------------------------
// V4A patches (SPEC section 8)
// ---------------------------------------------------------------------------

type V4aSection =
  | { kind: 'add'; path: string; body: string[] }
  | { kind: 'delete'; path: string }
  | { kind: 'update'; path: string; moveTo: string | null; chunks: V4aChunk[] };

interface V4aChunk {
  anchor: string | null;
  body: HunkLine[];
  eof: boolean;
}

function isV4aBodyLine(line: string): boolean {
  return line === '' || line[0] === ' ' || line[0] === '-' || line[0] === '+';
}

function sectionStartOf(line: string): 'add' | 'delete' | 'update' | null {
  if (line.startsWith('*** Add File: ') || line === '*** Add File:') return 'add';
  if (line.startsWith('*** Delete File: ') || line === '*** Delete File:') return 'delete';
  if (line.startsWith('*** Update File: ') || line === '*** Update File:') return 'update';
  return null;
}

function sectionPathOf(line: string): string {
  const at = line.indexOf(': ');
  return at < 0 ? '' : line.slice(at + 2).trim();
}

function parseV4a(lines: string[]): V4aSection[] {
  let first = -1;
  for (let i = 0; i < lines.length; i += 1) {
    if (!isBlank(lines[i])) {
      first = i;
      break;
    }
  }
  if (first < 0) throw new ParseFault(1);
  if (lines[first].trim() !== '*** Begin Patch') throw new ParseFault(first + 1);
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i -= 1) {
    if (!isBlank(lines[i])) {
      last = i;
      break;
    }
  }
  if (lines[last].trim() !== '*** End Patch') throw new ParseFault(lines.length + 1);
  const sections: V4aSection[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i];
    if (isBlank(line)) {
      i += 1;
      continue;
    }
    const kind = sectionStartOf(line);
    if (kind === null) throw new ParseFault(i + 1);
    const path = sectionPathOf(line);
    if (kind === 'add') {
      const body: string[] = [];
      let j = i + 1;
      while (j < last) {
        const bl = lines[j];
        if (bl.startsWith('+')) {
          body.push(bl.slice(1));
          j += 1;
        } else if (bl === '') {
          body.push('');
          j += 1;
        } else {
          break;
        }
      }
      while (body.length > 0 && body[body.length - 1] === '') body.pop();
      sections.push({ kind: 'add', path, body });
      i = j;
      continue;
    }
    if (kind === 'delete') {
      sections.push({ kind: 'delete', path });
      i += 1;
      continue;
    }
    // update
    let j = i + 1;
    let moveTo: string | null = null;
    if (j < last && lines[j].startsWith('*** Move to: ')) {
      moveTo = lines[j].slice('*** Move to: '.length).trim();
      j += 1;
    }
    const chunks: V4aChunk[] = [];
    let firstChunk = true;
    while (j < last) {
      const cl = lines[j];
      if (cl.startsWith('@@')) {
        const anchorText = cl.slice(2).trim();
        const chunk: V4aChunk = { anchor: anchorText === '' ? null : anchorText, body: [], eof: false };
        j += 1;
        j = readV4aChunkBody(lines, j, last, chunk);
        chunks.push(chunk);
        firstChunk = false;
        continue;
      }
      if (firstChunk && isV4aBodyLine(cl)) {
        const chunk: V4aChunk = { anchor: null, body: [], eof: false };
        j = readV4aChunkBody(lines, j, last, chunk);
        chunks.push(chunk);
        firstChunk = false;
        continue;
      }
      if (isBlank(cl) && !firstChunk) {
        // Blank lines between chunks are separators, not body lines.
        j += 1;
        continue;
      }
      break;
    }
    // Blank lines at the end of the section are not part of it: drop any
    // trailing empty context lines the last chunk swallowed.
    if (chunks.length > 0) {
      const tail = chunks[chunks.length - 1].body;
      while (tail.length > 0) {
        const b = tail[tail.length - 1];
        if (b.kind === ' ' && b.text === '') tail.pop();
        else break;
      }
    }
    if (chunks.length === 0 && moveTo === null) throw new ParseFault(i + 1);
    sections.push({ kind: 'update', path, moveTo, chunks });
    i = j;
  }
  return sections;
}

// Reads one chunk's body lines starting at j; returns the next index.
function readV4aChunkBody(lines: string[], j0: number, last: number, chunk: V4aChunk): number {
  let j = j0;
  while (j < last) {
    const bl = lines[j];
    if (bl.trim() === '*** End of File') {
      chunk.eof = true;
      return j + 1;
    }
    if (bl.startsWith('@@') || sectionStartOf(bl) !== null) return j;
    if (bl === '') {
      chunk.body.push({ kind: ' ', text: '' });
      j += 1;
    } else if (bl[0] === ' ' || bl[0] === '-' || bl[0] === '+') {
      chunk.body.push({ kind: bl[0] as HunkLine['kind'], text: bl.slice(1) });
      j += 1;
    } else {
      return j;
    }
  }
  return j;
}

function applyV4a(sec: V4aSection, tree: Tree, strict: boolean): ApplyOut {
  if (sec.kind === 'add') {
    const unsafe = checkSafe([sec.path]);
    if (unsafe !== null) return { failure: unsafe, move: null };
    if (tree.has(sec.path)) return badOut('exists', sec.path);
    const shape: FileShape = { lines: sec.body.slice(), br: '\n', ends: sec.body.length > 0 };
    tree.set(sec.path, rawOf(shape));
    return okOut();
  }
  if (sec.kind === 'delete') {
    const unsafe = checkSafe([sec.path]);
    if (unsafe !== null) return { failure: unsafe, move: null };
    if (!tree.has(sec.path)) return badOut('missing', sec.path);
    tree.delete(sec.path);
    return okOut();
  }
  const unsafe = checkSafe([sec.path, sec.moveTo]);
  if (unsafe !== null) return { failure: unsafe, move: null };
  if (!tree.has(sec.path)) return badOut('missing', sec.path);
  const isMove = sec.moveTo !== null && sec.moveTo !== sec.path;
  if (isMove && tree.has(sec.moveTo as string)) return badOut('exists', sec.moveTo as string);
  const shape = shapeOf(tree.get(sec.path) as string);
  let cursor = 0;
  const topTier = strict ? 0 : 2;
  for (const chunk of sec.chunks) {
    if (chunk.anchor !== null) {
      let foundAt = -1;
      for (let tier = 0; tier <= topTier; tier += 1) {
        for (let k = cursor; k < shape.lines.length; k += 1) {
          if (linesMatch(chunk.anchor, shape.lines[k], tier)) {
            foundAt = k;
            break;
          }
        }
        if (foundAt >= 0) break;
      }
      if (foundAt < 0) return badOut('no-match', sec.path);
      cursor = foundAt + 1;
    }
    const oldLines: string[] = [];
    const pieces: NewPiece[] = [];
    for (const bl of chunk.body) {
      if (bl.kind === ' ') {
        oldLines.push(bl.text);
        pieces.push({ ctx: true, text: bl.text, oldIdx: oldLines.length - 1 });
      } else if (bl.kind === '-') {
        oldLines.push(bl.text);
      } else if (bl.kind === '+') {
        pieces.push({ ctx: false, text: bl.text, oldIdx: -1 });
      }
    }
    if (oldLines.length === 0) {
      const pos = chunk.eof ? shape.lines.length : cursor;
      const made = renderNew(pieces, shape.lines, pos, 0, '');
      shape.lines.splice(pos, 0, ...made);
      cursor = pos + made.length;
      continue;
    }
    let pick: { tier: number; at: number } | null = null;
    for (let tier = 0; tier <= topTier; tier += 1) {
      const occ = findOccurrences(oldLines, shape.lines, tier).filter(
        (at) => at >= cursor && (!chunk.eof || at + oldLines.length === shape.lines.length),
      );
      if (occ.length > 0) {
        pick = { tier, at: occ[0] };
        break;
      }
    }
    if (pick === null) return badOut('no-match', sec.path);
    const made = renderNew(pieces, shape.lines, pick.at, pick.tier, oldLines[0]);
    shape.lines.splice(pick.at, oldLines.length, ...made);
    cursor = pick.at + made.length;
  }
  const result = rawOf(shape);
  if (isMove) {
    tree.delete(sec.path);
    tree.set(sec.moveTo as string, result);
    return okOut({ oldPath: sec.path, newPath: sec.moveTo as string });
  }
  tree.set(sec.path, result);
  return okOut();
}

// ---------------------------------------------------------------------------
// JSON edits (SPEC section 9)
// ---------------------------------------------------------------------------

interface JsonEdit {
  command: 'create' | 'str_replace' | 'insert';
  path: string;
  fileText: string;
  oldStr: string;
  newStr: string;
  insertLine: number;
}

function validateJsonEdit(obj: unknown, lineNo: number): JsonEdit {
  if (obj === null || typeof obj !== 'object' || Array.isArray(obj)) throw new ParseFault(lineNo);
  const rec = obj as Record<string, unknown>;
  if (typeof rec.path !== 'string') throw new ParseFault(lineNo);
  if (rec.command === 'create') {
    if (typeof rec.file_text !== 'string') throw new ParseFault(lineNo);
    return { command: 'create', path: rec.path, fileText: rec.file_text, oldStr: '', newStr: '', insertLine: 0 };
  }
  if (rec.command === 'str_replace') {
    if (typeof rec.old_str !== 'string' || rec.old_str === '') throw new ParseFault(lineNo);
    if (rec.new_str !== undefined && typeof rec.new_str !== 'string') throw new ParseFault(lineNo);
    return { command: 'str_replace', path: rec.path, fileText: '', oldStr: rec.old_str, newStr: (rec.new_str as string | undefined) ?? '', insertLine: 0 };
  }
  if (rec.command === 'insert') {
    if (typeof rec.insert_line !== 'number' || !Number.isInteger(rec.insert_line)) throw new ParseFault(lineNo);
    if (typeof rec.new_str !== 'string') throw new ParseFault(lineNo);
    return { command: 'insert', path: rec.path, fileText: '', oldStr: '', newStr: rec.new_str, insertLine: rec.insert_line };
  }
  throw new ParseFault(lineNo);
}

function parseJson(lines: string[], text: string): JsonEdit[] {
  const firstNonWs = text.replace(/^\s+/, '');
  if (firstNonWs.startsWith('[')) {
    const at = text.indexOf('[');
    const startLine = text.slice(0, at).split('\n').length;
    let parsed: unknown;
    try {
      parsed = JSON.parse(text);
    } catch {
      throw new ParseFault(startLine);
    }
    if (!Array.isArray(parsed)) throw new ParseFault(startLine);
    return parsed.map((el) => validateJsonEdit(el, startLine));
  }
  const edits: JsonEdit[] = [];
  for (let i = 0; i < lines.length; i += 1) {
    if (isBlank(lines[i])) continue;
    let parsed: unknown;
    try {
      parsed = JSON.parse(lines[i]);
    } catch {
      throw new ParseFault(i + 1);
    }
    edits.push(validateJsonEdit(parsed, i + 1));
  }
  return edits;
}

function countOverlapping(hay: string, needle: string): number {
  let count = 0;
  let from = 0;
  for (;;) {
    const at = hay.indexOf(needle, from);
    if (at < 0) return count;
    count += 1;
    from = at + 1;
  }
}

function applyJson(edit: JsonEdit, tree: Tree): ApplyOut {
  const unsafe = checkSafe([edit.path]);
  if (unsafe !== null) return { failure: unsafe, move: null };
  if (edit.command === 'create') {
    if (tree.has(edit.path)) return badOut('exists', edit.path);
    tree.set(edit.path, edit.fileText);
    return okOut();
  }
  if (!tree.has(edit.path)) return badOut('missing', edit.path);
  if (edit.command === 'str_replace') {
    const raw = tree.get(edit.path) as string;
    const shape = shapeOf(raw);
    if (shape.br === '\r\n') {
      const normText = raw.split('\r\n').join('\n');
      const normOld = edit.oldStr.split('\r\n').join('\n');
      const normNew = edit.newStr.split('\r\n').join('\n');
      const hits = countOverlapping(normText, normOld);
      if (hits === 0) return badOut('no-match', edit.path);
      if (hits > 1) return badOut('ambiguous', edit.path);
      const at = normText.indexOf(normOld);
      const done = normText.slice(0, at) + normNew + normText.slice(at + normOld.length);
      tree.set(edit.path, done.split('\n').join('\r\n'));
      return okOut();
    }
    const hits = countOverlapping(raw, edit.oldStr);
    if (hits === 0) return badOut('no-match', edit.path);
    if (hits > 1) return badOut('ambiguous', edit.path);
    const at = raw.indexOf(edit.oldStr);
    tree.set(edit.path, raw.slice(0, at) + edit.newStr + raw.slice(at + edit.oldStr.length));
    return okOut();
  }
  const shape = shapeOf(tree.get(edit.path) as string);
  if (edit.insertLine < 0 || edit.insertLine > shape.lines.length) return badOut('no-match', edit.path);
  const added = splitInserted(edit.newStr);
  shape.lines.splice(edit.insertLine, 0, ...added);
  tree.set(edit.path, rawOf(shape));
  return okOut();
}

// ---------------------------------------------------------------------------
// The tree on disk
// ---------------------------------------------------------------------------

function readTree(dir: string, prefix: string): Tree {
  const out: Tree = new Map();
  for (const name of readdirSync(dir)) {
    const full = join(dir, name);
    const st = statSync(full);
    if (st.isDirectory()) {
      for (const [k, v] of readTree(full, prefix + name + '/')) out.set(k, v);
    } else if (st.isFile()) {
      out.set(prefix + name, readFileSync(full, 'utf8'));
    }
  }
  return out;
}

function writeTree(orig: Tree, next: Tree): void {
  for (const [p, text] of next) {
    if (orig.get(p) === text) continue;
    const full = join(process.cwd(), ...p.split('/'));
    mkdirSync(dirname(full), { recursive: true });
    writeFileSync(full, text, 'utf8');
  }
  for (const p of orig.keys()) {
    if (!next.has(p)) rmSync(join(process.cwd(), ...p.split('/')), { force: true });
  }
}

// ---------------------------------------------------------------------------
// Invocation and output (SPEC sections 1, 2 and 10)
// ---------------------------------------------------------------------------

interface Args {
  format: string;
  check: boolean;
  strict: boolean;
  patch: string | null;
}

function parseArgs(argv: string[]): Args | null {
  let format: string | null = null;
  let check = false;
  let strict = false;
  let seenCheck = false;
  let seenStrict = false;
  let seenFormat = false;
  let positional: string | null = null;
  let positionalCount = 0;
  let afterDashDash = false;
  for (const arg of argv) {
    if (!afterDashDash && arg === '--') {
      afterDashDash = true;
      continue;
    }
    if (!afterDashDash && arg.startsWith('-') && arg !== '-') {
      if (arg === '--check') {
        if (seenCheck) return null;
        seenCheck = true;
        check = true;
      } else if (arg === '--strict') {
        if (seenStrict) return null;
        seenStrict = true;
        strict = true;
      } else if (arg.startsWith('--format=')) {
        if (seenFormat) return null;
        seenFormat = true;
        format = arg.slice('--format='.length);
        if (!['unified', 'search-replace', 'v4a', 'json', 'auto'].includes(format)) return null;
      } else {
        return null;
      }
      continue;
    }
    positionalCount += 1;
    if (positionalCount > 1) return null;
    positional = arg;
  }
  return { format: format ?? 'auto', check, strict, patch: positional };
}

function emit(text: string): void {
  process.stdout.write(text);
}

function runCli(): number {
  const args = parseArgs(process.argv.slice(2));
  if (args === null) {
    emit('error: usage\n');
    return 2;
  }
  let patchText: string;
  if (args.patch === null || args.patch === '-') {
    try {
      patchText = readFileSync(0, 'utf8');
    } catch {
      emit('error: no-patch\n');
      return 2;
    }
  } else {
    try {
      patchText = readFileSync(args.patch, 'utf8');
    } catch {
      emit('error: no-patch\n');
      return 2;
    }
  }
  const lines = splitPatch(patchText);
  const format = args.format === 'auto' ? detectFormat(lines) : args.format;
  if (format === null) {
    emit('error: format\n');
    return 2;
  }
  type AnyEdit = UniSection | SrBlock | V4aSection | JsonEdit;
  let edits: AnyEdit[];
  try {
    if (format === 'unified') edits = parseUnified(lines);
    else if (format === 'search-replace') edits = parseSearchReplace(lines);
    else if (format === 'v4a') edits = parseV4a(lines);
    else edits = parseJson(lines, patchText);
  } catch (err) {
    if (err instanceof ParseFault) {
      emit(`error: parse ${err.lineNo}\n`);
      return 2;
    }
    throw err;
  }
  if (edits.length === 0) {
    emit('error: parse 1\n');
    return 2;
  }
  const before = readTree(process.cwd(), '');
  const working: Tree = new Map(before);
  const failures: EditFailure[] = [];
  const moves: { oldPath: string; newPath: string }[] = [];
  for (const edit of edits) {
    let out: ApplyOut;
    if (format === 'unified') out = applyUnified(edit as UniSection, working, args.strict);
    else if (format === 'search-replace') out = applySearchReplace(edit as SrBlock, working, args.strict);
    else if (format === 'v4a') out = applyV4a(edit as V4aSection, working, args.strict);
    else out = applyJson(edit as JsonEdit, working);
    if (out.failure !== null) failures.push(out.failure);
    else if (out.move !== null) moves.push(out.move);
  }
  if (failures.length > 0) {
    let text = '';
    for (const f of failures) text += `error: ${f.code} ${f.path}\n`;
    text += `failed: ${failures.length} of ${edits.length} edits\n`;
    emit(text);
    return 1;
  }
  if (!args.check) writeTree(before, working);
  const moved: { oldPath: string; newPath: string }[] = [];
  for (const mv of moves) {
    if (before.has(mv.oldPath) && !working.has(mv.oldPath) && !before.has(mv.newPath) && working.has(mv.newPath)) {
      moved.push(mv);
    }
  }
  const movedOld = new Set(moved.map((m) => m.oldPath));
  const movedNew = new Set(moved.map((m) => m.newPath));
  const rows: { key: string; text: string }[] = [];
  const allPaths = new Set([...before.keys(), ...working.keys()]);
  for (const p of allPaths) {
    const was = before.get(p);
    const now = working.get(p);
    if (was === now) continue;
    if (movedOld.has(p) || movedNew.has(p)) continue;
    if (was === undefined) rows.push({ key: p, text: `A ${p}` });
    else if (now === undefined) rows.push({ key: p, text: `D ${p}` });
    else rows.push({ key: p, text: `M ${p}` });
  }
  for (const mv of moved) rows.push({ key: mv.newPath, text: `R ${mv.oldPath} -> ${mv.newPath}` });
  rows.sort((a, b) => byteOrder(a.key, b.key));
  let text = '';
  for (const row of rows) text += `${row.text}\n`;
  text += rows.length === 1 ? 'ok: 1 file\n' : `ok: ${rows.length} files\n`;
  emit(text);
  return 0;
}

// A trial hands over to the runner beside this file when the trial env is
// set; otherwise this file is the mend command line tool.
if (process.env.MAKEFUN_ENV_URL !== undefined) {
  import('./runner.ts').then((m) => m.runTrial(process.env.MAKEFUN_ENV_URL as string));
} else {
  process.exitCode = runCli();
}
