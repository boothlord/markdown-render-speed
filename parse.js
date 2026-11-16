// parse.js — an original, dependency-free Markdown renderer.
//
// parse(markdown) returns the HTML that marked 18.1.3 renders for the same
// input with its default options (gfm: true, breaks: false, pedantic: false).
//
// Architecture: a single pass over the source by index. The block tokenizer
// walks the document with a cursor and never re-slices the remaining input;
// anchored grammar patterns are compiled as sticky regexes and executed
// against the whole string at the cursor, so a match attempt costs the same
// at the end of a document as at the start. Inline tokenizing likewise walks
// its string by index, with delimiter-run matching for emphasis on a masked
// copy of the text. Tokens are rendered in a final walk.
//
// No state is kept between calls: every call builds a fresh lexer, so parse
// is deterministic and reentrant.

// ---------------------------------------------------------------------------
// Small string helpers
// ---------------------------------------------------------------------------

const ESCAPE_MAP = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
const ESCAPE_REPLACE = /[&<>"']/g;
const ESCAPE_REPLACE_NOENCODE = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

function escapeChar(c) {
  return ESCAPE_MAP[c];
}

/** Escape HTML specials. With encode, existing entities are escaped too. */
const ESCAPE_TEST = /[<>&"']/;
function escapeHtml(text, encode) {
  // Most rendered text has nothing to escape; a plain class test scans
  // faster than the replacement patterns (one carries a lookahead).
  if (!ESCAPE_TEST.test(text)) return text;
  return encode ? text.replace(ESCAPE_REPLACE, escapeChar) : text.replace(ESCAPE_REPLACE_NOENCODE, escapeChar);
}

const NUMERIC_REF_TEST = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const NUMERIC_REF_OR_AMP = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

/** Resolve numeric character references in a text run; a bare & becomes &amp;. */
function decodeCharRefs(text) {
  if (!text.includes('&#')) return text;
  if (!NUMERIC_REF_TEST.test(text)) return text;
  return text.replace(NUMERIC_REF_OR_AMP, (match, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const cp = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (cp === 0 || cp > 0x10FFFF || (cp >= 0xD800 && cp <= 0xDFFF)) return '\uFFFD';
    if (cp === 38) return '&amp;';
    return String.fromCodePoint(cp);
  });
}

/** encodeURI a link destination the way the reference does; null if it throws. */
function cleanUrl(href) {
  try {
    const enc = encodeURI(href);
    return enc.includes('%') ? enc.replace(/%25/g, '%') : enc;
  } catch {
    return null;
  }
}

/** Remove trailing copies of `ch` (or, with invert, trailing non-`ch` chars). */
function trimEndChar(text, ch, invert) {
  const n = text.length;
  if (n === 0) return '';
  let count = 0;
  while (count < n) {
    const r = text.charAt(n - count - 1);
    if (r === ch && !invert) count++;
    else if (r !== ch && invert) count++;
    else break;
  }
  return text.slice(0, n - count);
}

const BLANK_LINE = /^[ \t]*$/;

/** Drop trailing blank lines, keeping at most the shape the reference keeps. */
function trimBlankEnd(text) {
  const lines = text.split('\n');
  let last = lines.length - 1;
  while (last >= 0 && BLANK_LINE.test(lines[last])) last--;
  return lines.length - last <= 2 ? text : lines.slice(0, last + 1).join('\n');
}

/** Expand tabs to spaces, tab stops every 4 columns from `startCol`. */
function expandTabs(text, startCol = 0) {
  if (!text.includes('\t')) return text;
  let col = startCol;
  let out = '';
  for (const ch of text) {
    if (ch === '\t') {
      const width = 4 - (col % 4);
      out += ' '.repeat(width);
      col += width;
    } else {
      out += ch;
      col++;
    }
  }
  return out;
}

/**
 * Scan `text` for the closing char of a bracket pair, skipping \-escapes.
 * Returns -1 when balanced or absent, -2 when an opener is left unclosed,
 * or the index of a closer that closes too much.
 */
function findClosingBracket(text, pair) {
  if (text.indexOf(pair[0]) === -1 && text.indexOf(pair[1]) === -1) return -1;
  let depth = 0;
  for (let i = 0; i < text.length; i++) {
    if (text[i] === '\\') i++;
    else if (text[i] === pair[0]) depth++;
    else if (text[i] === pair[1] && --depth < 0) return i;
  }
  return depth > 0 ? -2 : -1;
}

/** Whether a string ends with a blank line: \n, spaces/tabs, \n, spaces/tabs. */
function endsWithBlankLine(s) {
  let i = s.length - 1;
  while (i >= 0 && (s[i] === ' ' || s[i] === '\t')) i--;
  if (i < 0 || s[i] !== '\n') return false;
  i--;
  while (i >= 0 && (s[i] === ' ' || s[i] === '\t')) i--;
  return i >= 0 && s[i] === '\n';
}

/** Index of the first character that is not a space (or the string length). */
function firstNonSpace(s) {
  let i = 0;
  while (s[i] === ' ') i++;
  return i;
}

/**
 * Index of the first non-space character when every tab counts as 4 spaces
 * (the position a /\t/g -> '    ' replacement would report).
 */
function firstNonSpaceTabs4(s) {
  let col = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if (c === ' ') col++;
    else if (c === '\t') col += 4;
    else return col;
  }
  return -1;
}

/**
 * Whether any of the list continuation probes could match a line: they all
 * need a construct character within the first `level` spaces.
 */
function probeMayMatch(line, level) {
  let f = 0;
  while (line[f] === ' ') f++;
  if (f > level) return false;
  const c = line[f];
  return (
    c === '`' || c === '~' || c === '#' || c === '<' || c === '>' ||
    c === '*' || c === '+' || c === '-' || c === '_' ||
    (c >= '0' && c <= '9')
  );
}

/** The first line of a string (without splitting the whole string). */
function firstLine(text) {
  const nl = text.indexOf('\n');
  return nl === -1 ? text : text.slice(0, nl);
}

/** End index (of the '\n' or of the string) of the line starting at `pos`. */
function lineEnd(s, pos) {
  const nl = s.indexOf('\n', pos);
  return nl === -1 ? s.length : nl;
}

/** The line starting at `pos`, as a string. */
function lineSlice(s, pos) {
  return s.slice(pos, lineEnd(s, pos));
}

/** Execute a sticky regex anchored exactly at `pos`. */
function execAt(re, s, pos) {
  re.lastIndex = pos;
  return re.exec(s);
}

/** Whether a sticky regex matches anchored exactly at `pos`. */
function testAt(re, s, pos) {
  re.lastIndex = pos;
  return re.exec(s) !== null;
}

/** Normalize a link reference label for use as a dictionary key. */
function normalizeLabel(label) {
  return label.trim().replace(/\s+/g, ' ').toLowerCase().toUpperCase().toLowerCase();
}

/** Split a table row into cells, honouring \| escapes, padding to `count`. */
function splitRow(row, count) {
  // Without backslashes every pipe is a plain separator: the mark-up
  // transform below and splitting on ' |' reduce to splitting on '|',
  // and the per-cell unescape is the identity.
  const noEscapes = !row.includes('\\');
  let cells;
  if (noEscapes) {
    cells = row.split('|');
  } else {
    const markedUp = row.replace(/\|/g, (match, offset, str) => {
      let escaped = false;
      let p = offset;
      while (--p >= 0 && str[p] === '\\') escaped = !escaped;
      return escaped ? '|' : ' |';
    });
    cells = markedUp.split(/ \|/);
  }
  if (!cells[0].trim()) cells.shift();
  if (cells.length > 0 && !cells[cells.length - 1].trim()) cells.pop();
  if (count) {
    if (cells.length > count) cells.splice(count);
    else while (cells.length < count) cells.push('');
  }
  for (let i = 0; i < cells.length; i++) {
    cells[i] = noEscapes ? cells[i].trim() : cells[i].trim().replace(/\\\|/g, '|');
  }
  return cells;
}

// ---------------------------------------------------------------------------
// Grammar constants shared by several rules
// ---------------------------------------------------------------------------

const OTHER = {
  codeRemoveIndent: /^(?: {0,3}\t| {1,4})/gm,
  outputLinkReplace: /\\([\[\]])/g,
  indentCodeCompensation: /^(\s+)(?:```)/,
  beginningSpace: /^\s+/,
  endingHash: /#$/,
  endingSpaceTabChar: /[ \t]$/,
  nonSpaceChar: /[^ ]/,
  leadingSpaceTab: /^[ \t]+/,
  blankLine: BLANK_LINE,
  doubleBlankLine: /\n[ \t]*\n[ \t]*$/,
  blockquoteStart: /^ {0,3}>/,
  blockquoteSetextReplace: /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g,
  blockquoteSetextReplace2: /^ {0,3}>[ \t]?/gm,
  blockquoteMarkerWhitespace: /^( {0,3}>)([ \t]+)/gm,
  listReplaceNesting: /^ {1,4}(?=( {4})*[^ ])/g,
  listIsTask: /^\[[ xX]\][ \t]+\S/,
  listReplaceTask: /^\[[ xX]\][ \t]+/,
  listTaskCheckbox: /\[[ xX]\]/,
  anyLine: /\n.*\n/,
  hrefBrackets: /^<(.*)>$/,
  tableDelimiter: /[:|]/,
  tableAlignChars: /^\||\| *$/g,
  tableRowBlankLine: /\n[ \t]*$/,
  tableAlignRight: /^ *-+: *$/,
  tableAlignCenter: /^ *:-+: *$/,
  tableAlignLeft: /^ *:-+ *$/,
  startATag: /^<a /i,
  endATag: /^<\/a>/i,
  startPreScriptTag: /^<(pre|code|kbd|script)(\s|>)/i,
  endPreScriptTag: /^<\/(pre|code|kbd|script)(\s|>)/i,
  startAngleBracket: /^</,
  endAngleBracket: />$/,
  unicodeAlphaNumeric: /[\p{L}\p{N}]/u,
};

// Indent-parameterised "does the next construct start here" probes used by
// the list tokenizer, as hand-written line checks. Each takes a line (no
// trailing newline) and the level clamped to 0..3 from (indent - 1).
function clampedLevel(indent) {
  return Math.max(0, Math.min(3, indent - 1));
}
function listItemRegex(bullet) {
  return new RegExp(`( {0,3}${bullet})((?:[ \\t][^\\n]*)?(?:\\n|$))`, 'y');
}

/** Index of the first non-space char, or -1 when there are > level spaces. */
function probeStart(line, level) {
  let f = 0;
  while (line[f] === ' ') f++;
  return f <= level ? f : -1;
}

function probeNextBullet(line, level) {
  const f = probeStart(line, level);
  if (f < 0) return false;
  const c = line[f];
  if (c === '*' || c === '+' || c === '-') {
    const nx = line[f + 1];
    return nx === undefined || nx === ' ' || nx === '\t';
  }
  if (c >= '0' && c <= '9') {
    let d = 0;
    while (line[f + d] >= '0' && line[f + d] <= '9') d++;
    if (d > 9) return false;
    const term = line[f + d];
    if (term !== '.' && term !== ')') return false;
    const nx = line[f + d + 1];
    return nx === undefined || nx === ' ' || nx === '\t';
  }
  return false;
}

/** Whether s[i..end) is an hr body: >= 3 copies of one of - _ *, spaces aside. */
function hrRun(s, i, end) {
  const c = s[i];
  if (c !== '-' && c !== '_' && c !== '*') return false;
  let count = 0;
  while (i < end) {
    const ch = s[i];
    if (ch === c) count++;
    else if (ch !== ' ' && ch !== '\t') return false;
    i++;
  }
  return count >= 3;
}

function probeHr(line, level) {
  const f = probeStart(line, level);
  return f >= 0 && hrRun(line, f, line.length);
}

function probeFence(line, level) {
  const f = probeStart(line, level);
  if (f < 0) return false;
  const c = line[f];
  return (c === '`' || c === '~') && line[f + 1] === c && line[f + 2] === c;
}

function probeHeading(line, level) {
  const f = probeStart(line, level);
  if (f < 0) return false;
  let d = 0;
  while (line[f + d] === '#') d++;
  if (d < 1 || d > 6) return false;
  const nx = line[f + d];
  return nx === undefined || isWsCode(line.charCodeAt(f + d));
}

function probeBlockquote(line, level) {
  const f = probeStart(line, level);
  return f >= 0 && line[f] === '>';
}

const BLOCK_TAGS = new Set(['address', 'article', 'aside', 'base', 'basefont', 'blockquote', 'body', 'caption', 'center', 'col', 'colgroup', 'dd', 'details', 'dialog', 'dir', 'div', 'dl', 'dt', 'fieldset', 'figcaption', 'figure', 'footer', 'form', 'frame', 'frameset', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'head', 'header', 'hr', 'html', 'iframe', 'legend', 'li', 'link', 'main', 'menu', 'menuitem', 'meta', 'nav', 'noframes', 'ol', 'optgroup', 'option', 'p', 'param', 'search', 'section', 'summary', 'table', 'tbody', 'td', 'tfoot', 'th', 'thead', 'title', 'tr', 'track', 'ul']);
const RAW_TAGS = new Set(['script', 'pre', 'style', 'textarea']);

function probeHtml(line, level) {
  const f = probeStart(line, level);
  if (f < 0 || line[f] !== '<') return false;
  if (line.startsWith('<!--', f)) return true;
  const c1 = line[f + 1];
  if (c1 === '?') return true;
  if (c1 === '!') {
    if (line.startsWith('<![CDATA[', f)) return true;
    const c2 = line.charCodeAt(f + 2);
    return (c2 >= 65 && c2 <= 90) || (c2 >= 97 && c2 <= 122);
  }
  let q = f + 1;
  let closing = false;
  if (line[q] === '/') {
    closing = true;
    q++;
  }
  let e = q;
  while (e < line.length) {
    const cc = line.charCodeAt(e);
    if ((cc >= 65 && cc <= 90) || (cc >= 97 && cc <= 122) || (cc >= 48 && cc <= 57)) e++;
    else break;
  }
  if (e === q) return false;
  const name = line.slice(q, e).toLowerCase();
  const nx = line[e];
  if (!closing && RAW_TAGS.has(name)) {
    return nx === undefined || nx === '>' || isWsCode(line.charCodeAt(e));
  }
  if (!BLOCK_TAGS.has(name)) return false;
  if (nx === undefined || nx === ' ' || nx === '>') return true;
  return nx === '/' && line[e + 1] === '>';
}

// All six "next construct" probes for one list indent level, cached together.
const probesCache = new Map();
function listProbes(indent) {
  let probes = probesCache.get(indent);
  if (!probes) {
    const level = clampedLevel(indent);
    probes = {
      nb: (line) => probeNextBullet(line, level),
      hr: (line) => probeHr(line, level),
      fence: (line) => probeFence(line, level),
      head: (line) => probeHeading(line, level),
      html: (line) => probeHtml(line, level),
      bq: (line) => probeBlockquote(line, level),
    };
    probesCache.set(indent, probes);
  }
  return probes;
}

// ---------------------------------------------------------------------------
// Block grammar (GFM rule set), as sticky patterns matched at a cursor.
// Each is the anchored form of the grammar rule with the leading ^ removed;
// the sticky flag supplies the anchor. End-of-input assertions keep their
// meaning because the cursor string is the whole remaining document.
// ---------------------------------------------------------------------------

const BLOCK = {
  code: /((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/y,
  fences: / {0,3}(`{3,}(?=[^`\n]*(?:\n|$))|~{3,})([^\n]*)(?:\n|$)(?:|([\s\S]*?)(?:\n|$))(?: {0,3}(?:(?=`)\1`*|(?=~)\1~*) *(?=\n|$)|$)/y,
  heading: / {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/y,
  hr: / {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/y,
  blockquote: /( {0,3}> ?(?:(?![ \t]*(?:\n|$))(([^\n]+(?:\n(?! {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)| {0,3}#{1,6}(?:\s|$)| {0,3}>| {0,3}(?:`{3,}(?=[^`\n]*(?:\n|$))|~~~)[^\n]*(?:\n|$)| {0,3}(?:[*+-]|\d{1,9}[.)])(?:[ \t]|\n|$)| {0,3}(?:<\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\n|\/?>)|<(?:(?:script|pre|style|textarea)(?:[\s>]|$)|!--)|<\?|<![A-Za-z]|<!\[CDATA\[)|[ \t]+\n)[^\n]+)*))|[^\n]*)(?:\n|$))+/y,
  list: /( {0,3}(?:[*+-]|\d{1,9}[.)]))([ \t][^\n]*?)?(?:\n|$)/y,
  html: / {0,3}(?:<(script|pre|style|textarea)[\s>][\s\S]*?(?:<\/\1>[^\n]*\n*|$)|<!--(?:-?>|[\s\S]*?(?:-->|$))[^\n]*(\n+|$)|<\?[\s\S]*?(?:\?>[^\n]*\n*|$)|<![A-Z][\s\S]*?(?:>[^\n]*\n*|$)|<!\[CDATA\[[\s\S]*?(?:\]\]>[^\n]*\n*|$)|<\/?(address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?:[ \t]+|\n|\/?>|$)[\s\S]*?(?:(?:\n[ \t]*)+\n|$)|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?: +[a-zA-Z:_][\w.:-]*(?: *= *"[^"\n]*"| *= *'[^'\n]*'| *= *[^\s"'=<>`]+)?)*? *\/?>(?=[ \t]*(?:\n|$))[\s\S]*?(?:(?:\n[ \t]*)+\n|$)|<\/[a-z][a-z0-9-]*\s*>(?=[ \t]*(?:\n|$))[\s\S]*?(?:(?:\n[ \t]*)+\n|$))/iy,
  def: / {0,3}\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+)\]: *(?:\n[ \t]*)?([^<\s][^\s]*|<.*?>)(?:(?: +(?:\n[ \t]*)?| *\n[ \t]*)((?:"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\\n]|\n(?!\n))*'|\((?:\\[\s\S]|[^()\\])*\))))? *(?:\n+|$)/y,
  table: / *([^\n ].*)\n {0,3}((?:\| *)?:?-+:? *(?:\| *:?-+:? *)*(?:\| *)?)(?:\n((?:(?! *\n| {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)| {0,3}#{1,6}(?:\s|$)| {0,3}>|(?: {4}| {0,3}\t)[^\n]| {0,3}(?:`{3,}(?=[^`\n]*(?:\n|$))|~~~)[^\n]*(?:\n|$)| {0,3}(?:[*+-]|1[.)])[ \t]| {0,3}(?:<\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\n|\/?>)|<(?:(?:script|pre|style|textarea)(?:[\s>]|$)|!--)|<\?|<![A-Za-z]|<!\[CDATA\[)).*(?:\n|$))*)\n*|$)/y,
  lheading: /(?! {0,3}(?:[*+-]|\d{1,9}[.)]) |(?: {4}| {0,3}\t)| {0,3}(?:`{3,}|~{3,})| {0,3}>| {0,3}#{1,6}(?:\s|$)| {0,3}<[^\n>]+>\n| {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n)((?:.|\n(?!\s*?\n| {0,3}(?:[*+-]|\d{1,9}[.)]) | {0,3}(?:`{3,}|~{3,})| {0,3}>| {0,3}#{1,6}(?:\s|$)| {0,3}(?:(?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)| {0,3}<[^\n>]+>\n| {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n))+?)\n {0,3}(=+|-+)[ \t]*(?:\n+|$)/y,
};

// Plain (non-sticky) twins of two sticky patterns, for the spots that test a
// pattern against a freshly built string rather than at a cursor.
const LHEADING_PLAIN = /^(?! {0,3}(?:[*+-]|\d{1,9}[.)]) |(?: {4}| {0,3}\t)| {0,3}(?:`{3,}|~{3,})| {0,3}>| {0,3}#{1,6}(?:\s|$)| {0,3}<[^\n>]+>\n| {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n)((?:.|\n(?!\s*?\n| {0,3}(?:[*+-]|\d{1,9}[.)]) | {0,3}(?:`{3,}|~{3,})| {0,3}>| {0,3}#{1,6}(?:\s|$)| {0,3}(?:(?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)| {0,3}<[^\n>]+>\n| {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n))+?)\n {0,3}(=+|-+)[ \t]*(?:\n+|$)/;

// ---------------------------------------------------------------------------
// Inline grammar (GFM rule set), sticky at the cursor like the block rules.
// ---------------------------------------------------------------------------

const INLINE = {
  code: /(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/y,
  tag: /<!--(?:-?>|[\s\S]*?-->)|<\/[a-zA-Z][a-zA-Z0-9-]*\s*>|<[a-zA-Z][a-zA-Z0-9-]*(?:\s+[a-zA-Z:_][\w.:-]*(?:\s*=\s*"[^"]*"|\s*=\s*'[^']*'|\s*=\s*[^\s"'=<>`]+)?)*?\s*\/?>|<\?[\s\S]*?\?>|<![a-zA-Z]+\s[\s\S]*?>|<!\[CDATA\[[\s\S]*?\]\]>/y,
  link: /!?\[((?:\[(?:\[(?:\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\])|[^\[\]\\`])*?)\]\([ \t\n]*(<(?:\\.|[^\n<>\\])+>|[^ \t\n\x00-\x1f]+|(?=\)))(?:(?:[ \t]+(?:\n[ \t]*)?|\n[ \t]*)("(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\])*'|\((?:\\[\s\S]|[^)\\])*\)))?[ \t\n]*\)/y,
  reflink: /!?\[((?:\[(?:\[(?:\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\])|[^\[\]\\`])*?)\]\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+)\]/y,
  nolink: /!?\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+)\](?:\[\])?/y,
  reflinkSearch: /!?\[((?:[^\[\]\\`]*(?:\[(?:\[(?:\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\]))){0,999}?[^\[\]\\`]*?)\]\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\]){1,999})\]|!?\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\]){1,999})\](?:\[\])?(?!\()/g,
  blockSkip: /\[(?:[^\[\]`]|(?<a>`+)[^`]+\k<a>(?!`))*?\]\((?:\\[\s\S]|[^\\\(\)]|\((?:\\[\s\S]|[^\\\(\)])*\))*\)|(?<!`)()(?<b>`+)[^`]+\k<b>(?!`)|<(?! )[^<>]*?>/g,
  anyPunctuation: /\\([\p{P}\p{S}])/gu,
  anyPunctuationOutsideCode: /(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\([\p{P}\p{S}])/gu,
  punctuation: /^((?![*_])[\s\p{P}\p{S}])/u,
  emStrongLDelim: /(?:\*+(?:((?!\*)(?!~)[\p{P}\p{S}])|([^\s*]))?)|_+(?:((?!_)(?!~)[\p{P}\p{S}])|([^\s_]))?/uy,
  emStrongRDelimAstA: /[^_*]*?__[^_*]*?\*[^_*]*?(?=__)/y,
  emStrongRDelimAst: /[^*]+(?=[^*])|(?!\*)(?!~)[\p{P}\p{S}](\*+)(?=[\s]|$)|(?:[^\s\p{P}\p{S}]|~)(\*+)(?!\*)(?=(?!~)[\s\p{P}\p{S}]|$)|(?!\*)(?!~)[\s\p{P}\p{S}](\*+)(?=(?:[^\s\p{P}\p{S}]|~))|[\s](\*+)(?!\*)(?=(?!~)[\p{P}\p{S}])|(?!\*)(?!~)[\p{P}\p{S}](\*+)(?!\*)(?=(?!~)[\p{P}\p{S}])|(?:[^\s\p{P}\p{S}]|~)(\*+)(?=(?:[^\s\p{P}\p{S}]|~))/gu,
  emStrongRDelimUndA: /[^_*]*?\*\*[^_*]*?_[^_*]*?(?=\*\*)/y,
  emStrongRDelimUnd: /[^_]+(?=[^_])|(?!_)[\p{P}\p{S}](_+)(?=[\s]|$)|[^\s\p{P}\p{S}](_+)(?!_)(?=[\s\p{P}\p{S}]|$)|(?!_)[\s\p{P}\p{S}](_+)(?=[^\s\p{P}\p{S}])|[\s](_+)(?!_)(?=[\p{P}\p{S}])|(?!_)[\p{P}\p{S}](_+)(?!_)(?=[\p{P}\p{S}])/gu,
  delLDelim: /~~?(?:((?!~)[\p{P}\p{S}])|[^\s~])/uy,
  delRDelimA: /[^~]+(?=[^~])/y,
  delRDelim: /(?!~)[\p{P}\p{S}](~~?)(?=[\s]|$)|[^\s\p{P}\p{S}](~~?)(?!~)(?=[\s\p{P}\p{S}]|$)|(?!~)[\s\p{P}\p{S}](~~?)(?=[^\s\p{P}\p{S}])|[\s](~~?)(?!~)(?=[\p{P}\p{S}])|(?!~)[\p{P}\p{S}](~~?)(?!~)(?=[\p{P}\p{S}])|[^\s\p{P}\p{S}](~~?)(?=[^\s\p{P}\p{S}])/gu,
  autolink: /<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\s\x00-\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>/y,
  url: /(?:mailto:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])|xmpp:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])(?:\/[A-Za-z0-9@.]+)?)|((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\/\/|www\.)(?:[a-zA-Z0-9\-]+\.?)+[^\s<]*|[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])/y,
  backpedal: /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/,
};

// Plain twin of the link pattern for linkInText's test() on candidate strings.
const LINK_PLAIN = /^!?\[((?:\[(?:\[(?:\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\])|[^\[\]\\`])*?)\]\([ \t\n]*(<(?:\\.|[^\n<>\\])+>|[^ \t\n\x00-\x1f]+|(?=\)))(?:(?:[ \t]+(?:\n[ \t]*)?|\n[ \t]*)("(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\])*'|\((?:\\[\s\S]|[^)\\])*\)))?[ \t\n]*\)/;

// ---------------------------------------------------------------------------
// Inline layer
//
// Inline tokenizing runs after the block pass: block tokenizers queue their
// text, and the queue is drained in order once every link definition in the
// document has been registered. Emphasis and strikethrough matching works on
// a masked copy of the text (same length) where link destinations, code spans
// and escaped punctuation are blanked out, so delimiter runs inside them are
// invisible to the matcher. Tokenizers take the string and a cursor and
// return a token whose `raw` is the exact slice consumed.
// ---------------------------------------------------------------------------

/** Length in code units of the first code point of a string. */
function firstCpLen(s) {
  const c = s.charCodeAt(0);
  return c >= 0xD800 && c <= 0xDBFF && s.charCodeAt(1) >= 0xDC00 && s.charCodeAt(1) <= 0xDFFF ? 2 : 1;
}

/**
 * For a delimiter-opener match (a run of one delimiter char plus one more
 * char), the run length in code points: the match's code point count minus
 * one, computed without spreading the string.
 */
function openerRunLength(match) {
  const units = match.length;
  const last = match.charCodeAt(units - 1);
  if (last >= 0xDC00 && last <= 0xDFFF && units >= 2) {
    const prev = match.charCodeAt(units - 2);
    if (prev >= 0xD800 && prev <= 0xDBFF) return units - 2;
  }
  return units - 1;
}

/** The code point just before `index` in a string, as a string. */
function prevCodePoint(s, index) {
  if (index === 0) return '';
  const c1 = s.charCodeAt(index - 1);
  if (c1 >= 0xDC00 && c1 <= 0xDFFF && index >= 2) {
    const c0 = s.charCodeAt(index - 2);
    if (c0 >= 0xD800 && c0 <= 0xDBFF) return s.slice(index - 2, index);
  }
  return s[index - 1];
}

/** Scan a masked string for the last index each delimiter can close at. */
// ASCII members of \p{P} \cup  \p{S}: the punctuation/symbol ranges.
const ASCII_PS = new Uint8Array(128);
for (const [lo, hi] of [[33, 47], [58, 64], [91, 96], [123, 126]]) {
  for (let c = lo; c <= hi; c++) ASCII_PS[c] = 1;
}

/** The punctuation test for a single-code-point string: [\s\p{P}\p{S}]
 *  but never * or _. ASCII fast path, regex otherwise. */
function isPunctStr(ch) {
  if (ch.length === 1) {
    const c = ch.charCodeAt(0);
    if (c < 128) {
      if (c === 42 || c === 95) return false;
      if (c === 32 || (c >= 9 && c <= 13)) return true;
      return ASCII_PS[c] === 1;
    }
  }
  return INLINE.punctuation.test(ch);
}

/** \p{L} or \p{N} for a single-code-point string, ASCII fast path. */
function isAlphaNumStr(ch) {
  if (ch.length === 1) {
    const c = ch.charCodeAt(0);
    if (c < 128) return isAlnumCode(c);
  }
  return OTHER.unicodeAlphaNumeric.test(ch);
}

function scanDelimRuns(masked) {
  const lastEm = { '*': -1, '_': -1 };
  let lastDel = -1;
  const n = masked.length;
  for (let s = 0; s < n; s++) {
    const r = masked.charCodeAt(s);
    if (r !== 42 && r !== 95 && r !== 126) continue;
    const before = s === 0 ? 10 : masked.charCodeAt(s - 1);
    let i = s + 1;
    while (i < n && masked.charCodeAt(i) === r) i++;
    if (before !== 32 && before !== 9 && before !== 10 && before !== 13 && before !== 12) {
      if (r === 126) lastDel = s;
      else lastEm[r === 42 ? '*' : '_'] = s;
    }
    s = i - 1;
  }
  return { maskedSrc: masked, lastEm, lastDel };
}

function lastEmCloser(lx, masked, ch) {
  const top = lx.maskStack[lx.maskStack.length - 1];
  return top && top.maskedSrc === masked ? top.lastEm[ch] : scanDelimRuns(masked).lastEm[ch];
}

function lastDelCloser(lx, masked) {
  const top = lx.maskStack[lx.maskStack.length - 1];
  return top && top.maskedSrc === masked ? top.lastDel : scanDelimRuns(masked).lastDel;
}

/** Does this text contain a complete inline link (not just a reference)? */
function linkInText(lx, text) {
  if (!text.includes('[')) return false;
  for (const m of text.matchAll(INLINE.blockSkip)) {
    if (LINK_PLAIN.test(m[0]) && text.charAt(m.index - 1) !== '!') return true;
  }
  for (const m of text.matchAll(INLINE.reflinkSearch)) {
    const s = m[0];
    const r = s.lastIndexOf('[');
    if (
      !(s.charAt(0) === '!' || !Object.hasOwn(lx.links, normalizeLabel(s.slice(r + 1, -1)))) &&
      !(r > 1 && linkInText(lx, s.slice(1, r - 1)))
    ) {
      return true;
    }
  }
  return false;
}

/** Build the masked copy of a text used for emphasis/delimiter matching. */
function maskForEm(lx, src) {
  let t = src;
  if (src.includes('[') && lx.linkCount > 0) {
    const blankRef = (match) => {
      const open = match.lastIndexOf('[');
      if (!Object.hasOwn(lx.links, normalizeLabel(match.slice(open + 1, -1)))) return match;
      if (open > 1 && match.charAt(0) !== '!') {
        const inner = match.slice(1, open - 1);
        if (linkInText(lx, inner)) {
          return '[' + inner.replace(INLINE.reflinkSearch, blankRef) + '][' + 'a'.repeat(match.length - open - 2) + ']';
        }
      }
      return '[' + 'a'.repeat(match.length - 2) + ']';
    };
    t = t.replace(INLINE.reflinkSearch, blankRef);
  }
  if (t.includes('`') || t.includes('\\')) {
    t = t.replace(INLINE.anyPunctuationOutsideCode, (match, codeRun, punct) => {
      if (punct) return '+'.repeat(match.length);
      if (!codeRun) return match;
      const inner = match.slice(codeRun.length, -codeRun.length);
      return codeRun + (inner.includes('`') ? inner.replace(/`/g, '+') : inner) + codeRun;
    });
  }
  if (t.includes('[') || t.includes('`') || t.includes('<')) {
    t = t.replace(INLINE.blockSkip, (match, g1, g2) => {
      const keep = g2 ? g2.length : 0;
      return match.slice(0, keep) + '[' + 'a'.repeat(match.length - keep - 2) + ']';
    });
  }
  return t;
}

/** True when a link label holds a tag/autolink that runs past the label end. */
function labelHasOpenTag(src, label, offset) {
  if (!label.includes('<')) return false;
  for (let s = 0; s < label.length; s++) {
    if (label[s] === '\\') {
      s++;
      continue;
    }
    if (label[s] === '`') {
      const m = execAt(INLINE.code, label, s);
      if (m) {
        s += m[0].length - 1;
        continue;
      }
    }
    if (label[s] !== '<') continue;
    const m = execAt(INLINE.tag, src, offset + s) || execAt(INLINE.autolink, src, offset + s);
    if (m) {
      if (m[0].length > label.length - s) return true;
      s += m[0].length - 1;
    }
  }
  return false;
}

/** Shared tail of link/image construction: tokenize the label, guard nesting. */
function buildLink(lx, cap, dest, raw) {
  const href = dest.href;
  const title = dest.title || null;
  const text = cap[1].replace(OTHER.outputLinkReplace, '$1');
  const isImage = cap[0].charAt(0) === '!';
  const st = lx.state;
  const prevInLink = st.inLink;
  const prevEmitted = st.linkEmitted;
  const prevRawBlock = st.inRawBlock;
  st.inLink = true;
  st.linkEmitted = false;
  const tokens = inlineTokens(lx, text, []);
  const emitted = st.linkEmitted;
  st.linkEmitted = prevEmitted;
  st.inLink = prevInLink;
  if (!isImage) {
    if (emitted) {
      st.inRawBlock = prevRawBlock;
      return undefined;
    }
    st.linkEmitted = true;
  }
  return { type: isImage ? 'image' : 'link', raw, href, title, text, tokens };
}

function tokEscape(lx, s, i) {
  // INLINE.escape by hand: a backslash plus one ASCII punctuation character.
  if (ESCAPABLE[s.charCodeAt(i + 1)] === 1) {
    return { type: 'escape', raw: s.slice(i, i + 2), text: s[i + 1] };
  }
  return undefined;
}

// Characters a backslash can escape: !"#$%&'()*+,-./:;<=>?@[\]^_`{|}~
const ESCAPABLE = new Uint8Array(128);
for (const ch of '!"#$%&\'()*+,-./:;<=>?@[\\]^_`{|}~') ESCAPABLE[ch.charCodeAt(0)] = 1;

function tokTag(lx, s, i) {
  const cap = execAt(INLINE.tag, s, i);
  if (!cap) return undefined;
  const st = lx.state;
  if (!st.inLink && OTHER.startATag.test(cap[0])) st.inLink = true;
  else if (st.inLink && OTHER.endATag.test(cap[0])) st.inLink = false;
  if (!st.inRawBlock && OTHER.startPreScriptTag.test(cap[0])) st.inRawBlock = true;
  else if (st.inRawBlock && OTHER.endPreScriptTag.test(cap[0])) st.inRawBlock = false;
  return { type: 'html', raw: cap[0], inLink: st.inLink, inRawBlock: st.inRawBlock, block: false, text: cap[0] };
}

function tokLink(lx, s, i) {
  if (lx.state.linkParenPossible === false) return undefined;
  const cap = execAt(INLINE.link, s, i);
  if (!cap) return undefined;
  const labelOffset = cap[0].charAt(0) === '!' ? 2 : 1;
  if (labelHasOpenTag(s, cap[1], i + labelOffset)) return undefined;
  const href = cap[2].trim();
  if (OTHER.startAngleBracket.test(href)) {
    if (!OTHER.endAngleBracket.test(href)) return undefined;
    const stripped = trimEndChar(href.slice(0, -1), '\\');
    if ((href.length - stripped.length) % 2 === 0) return undefined;
  } else {
    const close = findClosingBracket(cap[2], '()');
    if (close === -2) return undefined;
    if (close > -1) {
      const end = (cap[0].indexOf('!') === 0 ? 5 : 4) + cap[1].length + close;
      cap[2] = cap[2].substring(0, close);
      cap[0] = cap[0].substring(0, end).trim();
      cap[3] = '';
    }
  }
  const beforeFinal = trimEndChar(cap[0].slice(0, -1), '\\');
  if ((cap[0].length - beforeFinal.length) % 2 === 0) return undefined;
  let dest = cap[2].trim();
  const title = cap[3] ? cap[3].slice(1, -1) : '';
  if (OTHER.startAngleBracket.test(dest)) dest = dest.slice(1, -1);
  return buildLink(lx, cap, {
    href: dest && dest.replace(INLINE.anyPunctuation, '$1'),
    title: title && title.replace(INLINE.anyPunctuation, '$1'),
  }, cap[0]);
}

function tokReflink(lx, s, i) {
  let cap;
  if ((cap = execAt(INLINE.reflink, s, i)) || (cap = execAt(INLINE.nolink, s, i))) {
    const labelOffset = cap[0].charAt(0) === '!' ? 2 : 1;
    if (labelHasOpenTag(s, cap[1], i + labelOffset)) return undefined;
    const def = lx.links[normalizeLabel(cap[2] || cap[1])];
    if (!def) {
      const first = cap[0].charAt(0);
      return { type: 'text', raw: first, text: first };
    }
    return buildLink(lx, cap, def, cap[0]);
  }
  return undefined;
}

function tokEmStrong(lx, s, i, masked, prevChar) {
  const cap = execAt(INLINE.emStrongLDelim, s, i);
  if (!cap || (!cap[1] && !cap[2] && !cap[3] && !cap[4])) return undefined;
  const delim = cap[0][0];
  const sameBefore = prevChar === delim;
  const maskedOffset = i;
  let runStart = maskedOffset;
  while (runStart > 0 && masked[runStart - 1] === delim) runStart--;
  const beforeRun = prevCodePoint(masked, runStart);
  const beforeIsPunct = beforeRun === '*' || beforeRun === '_' || isPunctStr(beforeRun);
  const canOpen = runStart < maskedOffset ? beforeIsPunct : isPunctStr(prevChar);
  const effPrev = runStart < maskedOffset ? beforeRun : prevChar;
  if (cap[4] && isAlphaNumStr(effPrev)) return undefined;
  const punctAfter = cap[1] || cap[3] || '';
  if (!punctAfter || !effPrev || canOpen) {
    const openLen = openerRunLength(cap[0]);
    let balance = openLen;
    let skipped = 0;
    const totalRun = maskedOffset - runStart + openLen;
    const oddContext = !!beforeRun.trim() && (!!punctAfter || (delim === '*' && !beforeIsPunct));
    if (delim !== '*' && delim !== '_') return undefined;
    const rdelim = delim === '*' ? INLINE.emStrongRDelimAst : INLINE.emStrongRDelimUnd;
    const rdelimA = delim === '*' ? INLINE.emStrongRDelimAstA : INLINE.emStrongRDelimUndA;
    const startPos = i + openLen;
    const lastCloser = lastEmCloser(lx, masked, delim);
    if (lastCloser < startPos) return undefined;
    // The reference scans a copy of the rest of the string with one pattern
    // whose first alternative is anchored to the copy's start. Equivalent
    // without the copy: try that alternative at startPos, then scan the
    // remaining alternatives on the string itself; indices are absolute.
    let scanPos = startPos;
    const aCap = execAt(rdelimA, masked, startPos);
    if (aCap) scanPos = startPos + aCap[0].length;
    rdelim.lastIndex = scanPos;
    let m;
    while ((m = rdelim.exec(masked)) !== null && !(m.index > lastCloser)) {
      const g = m[1] || m[2] || m[3] || m[4] || m[5] || m[6];
      if (!g) continue;
      let closeLen = g.length;
      if (m[3] || m[4]) {
        balance += closeLen;
        continue;
      }
      if (m[5] || m[6] || oddContext) {
        if (sameBefore && (m[5] || m[6])) break;
        if (totalRun % 3 && !((totalRun + closeLen) % 3)) {
          skipped += closeLen;
          continue;
        }
      }
      balance -= closeLen;
      if (balance > 0) continue;
      closeLen = Math.min(closeLen, closeLen + balance + skipped);
      const firstCharLen = firstCpLen(m[0]);
      const raw = s.slice(i, m.index + firstCharLen + closeLen);
      if (Math.min(openLen, closeLen) % 2) {
        const text = raw.slice(1, -1);
        return { type: 'em', raw, text, tokens: inlineTokens(lx, text, []) };
      }
      const text = raw.slice(2, -2);
      return { type: 'strong', raw, text, tokens: inlineTokens(lx, text, []) };
    }
  }
  return undefined;
}

function tokCodespan(lx, s, i) {
  const cap = execAt(INLINE.code, s, i);
  if (!cap) return undefined;
  let text = cap[2].replace(/\n/g, ' ');
  if (/[^ ]/.test(text) && /^ /.test(text) && / $/.test(text)) {
    text = text.substring(1, text.length - 1);
  }
  return { type: 'codespan', raw: cap[0], text };
}

function tokBr(lx, s, i) {
  // INLINE.br by hand: (two or more spaces | a backslash), a newline that is
  // not followed by nothing but whitespace, then any spaces/tabs.
  let j;
  if (s.charCodeAt(i) === 92) {
    j = i + 1;
  } else {
    let k = i;
    while (s.charCodeAt(k) === 32) k++;
    if (k - i < 2) return undefined;
    j = k;
  }
  if (s.charCodeAt(j) !== 10) return undefined;
  let r = j + 1;
  const n = s.length;
  while (r < n && isWsCode(s.charCodeAt(r))) r++;
  if (r === n) return undefined;
  let e = j + 1;
  while (s.charCodeAt(e) === 32 || s.charCodeAt(e) === 9) e++;
  return { type: 'br', raw: s.slice(i, e) };
}

/** Whether a char code is in the \s class. */
function isWsCode(c) {
  if (c < 128) return c === 32 || (c >= 9 && c <= 13);
  return (
    c === 0xA0 || c === 0x1680 || (c >= 0x2000 && c <= 0x200A) ||
    c === 0x2028 || c === 0x2029 || c === 0x202F || c === 0x205F ||
    c === 0x3000 || c === 0xFEFF
  );
}

function tokDel(lx, s, i, masked, prevChar) {
  const cap = execAt(INLINE.delLDelim, s, i);
  if (!cap) return undefined;
  if (!(cap[1] || '') || !prevChar || isPunctStr(prevChar)) {
    const openLen = openerRunLength(cap[0]);
    let balance = openLen;
    const startPos = i + openLen;
    const lastCloser = lastDelCloser(lx, masked);
    if (lastCloser < startPos) return undefined;
    // Same decomposition as the emphasis scan: anchored first alternative
    // at startPos, the rest scanned on the string itself.
    let scanPos = startPos;
    const aCap = execAt(INLINE.delRDelimA, masked, startPos);
    if (aCap) scanPos = startPos + aCap[0].length;
    const rdelim = INLINE.delRDelim;
    rdelim.lastIndex = scanPos;
    let m;
    while ((m = rdelim.exec(masked)) !== null && !(m.index > lastCloser)) {
      const g = m[1] || m[2] || m[3] || m[4] || m[5] || m[6];
      if (!g) continue;
      let len = g.length;
      if (len !== openLen) continue;
      if (m[3] || m[4]) {
        balance += len;
        continue;
      }
      balance -= len;
      if (balance > 0) continue;
      len = Math.min(len, len + balance);
      const firstCharLen = firstCpLen(m[0]);
      const raw = s.slice(i, m.index + firstCharLen + len);
      const text = raw.slice(openLen, -openLen);
      return { type: 'del', raw, text, tokens: inlineTokens(lx, text, []) };
    }
  }
  return undefined;
}

function tokAutolink(lx, s, i) {
  const cap = execAt(INLINE.autolink, s, i);
  if (!cap) return undefined;
  let text;
  let href;
  if (cap[2] === '@') {
    text = cap[1];
    href = 'mailto:' + cap[1];
  } else {
    text = cap[1];
    href = cap[1];
  }
  return { type: 'link', raw: cap[0], text, href, autolink: true, tokens: [{ type: 'text', raw: text, text }] };
}

/** Whether the extended-autolink pattern can start at i (a necessary
 *  condition): a mailto:/xmpp: prefix, a scheme, a www., or an email
 *  local part — a run of [A-Za-z0-9._+-] — ending at an @. */
function urlMayMatch(s, i) {
  const c = s.charCodeAt(i);
  if ((c === 109 || c === 120) && mailtoAt(s, i)) return true;
  if ((c === 104 || c === 72) && httpAt(s, i)) return true;
  if ((c === 102 || c === 70) && ftpAt(s, i)) return true;
  if (c === 119 && s.startsWith('www.', i)) return true;
  if (
    isAlnumCode(c) || c === 46 || c === 95 || c === 43 || c === 45
  ) {
    let j = i + 1;
    for (;;) {
      const d = s.charCodeAt(j);
      if (isAlnumCode(d) || d === 46 || d === 95 || d === 43 || d === 45) j++;
      else break;
    }
    if (s.charCodeAt(j) === 64) return true;
  }
  return false;
}

function tokUrl(lx, s, i) {
  const cap = execAt(INLINE.url, s, i);
  if (!cap) return undefined;
  let text;
  let href;
  if (cap[2] === '@') {
    text = cap[0];
    href = 'mailto:' + cap[0];
  } else {
    let prev;
    do {
      prev = cap[0];
      cap[0] = INLINE.backpedal.exec(cap[0])?.[0] ?? '';
    } while (prev !== cap[0]);
    text = cap[0];
    href = cap[1] === 'www.' ? 'http://' + cap[0] : cap[0];
  }
  return { type: 'link', raw: cap[0], text, href, autolink: true, tokens: [{ type: 'text', raw: text, text }] };
}

// ---------------------------------------------------------------------------
// Plain-text runs. The reference consumes a text run with a single large
// pattern; its extent is: an optional single character before a mailto:/xmpp:
// start, else a first group (a backtick run, a tilde run, or one character)
// followed by the longest lazy run that stops just before the next construct
// start. Every terminator of that lazy run sits at the first position where
// one of these begins: a special character, an email address, an http/https
// or ftp scheme, a www. in link position, a mailto:/xmpp: after a
// non-alphanumeric character, or the space run before a hard break — so a
// single candidate search finds the end, with the two position-sensitive
// candidates (www., mailto:) checked against the preceding character.
// ---------------------------------------------------------------------------

// Characters that can appear in an email address before the @, per the
// reference's text pattern: [a-zA-Z0-9.!#$%&'*+/=?_`{|}~-]
const EMAIL_CHAR = new Uint8Array(128);
for (const ch of 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789.!#$%&\'*+/=?_`{|}~-') {
  EMAIL_CHAR[ch.charCodeAt(0)] = 1;
}

function isAlnumCode(c) {
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122);
}

function isEmailCharAt(s, i) {
  const c = s.charCodeAt(i);
  return c < 128 && EMAIL_CHAR[c] === 1;
}

/** Whether an email address start (one or more email chars, then @) is at i. */
function emailStartAt(s, i) {
  let j = i;
  const n = s.length;
  while (j < n && isEmailCharAt(s, j)) j++;
  return j > i && s.charCodeAt(j) === 64;
}

/** Whether ` {2,}\n` (two or more spaces, then a newline) starts at i. */
function spacesThenNewline(s, i) {
  let j = i;
  const n = s.length;
  while (j < n && s.charCodeAt(j) === 32) j++;
  return j - i >= 2 && s.charCodeAt(j) === 10;
}

function mailtoAt(s, i) {
  return s.startsWith('mailto:', i) || s.startsWith('xmpp:', i);
}

/** Whether the letters http (any case) start at e: the scheme terminator. */
function httpAt(s, e) {
  const a = s.charCodeAt(e), b = s.charCodeAt(e + 1), c = s.charCodeAt(e + 2), d = s.charCodeAt(e + 3);
  return (a === 104 || a === 72) && (b === 116 || b === 84) && (c === 116 || c === 84) && (d === 112 || d === 80);
}

/** Whether ftp:// (any case on the letters) starts at e. */
function ftpAt(s, e) {
  const a = s.charCodeAt(e), b = s.charCodeAt(e + 1), c = s.charCodeAt(e + 2);
  return (a === 102 || a === 70) && (b === 116 || b === 84) && (c === 112 || c === 80) &&
    s.charCodeAt(e + 3) === 58 && s.charCodeAt(e + 4) === 47 && s.charCodeAt(e + 5) === 47;
}

const WWW_PREV_OK = /[\s*_~(]/;

// Candidate construct starts for the text-run scan: single interesting
// characters (specials, the first letters of the scheme/www/mailto starts,
// @, and the spaces of a hard break). Every candidate ends the run at its
// own index, except the position-sensitive ones (www., mailto:/xmpp:, and
// email, whose run start is found by scanning back from the @), which
// scanTextEnd checks individually.
const TEXT_CAND = /[\\<!\[`*~_@hHfFwmx]| {2,}\n/g;

/** The end index (exclusive) of the text run starting at i. Always > i. */
function scanTextEnd(s, i) {
  const n = s.length;
  // A lone non-alphanumeric character just before a mailto:/xmpp: start.
  if (!isAlnumCode(s.charCodeAt(i)) && mailtoAt(s, i + 1)) return i + 1;
  // First group: a backtick run, a tilde run, or any single character.
  let j = i;
  const c0 = s.charCodeAt(j);
  if (c0 === 96 || c0 === 126) {
    while (j < n && s.charCodeAt(j) === c0) j++;
  } else {
    j++;
  }
  if (j >= n) return j;
  const cj = s.charCodeAt(j);
  if (cj === 96 || cj === 126) return j; // next is a backtick or tilde
  if (cj === 32 && spacesThenNewline(s, j)) return j; // hard break follows
  TEXT_CAND.lastIndex = j;
  let m;
  while ((m = TEXT_CAND.exec(s)) !== null) {
    const q = m.index;
    const c = s.charCodeAt(q);
    if (c === 64) {
      // An email ends the run at the start of its address characters;
      // the backward scan stops at j at the earliest, which is exactly
      // the "an email starts here" case. A start before j belongs to a
      // previous token and does not count.
      let r = q;
      while (r > j) {
        const cc = s.charCodeAt(r - 1);
        if (cc < 128 && EMAIL_CHAR[cc] === 1) r--;
        else break;
      }
      if (r < q) return r;
      continue;
    }
    if (c === 119) {
      // www. terminates only after whitespace, one of *_~( , or the start.
      if (s.startsWith('www.', q) && (q === 0 || WWW_PREV_OK.test(s[q - 1]))) return q;
      continue;
    }
    if (c === 104 || c === 72) {
      if (httpAt(s, q)) return q;
      continue;
    }
    if (c === 102 || c === 70) {
      if (ftpAt(s, q)) return q;
      continue;
    }
    if (c === 109 || c === 120) {
      // mailto:/xmpp: terminate only after a non-alphanumeric character.
      if (mailtoAt(s, q) && !isAlnumCode(s.charCodeAt(q - 1))) return q;
      continue;
    }
    return q; // a special character, or the spaces before a hard break
  }
  return n;
}

function tokText(lx, s, i) {
  const raw = s.slice(i, scanTextEnd(s, i));
  const inRaw = lx.state.inRawBlock;
  return { type: 'text', raw, text: inRaw ? raw : decodeCharRefs(raw), escaped: inRaw };
}

/** Tokenize one inline string into `tokens`, honouring the paren gate state. */
function inlineTokens(lx, src, tokens) {
  const st = lx.state;
  const saved = st.linkParenPossible;
  st.linkParenPossible = saved && src.includes(')');
  try {
    return inlineTokensMasked(lx, src, tokens);
  } finally {
    st.linkParenPossible = saved;
  }
}

function inlineTokensMasked(lx, src, tokens) {
  const needsMask = src.includes('*') || src.includes('_') || src.includes('~');
  if (!needsMask) {
    // No delimiter characters at all: no emphasis tokenizers can fire at
    // this level, so the delimiter scan and mask stack are unneeded.
    return inlineLoop(lx, src, src, tokens);
  }
  const masked = maskForEm(lx, src);
  lx.maskStack.push(scanDelimRuns(masked));
  try {
    return inlineLoop(lx, src, masked, tokens);
  } finally {
    lx.maskStack.pop();
  }
}

function inlineLoop(lx, s, masked, tokens) {
  const st = lx.state;
  const n = s.length;
  let i = 0;
  let keepPrev = false;
  let prevChar = '';
  while (i < n) {
    if (!keepPrev) prevChar = '';
    keepPrev = false;
    let tok;
    // First-character dispatch: at any position only a few tokenizers can
    // match, and they are tried in the reference's order within each branch.
    const c = s.charCodeAt(i);
    if (c === 92) {
      // backslash: escape, then hard break
      if ((tok = tokEscape(lx, s, i))) {
        i += tok.raw.length;
        tokens.push(tok);
        continue;
      }
      if ((tok = tokBr(lx, s, i))) {
        i += tok.raw.length;
        tokens.push(tok);
        continue;
      }
    } else if (c === 60) {
      // <: inline tag, then autolink
      if ((tok = tokTag(lx, s, i))) {
        i += tok.raw.length;
        tokens.push(tok);
        continue;
      }
      if ((tok = tokAutolink(lx, s, i))) {
        i += tok.raw.length;
        tokens.push(tok);
        continue;
      }
    } else if (c === 91 || (c === 33 && s.charCodeAt(i + 1) === 91)) {
      // [ or ![ : inline link, then reference link
      if ((tok = tokLink(lx, s, i))) {
        i += tok.raw.length;
        tokens.push(tok);
        continue;
      }
      if ((tok = tokReflink(lx, s, i))) {
        i += tok.raw.length;
        const last = tokens[tokens.length - 1];
        if (tok.type === 'text' && last && last.type === 'text') {
          last.raw += tok.raw;
          last.text += tok.text;
        } else {
          tokens.push(tok);
        }
        continue;
      }
    } else if (c === 42 || c === 95) {
      // * or _: emphasis/strong; a bare email may also start at _
      if ((tok = tokEmStrong(lx, s, i, masked, prevChar))) {
        i += tok.raw.length;
        tokens.push(tok);
        continue;
      }
      if (c === 95 && !st.inLink && urlMayMatch(s, i) && (tok = tokUrl(lx, s, i))) {
        i += tok.raw.length;
        tokens.push(tok);
        continue;
      }
    } else if (c === 96) {
      // `: code span
      if ((tok = tokCodespan(lx, s, i))) {
        i += tok.raw.length;
        tokens.push(tok);
        continue;
      }
    } else if (c === 126) {
      // ~: strikethrough
      if ((tok = tokDel(lx, s, i, masked, prevChar))) {
        i += tok.raw.length;
        tokens.push(tok);
        continue;
      }
    } else if (c === 32) {
      // space: hard break only
      if ((tok = tokBr(lx, s, i))) {
        i += tok.raw.length;
        tokens.push(tok);
        continue;
      }
    } else if (!st.inLink && urlMayMatch(s, i) && (tok = tokUrl(lx, s, i))) {
      i += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    tok = tokText(lx, s, i);
    if (tok) {
      i += tok.raw.length;
      const lastCh = tok.raw[tok.raw.length - 1];
      if (lastCh !== '_') prevChar = lastCh;
      keepPrev = true;
      const last = tokens[tokens.length - 1];
      if (last && last.type === 'text') {
        last.raw += tok.raw;
        last.text += tok.text;
      } else {
        tokens.push(tok);
      }
      continue;
    }
    throw new Error('Infinite loop on byte: ' + s.charCodeAt(i));
  }
  return tokens;
}

// ---------------------------------------------------------------------------
// Block layer
//
// Each tokenizer takes the document string and a cursor and returns a token
// whose `raw` is exactly the slice consumed, or undefined when its construct
// does not start at the cursor.
// ---------------------------------------------------------------------------

function queueInline(lx, src, tokens) {
  lx.inlineQueue.push({ src, tokens });
  return tokens;
}

function blockSpace(lx, s, pos) {
  // The newline rule by hand: repetitions of [ \t]* followed by \n or the
  // end of the input.
  const len = s.length;
  let p = pos;
  while (p < len) {
    let q = p;
    while (q < len && (s[q] === ' ' || s[q] === '\t')) q++;
    if (q < len && s[q] === '\n') {
      p = q + 1;
      continue;
    }
    if (q === len) p = q;
    break;
  }
  if (p === pos) return undefined;
  return { type: 'space', raw: s.slice(pos, p) };
}

function blockCode(lx, s, pos) {
  const cap = execAt(BLOCK.code, s, pos);
  if (!cap) return undefined;
  const raw = trimBlankEnd(cap[0]);
  return { type: 'code', raw, codeBlockStyle: 'indented', text: raw.replace(OTHER.codeRemoveIndent, '') };
}

/** Remove list-indent compensation from fenced code content, when present. */
function fenceText(raw, content) {
  const m = raw.match(OTHER.indentCodeCompensation);
  if (!m) return content;
  const indent = m[1];
  return content
    .split('\n')
    .map((line) => {
      const lead = line.match(/^\s+/);
      if (!lead) return line;
      return line.slice(Math.min(lead[0].length, indent.length));
    })
    .join('\n');
}

function blockFences(lx, s, pos) {
  const cap = execAt(BLOCK.fences, s, pos);
  if (!cap) return undefined;
  return {
    type: 'code',
    raw: cap[0],
    lang: cap[2] ? cap[2].trim().replace(INLINE.anyPunctuation, '$1') : cap[2],
    text: fenceText(cap[0], cap[3] || ''),
  };
}

function blockHeading(lx, s, pos) {
  const cap = execAt(BLOCK.heading, s, pos);
  if (!cap) return undefined;
  let text = cap[2].trim();
  if (OTHER.endingHash.test(text)) {
    const stripped = trimEndChar(text, '#');
    if (!stripped || OTHER.endingSpaceTabChar.test(stripped)) text = stripped.trim();
  }
  const token = { type: 'heading', raw: trimEndChar(cap[0], '\n'), depth: cap[1].length, text, tokens: [] };
  queueInline(lx, text, token.tokens);
  return token;
}

function blockHr(lx, s, pos) {
  const cap = execAt(BLOCK.hr, s, pos);
  if (cap) return { type: 'hr', raw: trimEndChar(cap[0], '\n') };
  return undefined;
}

function blockBlockquote(lx, s, pos) {
  const cap = execAt(BLOCK.blockquote, s, pos);
  if (!cap) return undefined;
  let lines = trimEndChar(cap[0], '\n').split('\n');
  let rawAll = '';
  let textAll = '';
  const tokens = [];
  while (lines.length > 0) {
    let hitMarker = false;
    const chunk = [];
    let p = 0;
    for (; p < lines.length; p++) {
      if (OTHER.blockquoteStart.test(lines[p])) {
        chunk.push(lines[p]);
        hitMarker = true;
      } else if (!hitMarker) {
        chunk.push(lines[p]);
      } else {
        break;
      }
    }
    lines = lines.slice(p);
    const joined = chunk.join('\n');
    const cleaned = joined
      .replace(OTHER.blockquoteMarkerWhitespace, (m, marker, ws) => marker + expandTabs(ws, marker.length))
      .replace(OTHER.blockquoteSetextReplace, '\n    $1')
      .replace(OTHER.blockquoteSetextReplace2, '');
    rawAll = rawAll ? rawAll + '\n' + joined : joined;
    textAll = textAll ? textAll + '\n' + cleaned : cleaned;
    const savedTop = lx.state.top;
    lx.state.top = true;
    blockTokens(lx, cleaned, tokens, true);
    lx.state.top = savedTop;
    if (lines.length === 0) break;
    const last = tokens[tokens.length - 1];
    if (last && (last.type === 'code' || last.type === 'heading' || last.type === 'hr' || last.type === 'html' || last.type === 'table')) break;
    if (last && last.type === 'blockquote') {
      const restJoined = lines.join('\n');
      const merged = last.raw + '\n' + restJoined.replace(OTHER.blockquoteSetextReplace2, '');
      const newTok = blockBlockquote(lx, merged, 0);
      tokens[tokens.length - 1] = newTok;
      const rest = merged.substring(newTok.raw.length).replace(/^\n/, '');
      const restCount = rest ? rest.split('\n').length : 0;
      const consumedLines = restCount ? lines.slice(0, -restCount) : lines;
      if (consumedLines.length > 0) {
        rawAll = rawAll + '\n' + consumedLines.join('\n');
        textAll = textAll.substring(0, textAll.length - last.text.length) + newTok.text;
      }
      lines = lines.slice(consumedLines.length);
      if (lines.length > 0 && OTHER.blockquoteStart.test(lines[0])) continue;
      break;
    }
    if (last && last.type === 'list') {
      const combined = last.raw + '\n' + lines.join('\n');
      const newTok = blockList(lx, combined, 0);
      tokens[tokens.length - 1] = newTok;
      const extra = newTok.raw.length > last.raw.length
        ? combined.slice(last.raw.length + 1, newTok.raw.length).split('\n').length
        : 0;
      if (extra > 0) {
        const taken = lines.slice(0, extra).join('\n');
        rawAll += '\n' + taken;
        textAll += '\n' + taken;
      }
      lines = lines.slice(extra);
      continue;
    }
  }
  return { type: 'blockquote', raw: rawAll, tokens, text: textAll };
}

function blockList(lx, s, pos) {
  const first = execAt(BLOCK.list, s, pos);
  if (!first) return undefined;
  const fullSrc = s;
  const base = pos;
  let p = pos;
  const consumed = () => p - base;
  const bullet = first[1].trim();
  const ordered = bullet.length > 1;
  const list = {
    type: 'list',
    raw: '',
    ordered,
    start: ordered ? +bullet.slice(0, -1) : '',
    loose: false,
    items: [],
  };
  const bulletPattern = ordered ? `\\d{1,9}\\${bullet.slice(-1)}` : `\\${bullet}`;
  const itemRe = listItemRegex(bulletPattern);
  let looseNext = false;
  while (p < s.length) {
    let endEarly = false;
    let itemText = '';
    const cap = execAt(itemRe, s, p);
    if (!cap || testAt(BLOCK.hr, s, p)) break;
    const itemStart = consumed();
    p += cap[0].length;
    const firstLineText = firstLine(cap[2]);
    const bulletWidth = cap[1].length;
    const fc = firstLineText.charCodeAt(0);
    let content = firstLineText;
    if (fc === 32 || fc === 9) {
      // Tab expansion of the leading whitespace; a tab-free run is a no-op.
      let t = 0;
      let hasTab = false;
      while (t < firstLineText.length && (firstLineText[t] === ' ' || firstLineText[t] === '\t')) {
        if (firstLineText[t] === '\t') hasTab = true;
        t++;
      }
      if (hasTab) {
        content = firstLineText.replace(OTHER.leadingSpaceTab, (ws) => expandTabs(ws, bulletWidth));
      }
    }
    let nextLine = lineSlice(s, p);
    const blankFirst = !content.trim();
    let indent = 0;
    if (blankFirst) {
      indent = bulletWidth + 1;
    } else {
      indent = firstNonSpace(content);
      if (indent > 4) indent = 1;
      itemText = content.slice(indent);
      indent += bulletWidth;
    }
    if (blankFirst && OTHER.blankLine.test(nextLine)) {
      p += nextLine.length + 1;
      endEarly = true;
    }
    if (!endEarly) {
      const probes = listProbes(indent);
      const nb = probes.nb;
      const hrRe = probes.hr;
      const fenceRe = probes.fence;
      const headRe = probes.head;
      const htmlRe = probes.html;
      const bqRe = probes.bq;
      const level = Math.min(Math.max(indent - 1, 0), 3);
      let curContent = content;
      let isBlank = blankFirst;
      while (p < s.length) {
        const line = lineSlice(s, p);
        nextLine = line;
        let expanded = line;
        const lc = line.charCodeAt(0);
        if (lc === 32 || lc === 9) {
          let t = 0;
          let hasTab = false;
          while (t < line.length && (line[t] === ' ' || line[t] === '\t')) {
            if (line[t] === '\t') hasTab = true;
            t++;
          }
          if (hasTab) expanded = line.replace(OTHER.leadingSpaceTab, (ws) => expandTabs(ws));
        }
        if (
          probeMayMatch(line, level) &&
          (nb(line) || hrRe(line) || fenceRe(line) || headRe(line) || bqRe(line) || htmlRe(line))
        ) break;
        const sliced = expanded.slice(indent);
        const lineBlank = !line.trim();
        if (firstNonSpace(expanded) >= indent || lineBlank) {
          itemText += '\n' + sliced;
        } else {
          if (
            isBlank ||
            firstNonSpaceTabs4(curContent) >= 4 ||
            (probeMayMatch(curContent, level) &&
              (hrRe(curContent) || fenceRe(curContent) || headRe(curContent) || htmlRe(curContent)))
          ) {
            break;
          }
          const continuation = /^ {0,3}(?:=+|-+) *$/.test(line) && LHEADING_PLAIN.test(`${curContent}\n${line}`)
            ? '    ' + expanded.replace(/^ {0,3}/, '')
            : line;
          itemText += '\n' + continuation;
        }
        isBlank = lineBlank;
        p += line.length + 1;
        curContent = sliced;
      }
    }
    const itemRaw = fullSrc.slice(base + itemStart, base + consumed());
    if (!list.loose) {
      if (looseNext) list.loose = true;
      else if (endsWithBlankLine(itemRaw)) looseNext = true;
    }
    list.items.push({
      type: 'list_item',
      raw: itemRaw,
      task: itemText.charCodeAt(0) === 91 && OTHER.listIsTask.test(itemText),
      loose: false,
      text: itemText,
      tokens: [],
    });
  }
  const lastItem = list.items[list.items.length - 1];
  if (!lastItem) return undefined;
  lastItem.raw = lastItem.raw.trimEnd();
  lastItem.text = lastItem.text.trimEnd();
  list.raw = fullSrc.slice(base, base + consumed()).trimEnd();
  for (const item of list.items) {
    lx.state.top = false;
    item.tokens = blockTokens(lx, item.text, [], false);
    if (!list.loose) {
      for (const t of item.tokens) {
        if (t.type === 'space' && OTHER.anyLine.test(t.raw)) {
          list.loose = true;
          break;
        }
      }
    }
  }
  for (const item of list.items) {
    const head = item.tokens[0];
    if (item.task && head && (head.type === 'text' || head.type === 'paragraph')) {
      item.text = item.text.replace(OTHER.listReplaceTask, '');
      head.raw = head.raw.replace(OTHER.listReplaceTask, '');
      head.text = head.text.replace(OTHER.listReplaceTask, '');
      for (let g = lx.inlineQueue.length - 1; g >= 0; g--) {
        if (OTHER.listIsTask.test(lx.inlineQueue[g].src)) {
          lx.inlineQueue[g].src = lx.inlineQueue[g].src.replace(OTHER.listReplaceTask, '');
          break;
        }
      }
      const check = OTHER.listTaskCheckbox.exec(item.raw);
      if (check) {
        const checkbox = { type: 'checkbox', raw: check[0] + ' ', checked: check[0] !== '[ ]' };
        item.checked = checkbox.checked;
        if (list.loose) {
          if (head && (head.type === 'paragraph' || head.type === 'text') && head.tokens) {
            head.raw = checkbox.raw + head.raw;
            head.text = checkbox.raw + head.text;
            head.tokens.unshift(checkbox);
          } else {
            item.tokens.unshift({ type: 'paragraph', raw: checkbox.raw, text: checkbox.raw, tokens: [checkbox] });
          }
        } else {
          item.tokens.unshift(checkbox);
        }
      }
    } else if (item.task) {
      item.task = false;
    }
  }
  if (list.loose) {
    for (const item of list.items) {
      item.loose = true;
      for (const t of item.tokens) {
        if (t.type === 'text') t.type = 'paragraph';
      }
    }
  }
  return list;
}

function blockHtml(lx, s, pos) {
  const cap = execAt(BLOCK.html, s, pos);
  if (!cap) return undefined;
  const raw = trimBlankEnd(cap[0]);
  return {
    type: 'html',
    block: true,
    raw,
    pre: cap[1] === 'pre' || cap[1] === 'script' || cap[1] === 'style',
    text: raw,
  };
}

function blockDef(lx, s, pos) {
  const cap = execAt(BLOCK.def, s, pos);
  if (!cap) return undefined;
  if (!OTHER.startAngleBracket.test(cap[2]) && findClosingBracket(cap[2], '()') !== -1) return undefined;
  return {
    type: 'def',
    tag: normalizeLabel(cap[1]),
    raw: trimEndChar(cap[0], '\n'),
    href: cap[2] ? cap[2].replace(OTHER.hrefBrackets, '$1').replace(INLINE.anyPunctuation, '$1') : '',
    title: cap[3] ? cap[3].substring(1, cap[3].length - 1).replace(INLINE.anyPunctuation, '$1') : cap[3],
  };
}

function blockTable(lx, s, pos) {
  const cap = execAt(BLOCK.table, s, pos);
  if (!cap || !OTHER.tableDelimiter.test(cap[2])) return undefined;
  const headerCells = splitRow(cap[1]);
  const alignCols = cap[2].replace(OTHER.tableAlignChars, '').split('|');
  if (headerCells.length !== alignCols.length) return undefined;
  const table = { type: 'table', raw: trimEndChar(cap[0], '\n'), header: [], align: [], rows: [] };
  for (const col of alignCols) {
    if (OTHER.tableAlignRight.test(col)) table.align.push('right');
    else if (OTHER.tableAlignCenter.test(col)) table.align.push('center');
    else if (OTHER.tableAlignLeft.test(col)) table.align.push('left');
    else table.align.push(null);
  }
  for (let i = 0; i < headerCells.length; i++) {
    const cell = { text: headerCells[i], tokens: [], header: true, align: table.align[i] };
    queueInline(lx, headerCells[i], cell.tokens);
    table.header.push(cell);
  }
  const rowLines = cap[3]?.trim() ? cap[3].replace(OTHER.tableRowBlankLine, '').split('\n') : [];
  for (const line of rowLines) {
    const cells = splitRow(line, table.header.length);
    const row = [];
    for (let c = 0; c < cells.length; c++) {
      const cell = { text: cells[c], tokens: [], header: false, align: table.align[c] };
      queueInline(lx, cells[c], cell.tokens);
      row.push(cell);
    }
    table.rows.push(row);
  }
  return table;
}

function blockLheading(lx, s, pos) {
  const cap = execAt(BLOCK.lheading, s, pos);
  if (!cap) return undefined;
  const text = cap[1].trim();
  const token = { type: 'heading', raw: trimEndChar(cap[0], '\n'), depth: cap[2].charAt(0) === '=' ? 1 : 2, text, tokens: [] };
  queueInline(lx, text, token.tokens);
  return token;
}

/** One table delimiter column `:?-+:? *` at i; the end index, or -1. */
function delimColAt(s, i, le) {
  if (s[i] === ':') i++;
  let d = 0;
  while (i < le && s[i] === '-') {
    i++;
    d++;
  }
  if (d === 0) return -1;
  if (s[i] === ':') i++;
  while (i < le && s[i] === ' ') i++;
  return i;
}

/** Whether the line s[ls..le) is exactly a table delimiter row. */
function delimLineAt(s, ls, le) {
  let i = ls;
  let sp = 0;
  while (i < le && s[i] === ' ') {
    i++;
    sp++;
  }
  if (sp > 3) return false;
  if (s[i] === '|') {
    i++;
    while (i < le && s[i] === ' ') i++;
  }
  i = delimColAt(s, i, le);
  if (i < 0) return false;
  while (i < le && s[i] === '|') {
    let j = i + 1;
    while (j < le && s[j] === ' ') j++;
    const k = delimColAt(s, j, le);
    if (k < 0) break;
    i = k;
  }
  if (i < le && s[i] === '|') {
    i++;
    while (i < le && s[i] === ' ') i++;
  }
  return i === le;
}

/** The `[ \t]+` then a non-space check after a list bullet at j. */
function paraListWsAfter(s, j, le) {
  if (j >= le) return false;
  if (s[j] !== ' ' && s[j] !== '\t') return false;
  while (j < le && (s[j] === ' ' || s[j] === '\t')) j++;
  return j < le;
}

/**
 * Whether the paragraph pattern refuses the continuation line s[ls..le):
 * its per-line lookahead rejects lines that start another construct (hr,
 * heading, blockquote, fence, list item, HTML block), a table (this line as
 * the header, the next line s[nls..nle) as the delimiter), or a blank line
 * of spaces before a newline. `hasNl` says a newline follows this line.
 */
function paraStopAt(s, ls, le, nls, nle, hasNl) {
  // A line of only spaces/tabs stops the paragraph only before a newline.
  let allWs = true;
  for (let k = ls; k < le; k++) {
    if (s[k] !== ' ' && s[k] !== '\t') {
      allWs = false;
      break;
    }
  }
  if (allWs) return hasNl;
  let sp = 0;
  while (ls + sp < le && s[ls + sp] === ' ') sp++;
  if (sp <= 3) {
    const i = ls + sp;
    const c = s[i];
    if ((c === '-' || c === '_' || c === '*') && hrRun(s, i, le)) return true;
    if (c === '#') {
      let d = 0;
      while (s[i + d] === '#') d++;
      if (d <= 6 && (i + d >= le || isWsCode(s.charCodeAt(i + d)))) return true;
    }
    if (c === '>') return true;
    if (c === '`' || c === '~') {
      let d = 0;
      while (s[i + d] === c) d++;
      if (d >= 3 && (c === '~' || !s.slice(i + d, le).includes('`'))) return true;
    }
    if (c === '*' || c === '+' || c === '-') {
      if (paraListWsAfter(s, i + 1, le)) return true;
    }
    if (c === '1' && (s[i + 1] === '.' || s[i + 1] === ')')) {
      if (paraListWsAfter(s, i + 2, le)) return true;
    }
    if (c === '<' && probeHtml(s.slice(ls, le), 3)) return true;
  }
  if (nls >= 0 && delimLineAt(s, nls, nle)) return true;
  return false;
}

function blockParagraph(lx, s, pos) {
  // The paragraph pattern by hand: a first line, then each following line
  // unless the line starts another construct (see paraStopAt). The extent
  // never includes a trailing newline.
  let end = lineEnd(s, pos);
  let cur = end;
  const len = s.length;
  while (cur < len) {
    const ls = cur + 1;
    const le = lineEnd(s, ls);
    if (le === ls) break; // an empty line cannot continue a paragraph
    const hasNl = le < len;
    const nls = hasNl ? le + 1 : -1;
    const nle = hasNl ? lineEnd(s, nls) : -1;
    if (paraStopAt(s, ls, le, nls, nle, hasNl)) break;
    end = le;
    cur = le;
  }
  const raw = s.slice(pos, end);
  const text = raw.charAt(raw.length - 1) === '\n' ? raw.slice(0, -1) : raw;
  const token = { type: 'paragraph', raw, text, tokens: [] };
  queueInline(lx, text, token.tokens);
  return token;
}

function blockText(lx, s, pos) {
  const end = lineEnd(s, pos);
  if (end === pos) return undefined;
  const raw = s.slice(pos, end);
  const token = { type: 'text', raw, text: raw, tokens: [] };
  queueInline(lx, raw, token.tokens);
  return token;
}

/**
 * Cheap necessary condition for a table: the second line must be a delimiter
 * row (only |, :, - and spaces, at most 3 leading spaces, at least one dash).
 */
function tableGuard(s, pos) {
  const nl = s.indexOf('\n', pos);
  if (nl === -1) return false;
  let end = s.indexOf('\n', nl + 1);
  if (end === -1) end = s.length;
  let i = nl + 1;
  let spaces = 0;
  while (i < end && s[i] === ' ') {
    i++;
    spaces++;
  }
  if (spaces > 3) return false;
  let hasDash = false;
  for (; i < end; i++) {
    const c = s[i];
    if (c === '-') hasDash = true;
    else if (c !== '|' && c !== ':' && c !== ' ') return false;
  }
  return hasDash;
}

/**
 * Cheap necessary condition for a setext heading: an underline line (only
 * '=' or '-' after at most 3 spaces) must appear before the first blank
 * line, since heading text cannot cross a blank line.
 */
function lheadingPossible(s, pos) {
  let i = s.indexOf('\n', pos);
  if (i === -1) return false;
  i++;
  while (i < s.length) {
    let e = s.indexOf('\n', i);
    if (e === -1) e = s.length;
    let blank = true;
    for (let k = i; k < e; k++) {
      if (s[k] !== ' ' && s[k] !== '\t') {
        blank = false;
        break;
      }
    }
    if (blank) return false;
    let k = i;
    let spaces = 0;
    while (k < e && s[k] === ' ') {
      k++;
      spaces++;
    }
    if (spaces <= 3 && k < e && (s[k] === '=' || s[k] === '-')) {
      const ch = s[k];
      let ok = true;
      for (let m = k; m < e; m++) {
        if (s[m] !== ch && s[m] !== ' ' && s[m] !== '\t') {
          ok = false;
          break;
        }
      }
      if (ok) return true;
    }
    i = e + 1;
  }
  return false;
}

function blockTokens(lx, s, tokens, lastParagraphClipped) {
  let clipped = !!lastParagraphClipped;
  const len = s.length;
  let pos = 0;
  let lastLen = Infinity;
  while (pos < len) {
    const remaining = len - pos;
    if (remaining < lastLen) lastLen = remaining;
    else throw new Error('Infinite loop on byte: ' + s.charCodeAt(pos));
    let tok;
    if ((tok = blockSpace(lx, s, pos))) {
      pos += tok.raw.length;
      const last = tokens[tokens.length - 1];
      if (tok.raw.length === 1 && last !== undefined) last.raw += '\n';
      else tokens.push(tok);
      continue;
    }
    // First-significant-character dispatch: every block construct below
    // starts (after at most 3 spaces) with a distinctive character, so most
    // tokenizers can be skipped at most positions. Order is preserved.
    let sp = 0;
    while (sp < 4 && s.charCodeAt(pos + sp) === 32) sp++;
    const sig = s[pos + sp];
    const tabStart = sig === '\t';
    const deep = sp === 4;
    if ((deep || tabStart) && (tok = blockCode(lx, s, pos))) {
      pos += tok.raw.length;
      const last = tokens[tokens.length - 1];
      if (last && (last.type === 'paragraph' || last.type === 'text')) {
        last.raw += (last.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        last.text += '\n' + tok.text;
        lx.inlineQueue[lx.inlineQueue.length - 1].src = last.text;
      } else {
        tokens.push(tok);
      }
      continue;
    }
    if (!deep && !tabStart) {
      if ((sig === '`' || sig === '~') && (tok = blockFences(lx, s, pos))) {
        pos += tok.raw.length;
        tokens.push(tok);
        continue;
      }
      if (sig === '#' && (tok = blockHeading(lx, s, pos))) {
        pos += tok.raw.length;
        tokens.push(tok);
        continue;
      }
      if ((sig === '-' || sig === '_' || sig === '*') && (tok = blockHr(lx, s, pos))) {
        pos += tok.raw.length;
        tokens.push(tok);
        continue;
      }
      if (sig === '>' && (tok = blockBlockquote(lx, s, pos))) {
        pos += tok.raw.length;
        tokens.push(tok);
        continue;
      }
      if (
        (sig === '*' || sig === '+' || sig === '-' || (sig >= '0' && sig <= '9')) &&
        (tok = blockList(lx, s, pos))
      ) {
        pos += tok.raw.length;
        tokens.push(tok);
        continue;
      }
      if (sig === '<' && (tok = blockHtml(lx, s, pos))) {
        pos += tok.raw.length;
        tokens.push(tok);
        continue;
      }
      if (sig === '[' && (tok = blockDef(lx, s, pos))) {
        pos += tok.raw.length;
        const last = tokens[tokens.length - 1];
        if (last && (last.type === 'paragraph' || last.type === 'text')) {
          last.raw += (last.raw.endsWith('\n') ? '' : '\n') + tok.raw;
          last.text += '\n' + tok.raw;
          lx.inlineQueue[lx.inlineQueue.length - 1].src = last.text;
        } else {
          if (!lx.links[tok.tag]) {
            lx.links[tok.tag] = { href: tok.href, title: tok.title };
            lx.linkCount++;
          }
          tokens.push(tok);
        }
        continue;
      }
    }
    if (tableGuard(s, pos) && (tok = blockTable(lx, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    if (!deep && !tabStart && lheadingPossible(s, pos) && (tok = blockLheading(lx, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    if (lx.state.top && (tok = blockParagraph(lx, s, pos))) {
      const last = tokens[tokens.length - 1];
      if (clipped && last && last.type === 'paragraph') {
        last.raw += (last.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        last.text += '\n' + tok.text;
        lx.inlineQueue.pop();
        lx.inlineQueue[lx.inlineQueue.length - 1].src = last.text;
      } else {
        tokens.push(tok);
      }
      clipped = false;
      pos += tok.raw.length;
      continue;
    }
    if ((tok = blockText(lx, s, pos))) {
      pos += tok.raw.length;
      const last = tokens[tokens.length - 1];
      if (last && last.type === 'text') {
        last.raw += (last.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        last.text += '\n' + tok.text;
        lx.inlineQueue.pop();
        lx.inlineQueue[lx.inlineQueue.length - 1].src = last.text;
      } else {
        tokens.push(tok);
      }
      continue;
    }
    throw new Error('Infinite loop on byte: ' + s.charCodeAt(pos));
  }
  lx.state.top = true;
  return tokens;
}

/** Lex a whole document: block pass first, then drain the inline queue. */
function lexDocument(src) {
  const lx = {
    tokens: [],
    links: Object.create(null),
    linkCount: 0,
    inlineQueue: [],
    state: { inLink: false, inRawBlock: false, linkEmitted: false, linkParenPossible: true, top: true },
    maskStack: [],
  };
  const cleaned = src.includes('\r') ? src.replace(/\r\n|\r/g, '\n') : src;
  const tokens = blockTokens(lx, cleaned, lx.tokens, false);
  for (let i = 0; i < lx.inlineQueue.length; i++) {
    const entry = lx.inlineQueue[i];
    lx.state.inRawBlock = false;
    inlineTokens(lx, entry.src, entry.tokens);
  }
  lx.inlineQueue = [];
  return tokens;
}

// ---------------------------------------------------------------------------
// Renderer
// ---------------------------------------------------------------------------

function renderTextToken(t) {
  if (t.tokens) return renderInline(t.tokens, false);
  return t.escaped ? t.text : escapeHtml(t.text);
}

function renderCheckbox(t) {
  return '<input ' + (t.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
}

function renderCodeBlock(t) {
  const lang = (t.lang || '').match(/^\S*/)?.[0];
  const body = t.text ? t.text.replace(/\n$/, '') + '\n' : '';
  const content = t.escaped ? body : escapeHtml(body, true);
  return lang
    ? `<pre><code class="language-${escapeHtml(lang)}">${content}</code></pre>\n`
    : `<pre><code>${content}</code></pre>\n`;
}

function renderCell(cell) {
  const tag = cell.header ? 'th' : 'td';
  const open = cell.align ? `<${tag} align="${cell.align}">` : `<${tag}>`;
  return open + renderInline(cell.tokens, false) + `</${tag}>\n`;
}

function renderTable(t) {
  let headerRow = '';
  for (const cell of t.header) headerRow += renderCell(cell);
  let out = '<table>\n<thead>\n' + `<tr>\n${headerRow}</tr>\n` + '</thead>\n';
  let body = '';
  for (const row of t.rows) {
    let rowText = '';
    for (const cell of row) rowText += renderCell(cell);
    body += `<tr>\n${rowText}</tr>\n`;
  }
  if (body) out += `<tbody>${body}</tbody>`;
  return out + '</table>\n';
}

function renderList(t) {
  let body = '';
  for (const item of t.items) {
    body += `<li>${renderTokens(item.tokens)}</li>\n`;
  }
  const tag = t.ordered ? 'ol' : 'ul';
  const start = t.ordered && t.start !== 1 ? ` start="${t.start}"` : '';
  return `<${tag}${start}>\n${body}</${tag}>\n`;
}

function renderLink(t) {
  const label = t.autolink ? escapeHtml(t.text, true) : renderInline(t.tokens, false);
  const href = cleanUrl(t.href);
  if (href === null) return label;
  let out = `<a href="${escapeHtml(href, t.autolink)}"`;
  if (t.title) out += ` title="${escapeHtml(t.title)}"`;
  return out + '>' + label + '</a>';
}

function renderImage(t) {
  let alt = t.text;
  if (t.tokens) alt = renderInline(t.tokens, true);
  const href = cleanUrl(t.href);
  if (href === null) return escapeHtml(alt);
  let out = `<img src="${escapeHtml(href)}" alt="${escapeHtml(alt)}"`;
  if (t.title) out += ` title="${escapeHtml(t.title)}"`;
  return out + '>';
}

function renderInline(tokens, textOnly) {
  let out = '';
  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i];
    switch (t.type) {
      case 'escape':
        out += textOnly ? t.text : renderTextToken(t);
        break;
      case 'html':
        out += t.text;
        break;
      case 'link':
        out += textOnly ? (t.tokens ? renderInline(t.tokens, true) : t.text) : renderLink(t);
        break;
      case 'image':
        out += textOnly ? (t.tokens ? renderInline(t.tokens, true) : t.text) : renderImage(t);
        break;
      case 'checkbox':
        out += textOnly ? t.raw : renderCheckbox(t);
        break;
      case 'strong':
        out += textOnly ? renderInline(t.tokens, true) : `<strong>${renderInline(t.tokens, false)}</strong>`;
        break;
      case 'em':
        out += textOnly ? renderInline(t.tokens, true) : `<em>${renderInline(t.tokens, false)}</em>`;
        break;
      case 'codespan':
        out += textOnly ? t.text : `<code>${escapeHtml(t.text, true)}</code>`;
        break;
      case 'br':
        out += textOnly ? '' : '<br>';
        break;
      case 'del':
        out += textOnly ? renderInline(t.tokens, true) : `<del>${renderInline(t.tokens, false)}</del>`;
        break;
      case 'text':
        out += textOnly ? t.text : renderTextToken(t);
        break;
      default:
        throw new Error('Token with "' + t.type + '" type was not found.');
    }
  }
  return out;
}

function renderTokens(tokens) {
  let out = '';
  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i];
    switch (t.type) {
      case 'space':
        break;
      case 'hr':
        out += '<hr>\n';
        break;
      case 'heading':
        out += `<h${t.depth}>${renderInline(t.tokens, false)}</h${t.depth}>\n`;
        break;
      case 'code':
        out += renderCodeBlock(t);
        break;
      case 'table':
        out += renderTable(t);
        break;
      case 'blockquote':
        out += `<blockquote>\n${renderTokens(t.tokens)}</blockquote>\n`;
        break;
      case 'list':
        out += renderList(t);
        break;
      case 'checkbox':
        out += renderCheckbox(t);
        break;
      case 'html':
        out += t.text;
        break;
      case 'def':
        break;
      case 'paragraph':
        out += `<p>${renderInline(t.tokens, false)}</p>\n`;
        break;
      case 'text':
        out += renderTextToken(t);
        break;
      default:
        throw new Error('Token with "' + t.type + '" type was not found.');
    }
  }
  return out;
}

/**
 * Render a Markdown string to HTML, byte-identical to marked 18.1.3 with
 * default options for every input.
 */
export function parse(markdown) {
  return renderTokens(lexDocument(markdown));
}

// Dev-only audit hook: the grammar tables, for source comparison against
// the reference's published rules.
export const __rules = { BLOCK, INLINE };
