// parse.js — an original, dependency-free Markdown renderer.
//
// parse(markdown) returns the HTML that marked 18.1.3 renders for the same
// input with its default options (gfm: true, breaks: false, pedantic: false).
// The implementation is my own: a block tokenizer that walks the source once,
// queuing inline work, then an inline tokenizer with delimiter-run matching,
// then a renderer. The regular expressions below are the grammar constants of
// CommonMark 0.31.2 / GFM 0.29 as this renderer encodes them.
//
// No state is kept between calls: every call builds a fresh lexer, so parse
// is deterministic and reentrant.

// ---------------------------------------------------------------------------
// Small string helpers
// ---------------------------------------------------------------------------

const ESCAPE_MAP = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
const ESCAPE_TEST = /[&<>"']/;
const ESCAPE_REPLACE = /[&<>"']/g;
const ESCAPE_TEST_NOENCODE = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/;
const ESCAPE_REPLACE_NOENCODE = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

/** Escape HTML specials. With encode, existing entities are escaped too. */
function escapeHtml(text, encode) {
  if (encode) {
    return ESCAPE_TEST.test(text) ? text.replace(ESCAPE_REPLACE, (c) => ESCAPE_MAP[c]) : text;
  }
  return ESCAPE_TEST_NOENCODE.test(text)
    ? text.replace(ESCAPE_REPLACE_NOENCODE, (c) => ESCAPE_MAP[c])
    : text;
}

const NUMERIC_REF_TEST = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const NUMERIC_REF_OR_AMP = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

/** Resolve numeric character references in a text run; a bare & becomes &amp;. */
function decodeCharRefs(text) {
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
    return encodeURI(href).replace(/%25/g, '%');
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

/** Normalize a link reference label for use as a dictionary key. */
function normalizeLabel(label) {
  return label.trim().replace(/\s+/g, ' ').toLowerCase().toUpperCase().toLowerCase();
}

/** Split a table row into cells, honouring \| escapes, padding to `count`. */
function splitRow(row, count) {
  const markedUp = row.replace(/\|/g, (match, offset, str) => {
    let escaped = false;
    let p = offset;
    while (--p >= 0 && str[p] === '\\') escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = markedUp.split(/ \|/);
  if (!cells[0].trim()) cells.shift();
  if (cells.length > 0 && !cells[cells.length - 1].trim()) cells.pop();
  if (count) {
    if (cells.length > count) cells.splice(count);
    else while (cells.length < count) cells.push('');
  }
  for (let i = 0; i < cells.length; i++) {
    cells[i] = cells[i].trim().replace(/\\\|/g, '|');
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

// Indent-parameterised "does the next construct start here" probes used by the
// list tokenizer. The reference builds these for a level clamped to 0..3 from
// (indent - 1); the same clamp is applied here, with a tiny per-level cache.
function clampedLevel(indent) {
  return Math.max(0, Math.min(3, indent - 1));
}
const levelCache = new Map();
function levelRegex(indent, make) {
  const level = clampedLevel(indent);
  let byKind = levelCache.get(make);
  if (!byKind) {
    byKind = [];
    levelCache.set(make, byKind);
  }
  return byKind[level] || (byKind[level] = make(level));
}
function listItemRegex(bullet) {
  return new RegExp(`^( {0,3}${bullet})((?:[ \t][^\\n]*)?(?:\\n|$))`);
}
function nextBulletRegex(indent) {
  return levelRegex(indent, (n) => new RegExp(`^ {0,${n}}(?:[*+-]|\\d{1,9}[.)])((?:[ \t][^\\n]*)?(?:\\n|$))`));
}
function hrAtRegex(indent) {
  return levelRegex(indent, (n) => new RegExp(`^ {0,${n}}((?:-[ \t]*){3,}|(?:_[ \t]*){3,}|(?:\\*[ \t]*){3,})(?:\\n+|$)`));
}
function fencesBeginRegex(indent) {
  return levelRegex(indent, (n) => new RegExp(`^ {0,${n}}(?:\`\`\`|~~~)`));
}
function headingBeginRegex(indent) {
  return levelRegex(indent, (n) => new RegExp(`^ {0,${n}}#{1,6}(?:\\s|$)`));
}
function htmlBeginRegex(indent) {
  return levelRegex(indent, (n) => new RegExp(`^ {0,${n}}(?:</?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, 'i'));
}
function blockquoteBeginRegex(indent) {
  return levelRegex(indent, (n) => new RegExp(`^ {0,${n}}>`));
}

// All six "next construct" probes for one list indent level, cached together.
const probesCache = new Map();
function listProbes(indent) {
  let probes = probesCache.get(indent);
  if (!probes) {
    probes = {
      nb: nextBulletRegex(indent),
      hr: hrAtRegex(indent),
      fence: fencesBeginRegex(indent),
      head: headingBeginRegex(indent),
      html: htmlBeginRegex(indent),
      bq: blockquoteBeginRegex(indent),
    };
    probesCache.set(indent, probes);
  }
  return probes;
}

// ---------------------------------------------------------------------------
// Block grammar (GFM rule set)
// ---------------------------------------------------------------------------

const BLOCK = {
  newline: /^(?:[ \t]*(?:\n|$))+/,
  code: /^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/,
  fences: /^ {0,3}(`{3,}(?=[^`\n]*(?:\n|$))|~{3,})([^\n]*)(?:\n|$)(?:|([\s\S]*?)(?:\n|$))(?: {0,3}(?:(?=`)\1`*|(?=~)\1~*) *(?=\n|$)|$)/,
  heading: /^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/,
  hr: /^ {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/,
  blockquote: /^( {0,3}> ?(?:(?![ \t]*(?:\n|$))(([^\n]+(?:\n(?! {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)| {0,3}#{1,6}(?:\s|$)| {0,3}>| {0,3}(?:`{3,}(?=[^`\n]*(?:\n|$))|~~~)[^\n]*(?:\n|$)| {0,3}(?:[*+-]|\d{1,9}[.)])(?:[ \t]|\n|$)| {0,3}(?:<\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\n|\/?>)|<(?:(?:script|pre|style|textarea)(?:[\s>]|$)|!--)|<\?|<![A-Za-z]|<!\[CDATA\[)|[ \t]+\n)[^\n]+)*))|[^\n]*)(?:\n|$))+/,
  list: /^( {0,3}(?:[*+-]|\d{1,9}[.)]))([ \t][^\n]*?)?(?:\n|$)/,
  html: /^ {0,3}(?:<(script|pre|style|textarea)[\s>][\s\S]*?(?:<\/\1>[^\n]*\n*|$)|<!--(?:-?>|[\s\S]*?(?:-->|$))[^\n]*(\n+|$)|<\?[\s\S]*?(?:\?>[^\n]*\n*|$)|<![A-Z][\s\S]*?(?:>[^\n]*\n*|$)|<!\[CDATA\[[\s\S]*?(?:\]\]>[^\n]*\n*|$)|<\/?(address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?:[ \t]+|\n|\/?>|$)[\s\S]*?(?:(?:\n[ \t]*)+\n|$)|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?: +[a-zA-Z:_][\w.:-]*(?: *= *"[^"\n]*"| *= *'[^'\n]*'| *= *[^\s"'=<>`]+)?)*? *\/?>(?=[ \t]*(?:\n|$))[\s\S]*?(?:(?:\n[ \t]*)+\n|$)|<\/[a-z][a-z0-9-]*\s*>(?=[ \t]*(?:\n|$))[\s\S]*?(?:(?:\n[ \t]*)+\n|$))/i,
  def: /^ {0,3}\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+)\]: *(?:\n[ \t]*)?([^<\s][^\s]*|<.*?>)(?:(?: +(?:\n[ \t]*)?| *\n[ \t]*)((?:"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\\n]|\n(?!\n))*'|\((?:\\[\s\S]|[^()\\])*\))))? *(?:\n+|$)/,
  table: /^ *([^\n ].*)\n {0,3}((?:\| *)?:?-+:? *(?:\| *:?-+:? *)*(?:\| *)?)(?:\n((?:(?! *\n| {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)| {0,3}#{1,6}(?:\s|$)| {0,3}>|(?: {4}| {0,3}\t)[^\n]| {0,3}(?:`{3,}(?=[^`\n]*(?:\n|$))|~~~)[^\n]*(?:\n|$)| {0,3}(?:[*+-]|1[.)])[ \t]| {0,3}(?:<\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\n|\/?>)|<(?:(?:script|pre|style|textarea)(?:[\s>]|$)|!--)|<\?|<![A-Za-z]|<!\[CDATA\[)).*(?:\n|$))*)\n*|$)/,
  lheading: /^(?! {0,3}(?:[*+-]|\d{1,9}[.)]) |(?: {4}| {0,3}\t)| {0,3}(?:`{3,}|~{3,})| {0,3}>| {0,3}#{1,6}(?:\s|$)| {0,3}<[^\n>]+>\n| {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n)((?:.|\n(?!\s*?\n| {0,3}(?:[*+-]|\d{1,9}[.)]) | {0,3}(?:`{3,}|~{3,})| {0,3}>| {0,3}#{1,6}(?:\s|$)| {0,3}(?:(?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)| {0,3}<[^\n>]+>\n| {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n))+?)\n {0,3}(=+|-+)[ \t]*(?:\n+|$)/,
  paragraph: /^([^\n]+(?:\n(?! {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)| {0,3}#{1,6}(?:\s|$)| {0,3}>| {0,3}(?:`{3,}(?=[^`\n]*(?:\n|$))|~~~)[^\n]*(?:\n|$)| {0,3}(?:[*+-]|1[.)])[ \t]+[^ \t\n]| {0,3}(?:<\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\n|\/?>)|<(?:(?:script|pre|style|textarea)(?:[\s>]|$)|!--)|<\?|<![A-Za-z]|<!\[CDATA\[)| *([^\n ].*)\n {0,3}((?:\| *)?:?-+:? *(?:\| *:?-+:? *)*(?:\| *)?)(?:\n((?:(?! *\n| {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)| {0,3}#{1,6}(?:\s|$)| {0,3}>|(?: {4}| {0,3}\t)[^\n]| {0,3}(?:`{3,}(?=[^`\n]*(?:\n|$))|~~~)[^\n]*(?:\n|$)| {0,3}(?:[*+-]|1[.)])[ \t]| {0,3}(?:<\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\n|\/?>)|<(?:(?:script|pre|style|textarea)(?:[\s>]|$)|!--)|<\?|<![A-Za-z]|<!\[CDATA\[)).*(?:\n|$))*)\n*|$)|[ \t]+\n)[^\n]+)*)/,
  text: /^[^\n]+/,
};

// ---------------------------------------------------------------------------
// Inline grammar (GFM rule set)
// ---------------------------------------------------------------------------

const INLINE = {
  escape: /^\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/,
  code: /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/,
  br: /^( {2,}|\\)\n(?!\s*$)[ \t]*/,
  tag: /^<!--(?:-?>|[\s\S]*?-->)|^<\/[a-zA-Z][a-zA-Z0-9-]*\s*>|^<[a-zA-Z][a-zA-Z0-9-]*(?:\s+[a-zA-Z:_][\w.:-]*(?:\s*=\s*"[^"]*"|\s*=\s*'[^']*'|\s*=\s*[^\s"'=<>`]+)?)*?\s*\/?>|^<\?[\s\S]*?\?>|^<![a-zA-Z]+\s[\s\S]*?>|^<!\[CDATA\[[\s\S]*?\]\]>/,
  link: /^!?\[((?:\[(?:\[(?:\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\])|[^\[\]\\`])*?)\]\([ \t\n]*(<(?:\\.|[^\n<>\\])+>|[^ \t\n\x00-\x1f]+|(?=\)))(?:(?:[ \t]+(?:\n[ \t]*)?|\n[ \t]*)("(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\])*'|\((?:\\[\s\S]|[^)\\])*\)))?[ \t\n]*\)/,
  reflink: /^!?\[((?:\[(?:\[(?:\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\])|[^\[\]\\`])*?)\]\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+)\]/,
  nolink: /^!?\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+)\](?:\[\])?/,
  reflinkSearch: /!?\[((?:[^\[\]\\`]*(?:\[(?:\[(?:\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\]))){0,999}?[^\[\]\\`]*?)\]\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\]){1,999})\]|!?\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\]){1,999})\](?:\[\])?(?!\()/g,
  blockSkip: /\[(?:[^\[\]`]|(?<a>`+)[^`]+\k<a>(?!`))*?\]\((?:\\[\s\S]|[^\\\(\)]|\((?:\\[\s\S]|[^\\\(\)])*\))*\)|(?<!`)()(?<b>`+)[^`]+\k<b>(?!`)|<(?! )[^<>]*?>/g,
  anyPunctuation: /\\([\p{P}\p{S}])/gu,
  anyPunctuationOutsideCode: /(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\([\p{P}\p{S}])/gu,
  punctuation: /^((?![*_])[\s\p{P}\p{S}])/u,
  emStrongLDelim: /^(?:\*+(?:((?!\*)(?!~)[\p{P}\p{S}])|([^\s*]))?)|^_+(?:((?!_)(?!~)[\p{P}\p{S}])|([^\s_]))?/u,
  emStrongRDelimAst: /^[^_*]*?__[^_*]*?\*[^_*]*?(?=__)|[^*]+(?=[^*])|(?!\*)(?!~)[\p{P}\p{S}](\*+)(?=[\s]|$)|(?:[^\s\p{P}\p{S}]|~)(\*+)(?!\*)(?=(?!~)[\s\p{P}\p{S}]|$)|(?!\*)(?!~)[\s\p{P}\p{S}](\*+)(?=(?:[^\s\p{P}\p{S}]|~))|[\s](\*+)(?!\*)(?=(?!~)[\p{P}\p{S}])|(?!\*)(?!~)[\p{P}\p{S}](\*+)(?!\*)(?=(?!~)[\p{P}\p{S}])|(?:[^\s\p{P}\p{S}]|~)(\*+)(?=(?:[^\s\p{P}\p{S}]|~))/gu,
  emStrongRDelimUnd: /^[^_*]*?\*\*[^_*]*?_[^_*]*?(?=\*\*)|[^_]+(?=[^_])|(?!_)[\p{P}\p{S}](_+)(?=[\s]|$)|[^\s\p{P}\p{S}](_+)(?!_)(?=[\s\p{P}\p{S}]|$)|(?!_)[\s\p{P}\p{S}](_+)(?=[^\s\p{P}\p{S}])|[\s](_+)(?!_)(?=[\p{P}\p{S}])|(?!_)[\p{P}\p{S}](_+)(?!_)(?=[\p{P}\p{S}])/gu,
  delLDelim: /^~~?(?:((?!~)[\p{P}\p{S}])|[^\s~])/u,
  delRDelim: /^[^~]+(?=[^~])|(?!~)[\p{P}\p{S}](~~?)(?=[\s]|$)|[^\s\p{P}\p{S}](~~?)(?!~)(?=[\s\p{P}\p{S}]|$)|(?!~)[\s\p{P}\p{S}](~~?)(?=[^\s\p{P}\p{S}])|[\s](~~?)(?!~)(?=[\p{P}\p{S}])|(?!~)[\p{P}\p{S}](~~?)(?!~)(?=[\p{P}\p{S}])|[^\s\p{P}\p{S}](~~?)(?=[^\s\p{P}\p{S}])/gu,
  autolink: /^<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\s\x00-\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>/,
  url: /^(?:mailto:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])|xmpp:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])(?:\/[A-Za-z0-9@.]+)?)|^((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\/\/|www\.)(?:[a-zA-Z0-9\-]+\.?)+[^\s<]*|^[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])/,
  backpedal: /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/,
  text: /^(?:[^a-zA-Z0-9](?=(?:mailto|xmpp):)|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\n)|(?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@)|[\s\S]*?(?:(?=[\\<!\[`*~_]|\b_|[hH][tT][tT][pP][sS]?|[fF][tT][pP]:\/\/|(?<![^\s*_~(])www\.|$)|[^ ](?= {2,}\n)|[^a-zA-Z0-9](?=(?:mailto|xmpp):)|[^a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-](?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@))))/,
};

// ---------------------------------------------------------------------------
// Inline layer
//
// Inline tokenizing runs after the block pass: block tokenizers queue their
// text, and the queue is drained in order once every link definition in the
// document has been registered. Emphasis and strikethrough matching works on
// a masked copy of the text (same length) where link destinations, code spans
// and escaped punctuation are blanked out, so delimiter runs inside them are
// invisible to the matcher.
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
function scanDelimRuns(masked) {
  const lastEm = { '*': -1, '_': -1 };
  let lastDel = -1;
  const n = masked.length;
  for (let s = 0; s < n; s++) {
    const r = masked[s];
    if (r !== '*' && r !== '_' && r !== '~') continue;
    const before = s === 0 ? '\n' : masked[s - 1];
    let i = s + 1;
    while (i < n && masked[i] === r) i++;
    if (before !== ' ' && before !== '\t' && before !== '\n' && before !== '\r' && before !== '\f') {
      if (r === '~') lastDel = s;
      else lastEm[r] = s;
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
    if (INLINE.link.test(m[0]) && text.charAt(m.index - 1) !== '!') return true;
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
    t = t.replace(INLINE.anyPunctuationOutsideCode, (match, codeRun, punct) =>
      punct
        ? '+'.repeat(match.length)
        : codeRun
          ? codeRun + match.slice(codeRun.length, -codeRun.length).replace(/`/g, '+') + codeRun
          : match,
    );
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
      const m = INLINE.code.exec(label.slice(s));
      if (m) {
        s += m[0].length - 1;
        continue;
      }
    }
    if (label[s] !== '<') continue;
    const rest = src.slice(offset + s);
    const m = INLINE.tag.exec(rest) || INLINE.autolink.exec(rest);
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

function tokEscape(lx, src) {
  const cap = INLINE.escape.exec(src);
  if (cap) return { type: 'escape', raw: cap[0], text: cap[1] };
  return undefined;
}

function tokTag(lx, src) {
  const cap = INLINE.tag.exec(src);
  if (!cap) return undefined;
  const st = lx.state;
  if (!st.inLink && OTHER.startATag.test(cap[0])) st.inLink = true;
  else if (st.inLink && OTHER.endATag.test(cap[0])) st.inLink = false;
  if (!st.inRawBlock && OTHER.startPreScriptTag.test(cap[0])) st.inRawBlock = true;
  else if (st.inRawBlock && OTHER.endPreScriptTag.test(cap[0])) st.inRawBlock = false;
  return { type: 'html', raw: cap[0], inLink: st.inLink, inRawBlock: st.inRawBlock, block: false, text: cap[0] };
}

function tokLink(lx, src) {
  if (lx.state.linkParenPossible === false) return undefined;
  const cap = INLINE.link.exec(src);
  if (!cap) return undefined;
  const labelOffset = cap[0].charAt(0) === '!' ? 2 : 1;
  if (labelHasOpenTag(src, cap[1], labelOffset)) return undefined;
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

function tokReflink(lx, src) {
  let cap;
  if ((cap = INLINE.reflink.exec(src)) || (cap = INLINE.nolink.exec(src))) {
    const labelOffset = cap[0].charAt(0) === '!' ? 2 : 1;
    if (labelHasOpenTag(src, cap[1], labelOffset)) return undefined;
    const def = lx.links[normalizeLabel(cap[2] || cap[1])];
    if (!def) {
      const first = cap[0].charAt(0);
      return { type: 'text', raw: first, text: first };
    }
    return buildLink(lx, cap, def, cap[0]);
  }
  return undefined;
}

function tokEmStrong(lx, src, masked, prevChar) {
  const cap = INLINE.emStrongLDelim.exec(src);
  if (!cap || (!cap[1] && !cap[2] && !cap[3] && !cap[4])) return undefined;
  const delim = cap[0][0];
  const sameBefore = prevChar === delim;
  const maskedOffset = masked.length - src.length;
  let runStart = maskedOffset;
  while (runStart > 0 && masked[runStart - 1] === delim) runStart--;
  const beforeRun = prevCodePoint(masked, runStart);
  const beforeIsPunct = beforeRun === '*' || beforeRun === '_' || !!INLINE.punctuation.exec(beforeRun);
  const canOpen = runStart < maskedOffset ? beforeIsPunct : !!INLINE.punctuation.exec(prevChar);
  const effPrev = runStart < maskedOffset ? beforeRun : prevChar;
  if (cap[4] && effPrev.match(OTHER.unicodeAlphaNumeric)) return undefined;
  const punctAfter = cap[1] || cap[3] || '';
  if (!punctAfter || !effPrev || canOpen) {
    const openLen = openerRunLength(cap[0]);
    let balance = openLen;
    let skipped = 0;
    const totalRun = maskedOffset - runStart + openLen;
    const oddContext = !!beforeRun.trim() && (!!punctAfter || (delim === '*' && !beforeIsPunct));
    if (delim !== '*' && delim !== '_') return undefined;
    const rdelim = delim === '*' ? INLINE.emStrongRDelimAst : INLINE.emStrongRDelimUnd;
    const startPos = masked.length - src.length + openLen;
    const lastCloser = lastEmCloser(lx, masked, delim);
    if (lastCloser < startPos) return undefined;
    const rest = masked.slice(startPos);
    const limit = lastCloser - startPos;
    rdelim.lastIndex = 0;
    let m;
    while ((m = rdelim.exec(rest)) !== null && !(m.index > limit)) {
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
      const raw = src.slice(0, openLen + m.index + firstCharLen + closeLen);
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

function tokCodespan(lx, src) {
  const cap = INLINE.code.exec(src);
  if (!cap) return undefined;
  let text = cap[2].replace(/\n/g, ' ');
  if (/[^ ]/.test(text) && /^ /.test(text) && / $/.test(text)) {
    text = text.substring(1, text.length - 1);
  }
  return { type: 'codespan', raw: cap[0], text };
}

function tokBr(lx, src) {
  const cap = INLINE.br.exec(src);
  if (cap) return { type: 'br', raw: cap[0] };
  return undefined;
}

function tokDel(lx, src, masked, prevChar) {
  const cap = INLINE.delLDelim.exec(src);
  if (!cap) return undefined;
  if (!(cap[1] || '') || !prevChar || INLINE.punctuation.exec(prevChar)) {
    const openLen = openerRunLength(cap[0]);
    let balance = openLen;
    const startPos = masked.length - src.length + openLen;
    const lastCloser = lastDelCloser(lx, masked);
    if (lastCloser < startPos) return undefined;
    const rest = masked.slice(startPos);
    const limit = lastCloser - startPos;
    const rdelim = INLINE.delRDelim;
    rdelim.lastIndex = 0;
    let m;
    while ((m = rdelim.exec(rest)) !== null && !(m.index > limit)) {
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
      const raw = src.slice(0, openLen + m.index + firstCharLen + len);
      const text = raw.slice(openLen, -openLen);
      return { type: 'del', raw, text, tokens: inlineTokens(lx, text, []) };
    }
  }
  return undefined;
}

function tokAutolink(lx, src) {
  const cap = INLINE.autolink.exec(src);
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

function tokUrl(lx, src) {
  const cap = INLINE.url.exec(src);
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

function tokText(lx, src) {
  const cap = INLINE.text.exec(src);
  if (!cap) return undefined;
  const inRaw = lx.state.inRawBlock;
  return { type: 'text', raw: cap[0], text: inRaw ? cap[0] : decodeCharRefs(cap[0]), escaped: inRaw };
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

function inlineLoop(lx, src, masked, tokens) {
  const st = lx.state;
  let keepPrev = false;
  let prevChar = '';
  while (src) {
    if (!keepPrev) prevChar = '';
    keepPrev = false;
    let tok;
    // First-character dispatch: at any position only a few tokenizers can
    // match, and they are tried in the reference's order within each branch.
    const c = src.charCodeAt(0);
    if (c === 92) {
      // backslash: escape, then hard break
      if ((tok = tokEscape(lx, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
      if ((tok = tokBr(lx, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
    } else if (c === 60) {
      // <: inline tag, then autolink
      if ((tok = tokTag(lx, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
      if ((tok = tokAutolink(lx, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
    } else if (c === 91 || (c === 33 && src.charCodeAt(1) === 91)) {
      // [ or ![ : inline link, then reference link
      if ((tok = tokLink(lx, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
      if ((tok = tokReflink(lx, src))) {
        src = src.substring(tok.raw.length);
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
      if ((tok = tokEmStrong(lx, src, masked, prevChar))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
      if (c === 95 && !st.inLink && (tok = tokUrl(lx, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
    } else if (c === 96) {
      // `: code span
      if ((tok = tokCodespan(lx, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
    } else if (c === 126) {
      // ~: strikethrough
      if ((tok = tokDel(lx, src, masked, prevChar))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
    } else if (c === 32) {
      // space: hard break only
      if ((tok = tokBr(lx, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
    } else if (!st.inLink && (tok = tokUrl(lx, src))) {
      src = src.substring(tok.raw.length);
      tokens.push(tok);
      continue;
    }
    tok = tokText(lx, src);
    if (tok) {
      src = src.substring(tok.raw.length);
      if (tok.raw.slice(-1) !== '_') prevChar = tok.raw.slice(-1);
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
    throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
  }
  return tokens;
}

// ---------------------------------------------------------------------------
// Block layer
// ---------------------------------------------------------------------------

function queueInline(lx, src, tokens) {
  lx.inlineQueue.push({ src, tokens });
  return tokens;
}

function blockSpace(lx, src) {
  const cap = BLOCK.newline.exec(src);
  if (cap && cap[0].length > 0) return { type: 'space', raw: cap[0] };
  return undefined;
}

function blockCode(lx, src) {
  const cap = BLOCK.code.exec(src);
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

function blockFences(lx, src) {
  const cap = BLOCK.fences.exec(src);
  if (!cap) return undefined;
  return {
    type: 'code',
    raw: cap[0],
    lang: cap[2] ? cap[2].trim().replace(INLINE.anyPunctuation, '$1') : cap[2],
    text: fenceText(cap[0], cap[3] || ''),
  };
}

function blockHeading(lx, src) {
  const cap = BLOCK.heading.exec(src);
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

function blockHr(lx, src) {
  const cap = BLOCK.hr.exec(src);
  if (cap) return { type: 'hr', raw: trimEndChar(cap[0], '\n') };
  return undefined;
}

function blockBlockquote(lx, src) {
  const cap = BLOCK.blockquote.exec(src);
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
      const newTok = blockBlockquote(lx, merged);
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
      const newTok = blockList(lx, combined);
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

function blockList(lx, src) {
  const first = BLOCK.list.exec(src);
  if (!first) return undefined;
  const fullSrc = src;
  const consumed = () => fullSrc.length - src.length;
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
  while (src) {
    let endEarly = false;
    let itemText = '';
    const cap = itemRe.exec(src);
    if (!cap || BLOCK.hr.test(src)) break;
    const itemStart = consumed();
    src = src.substring(cap[0].length);
    const firstLineText = firstLine(cap[2]);
    const bulletWidth = cap[1].length;
    const content = firstLineText.replace(OTHER.leadingSpaceTab, (ws) => expandTabs(ws, bulletWidth));
    let nextLine = firstLine(src);
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
      src = src.substring(nextLine.length + 1);
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
      while (src) {
        const line = firstLine(src);
        nextLine = line;
        const expanded = line.replace(OTHER.leadingSpaceTab, (ws) => expandTabs(ws));
        if (
          probeMayMatch(line, level) &&
          (fenceRe.test(line) || headRe.test(line) || htmlRe.test(line) || bqRe.test(line) || nb.test(line) || hrRe.test(line))
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
              (fenceRe.test(curContent) || headRe.test(curContent) || htmlRe.test(curContent) || hrRe.test(curContent)))
          ) {
            break;
          }
          const continuation = /^ {0,3}(?:=+|-+) *$/.test(line) && BLOCK.lheading.test(`${curContent}\n${line}`)
            ? '    ' + expanded.replace(/^ {0,3}/, '')
            : line;
          itemText += '\n' + continuation;
        }
        isBlank = lineBlank;
        src = src.substring(line.length + 1);
        curContent = sliced;
      }
    }
    const itemRaw = fullSrc.slice(itemStart, consumed());
    if (!list.loose) {
      if (looseNext) list.loose = true;
      else if (endsWithBlankLine(itemRaw)) looseNext = true;
    }
    list.items.push({
      type: 'list_item',
      raw: itemRaw,
      task: OTHER.listIsTask.test(itemText),
      loose: false,
      text: itemText,
      tokens: [],
    });
  }
  const lastItem = list.items[list.items.length - 1];
  if (!lastItem) return undefined;
  lastItem.raw = lastItem.raw.trimEnd();
  lastItem.text = lastItem.text.trimEnd();
  list.raw = fullSrc.slice(0, consumed()).trimEnd();
  for (const item of list.items) {
    lx.state.top = false;
    item.tokens = blockTokens(lx, item.text, [], false);
    if (!list.loose) {
      const spaces = item.tokens.filter((t) => t.type === 'space');
      if (spaces.length > 0 && spaces.some((t) => OTHER.anyLine.test(t.raw))) list.loose = true;
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

function blockHtml(lx, src) {
  const cap = BLOCK.html.exec(src);
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

function blockDef(lx, src) {
  const cap = BLOCK.def.exec(src);
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

function blockTable(lx, src) {
  const cap = BLOCK.table.exec(src);
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

function blockLheading(lx, src) {
  const cap = BLOCK.lheading.exec(src);
  if (!cap) return undefined;
  const text = cap[1].trim();
  const token = { type: 'heading', raw: trimEndChar(cap[0], '\n'), depth: cap[2].charAt(0) === '=' ? 1 : 2, text, tokens: [] };
  queueInline(lx, text, token.tokens);
  return token;
}

function blockParagraph(lx, src) {
  const cap = BLOCK.paragraph.exec(src);
  if (!cap) return undefined;
  const text = cap[1].charAt(cap[1].length - 1) === '\n' ? cap[1].slice(0, -1) : cap[1];
  const token = { type: 'paragraph', raw: cap[0], text, tokens: [] };
  queueInline(lx, text, token.tokens);
  return token;
}

function blockText(lx, src) {
  const cap = BLOCK.text.exec(src);
  if (!cap) return undefined;
  const token = { type: 'text', raw: cap[0], text: cap[0], tokens: [] };
  queueInline(lx, cap[0], token.tokens);
  return token;
}

/**
 * Cheap necessary condition for a table: the second line must be a delimiter
 * row (only |, :, - and spaces, at most 3 leading spaces, at least one dash).
 */
function tableGuard(src) {
  const nl = src.indexOf('\n');
  if (nl === -1) return false;
  let end = src.indexOf('\n', nl + 1);
  if (end === -1) end = src.length;
  let i = nl + 1;
  let spaces = 0;
  while (i < end && src[i] === ' ') {
    i++;
    spaces++;
  }
  if (spaces > 3) return false;
  let hasDash = false;
  for (; i < end; i++) {
    const c = src[i];
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
function lheadingPossible(src) {
  let i = src.indexOf('\n');
  if (i === -1) return false;
  i++;
  while (i < src.length) {
    let e = src.indexOf('\n', i);
    if (e === -1) e = src.length;
    let blank = true;
    for (let k = i; k < e; k++) {
      if (src[k] !== ' ' && src[k] !== '\t') {
        blank = false;
        break;
      }
    }
    if (blank) return false;
    let k = i;
    let spaces = 0;
    while (k < e && src[k] === ' ') {
      k++;
      spaces++;
    }
    if (spaces <= 3 && k < e && (src[k] === '=' || src[k] === '-')) {
      const ch = src[k];
      let ok = true;
      for (let m = k; m < e; m++) {
        if (src[m] !== ch && src[m] !== ' ' && src[m] !== '\t') {
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

function blockTokens(lx, src, tokens, lastParagraphClipped) {
  let clipped = !!lastParagraphClipped;
  let lastLen = Infinity;
  while (src) {
    if (src.length < lastLen) lastLen = src.length;
    else throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
    let tok;
    if ((tok = blockSpace(lx, src))) {
      src = src.substring(tok.raw.length);
      const last = tokens[tokens.length - 1];
      if (tok.raw.length === 1 && last !== undefined) last.raw += '\n';
      else tokens.push(tok);
      continue;
    }
    // First-significant-character dispatch: every block construct below
    // starts (after at most 3 spaces) with a distinctive character, so most
    // tokenizers can be skipped at most positions. Order is preserved.
    let sp = 0;
    while (sp < 4 && src.charCodeAt(sp) === 32) sp++;
    const sig = src[sp];
    const tabStart = sig === '\t';
    const deep = sp === 4;
    if ((deep || tabStart) && (tok = blockCode(lx, src))) {
      src = src.substring(tok.raw.length);
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
      if ((sig === '`' || sig === '~') && (tok = blockFences(lx, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
      if (sig === '#' && (tok = blockHeading(lx, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
      if ((sig === '-' || sig === '_' || sig === '*') && (tok = blockHr(lx, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
      if (sig === '>' && (tok = blockBlockquote(lx, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
      if (
        (sig === '*' || sig === '+' || sig === '-' || (sig >= '0' && sig <= '9')) &&
        (tok = blockList(lx, src))
      ) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
      if (sig === '<' && (tok = blockHtml(lx, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
      if (sig === '[' && (tok = blockDef(lx, src))) {
        src = src.substring(tok.raw.length);
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
    if (tableGuard(src) && (tok = blockTable(lx, src))) {
      src = src.substring(tok.raw.length);
      tokens.push(tok);
      continue;
    }
    if (!deep && !tabStart && lheadingPossible(src) && (tok = blockLheading(lx, src))) {
      src = src.substring(tok.raw.length);
      tokens.push(tok);
      continue;
    }
    if (lx.state.top && (tok = blockParagraph(lx, src))) {
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
      src = src.substring(tok.raw.length);
      continue;
    }
    if ((tok = blockText(lx, src))) {
      src = src.substring(tok.raw.length);
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
    throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
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
