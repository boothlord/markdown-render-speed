// Driver for the markdown-render-speed-02 entry.
//
// Reads the case set (a JSON array of {"id", "markdown"}) from the input
// directory, renders each case on its own with parse() from ./parse.js, and
// writes the resulting HTML strings, in the cases' order, as a JSON array to
// html.json in the output directory. Outside the grading container the
// MAKEFUN_INPUT_DIR / MAKEFUN_OUTPUT_DIR environment variables stand in for
// /input and /output.

import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

const inputDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outputDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const cases = JSON.parse(readFileSync(join(inputDir, 'cases.json'), 'utf8')) as { id: string; markdown: string }[];

const html = new Array<string>(cases.length);
for (let i = 0; i < cases.length; i++) {
  html[i] = parse(cases[i].markdown);
}

writeFileSync(join(outputDir, 'html.json'), JSON.stringify(html));
