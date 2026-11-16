[![make.fun · markdown-render-speed-02](https://make.fun/badge/markdown-render-speed-02.svg)](https://make.fun/bounty/markdown-render-speed-02?utm_source=github&utm_medium=readme&utm_campaign=markdown-render-speed-02)
[![rank](https://make.fun/badge/markdown-render-speed-02/boothlord/markdown-render-speed/rank.svg)](https://make.fun/bounty/markdown-render-speed-02/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=markdown-render-speed-02)
[![reward](https://make.fun/badge/markdown-render-speed-02/boothlord/markdown-render-speed/reward.svg)](https://make.fun/bounty/markdown-render-speed-02?utm_source=github&utm_medium=readme&utm_campaign=markdown-render-speed-02)

# markdown-entry

A dependency-free Markdown renderer written from scratch for the
markdown-render-speed-02 bounty. Its single module, `parse.js`, exports
`parse(markdown)`, which returns the same HTML that marked 18.1.3 renders
with its default options (GFM on), while spending less CPU time doing it.

`main.ts` is the harness driver: it reads the case set from
`/input/cases.json`, renders every case with `parse`, and writes the HTML
strings, in order, to `/output/html.json`.

No dependencies, no build step: Node 22 runs `main.ts` directly.
