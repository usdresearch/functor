#!/usr/bin/env node

import { spawnSync } from 'node:child_process';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const texPath = 'usd_functor_reference_implementation.tex';
const readmePath = 'README.md';
const scriptDir = dirname(fileURLToPath(import.meta.url));

function run(command, args) {
  const result = spawnSync(command, args, {
    stdio: 'inherit',
  });

  if (result.error) {
    throw result.error;
  }

  if (result.status !== 0) {
    process.exit(result.status ?? 1);
  }
}

run('latexmk', ['-pdf', '-interaction=nonstopmode', '-halt-on-error', texPath]);
run('latexmk', ['-c', texPath]);
run(process.execPath, [join(scriptDir, 'build-readme.mjs'), texPath, readmePath]);
