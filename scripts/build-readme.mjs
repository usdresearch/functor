#!/usr/bin/env node

import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { basename, resolve, join } from 'node:path';
import { spawnSync } from 'node:child_process';

const [texArg = 'usd_functor_reference_implementation.tex', outputArg = 'README.md'] = process.argv.slice(2);
const texPath = resolve(texArg);
const outputPath = resolve(outputArg);
const tex = readFileSync(texPath, 'utf8');
const today = new Intl.DateTimeFormat('en-US', {
  month: 'long',
  day: 'numeric',
  year: 'numeric',
  timeZone: 'UTC',
}).format(new Date());

function fail(message) {
  console.error(message);
  process.exit(1);
}

function extractCommand(source, command) {
  const needle = `\\${command}`;
  const commandStart = source.indexOf(needle);

  if (commandStart === -1) {
    fail(`Missing \\${command}{...} in ${basename(texPath)}.`);
  }

  let index = commandStart + needle.length;
  while (/\s/.test(source[index] ?? '')) {
    index += 1;
  }

  if (source[index] !== '{') {
    fail(`Expected braced argument for \\${command}.`);
  }

  const valueStart = index + 1;
  let depth = 1;

  for (index = valueStart; index < source.length; index += 1) {
    const char = source[index];

    if (char === '\\') {
      index += 1;
      continue;
    }

    if (char === '{') {
      depth += 1;
      continue;
    }

    if (char === '}') {
      depth -= 1;

      if (depth === 0) {
        return source.slice(valueStart, index);
      }
    }
  }

  fail(`Unclosed argument for \\${command}.`);
}

function extractEnvironment(source, environment) {
  const begin = `\\begin{${environment}}`;
  const end = `\\end{${environment}}`;
  const beginIndex = source.indexOf(begin);

  if (beginIndex === -1) {
    fail(`Missing ${begin} in ${basename(texPath)}.`);
  }

  const contentStart = beginIndex + begin.length;
  const endIndex = source.indexOf(end, contentStart);

  if (endIndex === -1) {
    fail(`Missing ${end} in ${basename(texPath)}.`);
  }

  return source.slice(contentStart, endIndex).trim();
}

function stripLatexComments(value) {
  return value.replace(/(^|[^\\])%.*/gm, '$1');
}

function latexTextToPlain(value) {
  return stripLatexComments(value)
    .replace(/\\today/g, today)
    .replace(/\\\\/g, ' ')
    .replace(/\\\s*\n/g, ' ')
    .replace(/\\[a-zA-Z]+\*?(?:\s*\{([^{}]*)\})?/g, (_match, argument) => argument ?? '')
    .replace(/[{}]/g, '')
    .replace(/\s+/g, ' ')
    .trim();
}

function splitDocument(source) {
  const documentMarker = '\\begin{document}';
  const documentIndex = source.indexOf(documentMarker);

  if (documentIndex === -1) {
    fail(`Missing ${documentMarker} in ${basename(texPath)}.`);
  }

  const preamble = source.slice(0, documentIndex);
  const tocIndex = source.indexOf('\\tableofcontents', documentIndex);

  if (tocIndex === -1) {
    fail(`Missing \\tableofcontents in ${basename(texPath)}.`);
  }

  let body = source.slice(tocIndex + '\\tableofcontents'.length);
  const endDocumentIndex = body.indexOf('\\end{document}');

  if (endDocumentIndex !== -1) {
    body = body.slice(0, endDocumentIndex);
  }

  return { preamble, body: body.trim() };
}

function latexDocument(preamble, content) {
  return `${preamble}
\\begin{document}
${content}
\\end{document}
`;
}

function runPandoc(inputPath, outputPath) {
  const result = spawnSync('pandoc', [
    inputPath,
    '--from=latex',
    '--to=gfm',
    '--wrap=none',
    '--output',
    outputPath,
  ], {
    stdio: 'inherit',
  });

  if (result.error) {
    throw result.error;
  }

  if (result.status !== 0) {
    process.exit(result.status ?? 1);
  }
}

function normalizeGithubMath(markdown) {
  const segments = markdown.split(/(^```[\s\S]*?^```$)/gm);

  return segments.map((segment) => {
    if (segment.startsWith('```')) {
      return segment;
    }

    return segment
      .replace(/\\\[((?:.|\n)*?)\\\]/g, (_match, math) => {
        return `\n\n\`\`\`math\n${math.trim()}\n\`\`\`\n\n`;
      })
      .replace(/\\\((.*?)\\\)/g, (_match, math) => {
        const trimmedMath = math.trim();

        if (trimmedMath.includes('`')) {
          return `$${trimmedMath}$`;
        }

        return '$`' + trimmedMath + '`$';
      })
      .replace(/[ \t]+\n\n```math/g, '\n\n```math')
      .replace(/```\n\n[ \t]+/g, '```\n\n');
  }).join('');
}

function shiftHeadings(markdown, levels) {
  let inFence = false;

  return markdown.split('\n').map((line) => {
    if (/^(```|~~~)/.test(line)) {
      inFence = !inFence;
      return line;
    }

    if (inFence) {
      return line;
    }

    return line.replace(/^(#{1,5})(\s+)/, `${'#'.repeat(levels)}$1$2`);
  }).join('\n');
}

function stripInlineMarkup(value) {
  return value
    .replace(/<[^>]*>/g, '')
    .replace(/`([^`]*)`/g, '$1')
    .replace(/\[([^\]]*)\]\([^)]*\)/g, '$1')
    .trim();
}

function githubHeadingSlug(value, seen) {
  const baseSlug = stripInlineMarkup(value)
    .toLowerCase()
    .normalize('NFKD')
    .replace(/[^\p{Letter}\p{Number} _-]/gu, '')
    .trim()
    .replace(/\s+/g, '-');
  const slug = baseSlug || 'section';
  const count = seen.get(slug) ?? 0;
  seen.set(slug, count + 1);
  return count === 0 ? slug : `${slug}-${count}`;
}

function buildContents(markdown) {
  const seen = new Map();
  const entries = [];

  for (const line of markdown.split('\n')) {
    const match = /^(#{2,3})\s+(.+?)\s*$/.exec(line);

    if (!match) {
      continue;
    }

    const level = match[1].length;
    const title = stripInlineMarkup(match[2]);
    const slug = githubHeadingSlug(title, seen);
    const indent = level === 3 ? '  ' : '';
    entries.push(`${indent}- [${title}](#${slug})`);
  }

  if (entries.length === 0) {
    return '';
  }

  return `## Contents

${entries.join('\n')}
`;
}

const title = latexTextToPlain(extractCommand(tex, 'title'));
const author = latexTextToPlain(extractCommand(tex, 'author'));
const date = latexTextToPlain(extractCommand(tex, 'date'));
const abstract = extractEnvironment(tex, 'abstract');
const { preamble, body } = splitDocument(tex);
const tempDir = mkdtempSync(join(tmpdir(), 'usd-readme-'));

try {
  const abstractTexPath = join(tempDir, 'abstract.tex');
  const bodyTexPath = join(tempDir, 'body.tex');
  const abstractMarkdownPath = join(tempDir, 'abstract.md');
  const bodyMarkdownPath = join(tempDir, 'body.md');

  writeFileSync(abstractTexPath, latexDocument(preamble, abstract));
  writeFileSync(bodyTexPath, latexDocument(preamble, body));
  runPandoc(abstractTexPath, abstractMarkdownPath);
  runPandoc(bodyTexPath, bodyMarkdownPath);

  const abstractMarkdown = normalizeGithubMath(readFileSync(abstractMarkdownPath, 'utf8').trim());
  const bodyMarkdown = normalizeGithubMath(shiftHeadings(readFileSync(bodyMarkdownPath, 'utf8').trim(), 1));
  const contents = buildContents(bodyMarkdown);
  const readme = `# ${title}

**Author:** ${author}

**Date:** ${date}

## Abstract

${abstractMarkdown}

${contents}
${bodyMarkdown}
`;

  writeFileSync(outputPath, readme);
} finally {
  rmSync(tempDir, { recursive: true, force: true });
}
