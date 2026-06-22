const { execa } = await import("npm:execa@9.6.0");

const today = new Intl.DateTimeFormat("en-US", {
  month: "long",
  day: "numeric",
  year: "numeric",
  timeZone: "UTC",
}).format(new Date());

function baseName(path: string) {
  return path.split(/[\\/]/).pop() ?? path;
}

function tempPath(directory: string, fileName: string) {
  return `${directory.replace(/\/$/, "")}/${fileName}`;
}

function fail(message: string): never {
  throw new Error(message);
}

function extractCommand(source: string, command: string) {
  const needle = `\\${command}`;
  const commandStart = source.indexOf(needle);

  if (commandStart === -1) {
    fail(`Missing \\${command}{...}.`);
  }

  let index = commandStart + needle.length;
  while (/\s/.test(source[index] ?? "")) {
    index += 1;
  }

  if (source[index] !== "{") {
    fail(`Expected braced argument for \\${command}.`);
  }

  const valueStart = index + 1;
  let depth = 1;

  for (index = valueStart; index < source.length; index += 1) {
    const char = source[index];

    if (char === "\\") {
      index += 1;
      continue;
    }

    if (char === "{") {
      depth += 1;
      continue;
    }

    if (char === "}") {
      depth -= 1;

      if (depth === 0) {
        return source.slice(valueStart, index);
      }
    }
  }

  fail(`Unclosed argument for \\${command}.`);
}

function extractEnvironment(
  source: string,
  environment: string,
  texPath: string,
) {
  const begin = `\\begin{${environment}}`;
  const end = `\\end{${environment}}`;
  const beginIndex = source.indexOf(begin);

  if (beginIndex === -1) {
    fail(`Missing ${begin} in ${baseName(texPath)}.`);
  }

  const contentStart = beginIndex + begin.length;
  const endIndex = source.indexOf(end, contentStart);

  if (endIndex === -1) {
    fail(`Missing ${end} in ${baseName(texPath)}.`);
  }

  return source.slice(contentStart, endIndex).trim();
}

function stripLatexComments(value: string) {
  return value.replace(/(^|[^\\])%.*/gm, "$1");
}

function latexTextToPlain(value: string) {
  return stripLatexComments(value)
    .replace(/\\today/g, today)
    .replace(/\\\\/g, " ")
    .replace(/\\\s*\n/g, " ")
    .replace(
      /\\[a-zA-Z]+\*?(?:\s*\{([^{}]*)\})?/g,
      (_match, argument) => argument ?? "",
    )
    .replace(/[{}]/g, "")
    .replace(/\s+/g, " ")
    .trim();
}

function splitDocument(source: string, texPath: string) {
  const documentMarker = "\\begin{document}";
  const documentIndex = source.indexOf(documentMarker);

  if (documentIndex === -1) {
    fail(`Missing ${documentMarker} in ${baseName(texPath)}.`);
  }

  const preamble = source.slice(0, documentIndex);
  const tocIndex = source.indexOf("\\tableofcontents", documentIndex);

  if (tocIndex === -1) {
    fail(`Missing \\tableofcontents in ${baseName(texPath)}.`);
  }

  let body = source.slice(tocIndex + "\\tableofcontents".length);
  const endDocumentIndex = body.indexOf("\\end{document}");

  if (endDocumentIndex !== -1) {
    body = body.slice(0, endDocumentIndex);
  }

  return { preamble, body: body.trim() };
}

function latexDocument(preamble: string, content: string) {
  return `${preamble}
\\begin{document}
${content}
\\end{document}
`;
}

async function runPandoc(inputPath: string, outputPath: string) {
  await execa("pandoc", [
    inputPath,
    "--from=latex",
    "--to=gfm",
    "--wrap=none",
    "--output",
    outputPath,
  ], { stdio: "inherit" });
}

function normalizeGithubMath(markdown: string) {
  return mapNonFenceSegments(markdown, normalizeGithubMathSegment);
}

function mapNonFenceSegments(
  markdown: string,
  normalizeSegment: (segment: string) => string,
) {
  return markdown.split(/(^```[\s\S]*?^```$)/gm).map((segment) => {
    if (segment.startsWith("```")) {
      return segment;
    }

    return normalizeSegment(segment);
  }).join("");
}

function normalizeGithubMathSegment(segment: string) {
  const displayNormalized = segment
    .replace(/\$\$([\s\S]*?)\$\$/g, (_match, math) => displayMath(math))
    .replace(/\\\[((?:.|\n)*?)\\\]/g, (_match, math) => displayMath(math))
    .replace(/[ \t]+\n\n```math/g, "\n\n```math")
    .replace(/```\n\n[ \t]+/g, "```\n\n");

  return mapNonFenceSegments(displayNormalized, (inlineSegment) => {
    return inlineSegment
      .replace(/\$`([^`\n]+)`\$/g, (_match, math) => inlineMath(math))
      .replace(/(^|[^$])\$([^$\n]+)\$(?!\$)/g, (_match, prefix, math) => {
        return `${prefix}${inlineMath(math)}`;
      })
      .replace(/\\\((.*?)\\\)/g, (_match, math) => inlineMath(math));
  });
}

function displayMath(math: string) {
  return `\n\n\`\`\`math\n${
    normalizeGithubMathContent(math.trim())
  }\n\`\`\`\n\n`;
}

function inlineMath(math: string) {
  const normalizedMath = normalizeGithubMathContent(math.trim());

  if (normalizedMath.includes("`")) {
    return `$${normalizedMath}$`;
  }

  return "$`" + normalizedMath + "`$";
}

function normalizeGithubMathContent(math: string) {
  return math
    .replace(/\\operatorname\s*\{([^{}]+)\}/g, "\\mathrm{$1}")
    .replace(/\\xleftarrow\s*\{([^{}]*)\}/g, "\\overset{$1}{\\leftarrow}")
    .replace(/\\xrightarrow\s*\{([^{}]*)\}/g, "\\overset{$1}{\\rightarrow}");
}

function shiftHeadings(markdown: string, levels: number) {
  let inFence = false;

  return markdown.split("\n").map((line) => {
    if (/^(```|~~~)/.test(line)) {
      inFence = !inFence;
      return line;
    }

    if (inFence) {
      return line;
    }

    return line.replace(/^(#{1,5})(\s+)/, `${"#".repeat(levels)}$1$2`);
  }).join("\n");
}

function stripInlineMarkup(value: string) {
  return value
    .replace(/<[^>]*>/g, "")
    .replace(/`([^`]*)`/g, "$1")
    .replace(/\[([^\]]*)\]\([^)]*\)/g, "$1")
    .trim();
}

function githubHeadingSlug(value: string, seen: Map<string, number>) {
  const baseSlug = stripInlineMarkup(value)
    .toLowerCase()
    .normalize("NFKD")
    .replace(/[^\p{Letter}\p{Number} _-]/gu, "")
    .trim()
    .replace(/\s+/g, "-");
  const slug = baseSlug || "section";
  const count = seen.get(slug) ?? 0;
  seen.set(slug, count + 1);
  return count === 0 ? slug : `${slug}-${count}`;
}

function buildContents(markdown: string) {
  const seen = new Map<string, number>();
  const entries: string[] = [];

  for (const line of markdown.split("\n")) {
    const match = /^(#{2,3})\s+(.+?)\s*$/.exec(line);

    if (!match) {
      continue;
    }

    const level = match[1].length;
    const title = stripInlineMarkup(match[2]);
    const slug = githubHeadingSlug(title, seen);
    const indent = level === 3 ? "  " : "";
    entries.push(`${indent}- [${title}](#${slug})`);
  }

  if (entries.length === 0) {
    return "";
  }

  return `## Contents

${entries.join("\n")}
`;
}

export async function buildReadme(
  texPath = "usd_functor_reference_implementation.tex",
  outputPath = "README.md",
) {
  const tex = await Deno.readTextFile(texPath);
  const title = latexTextToPlain(extractCommand(tex, "title"));
  const author = latexTextToPlain(extractCommand(tex, "author"));
  const date = latexTextToPlain(extractCommand(tex, "date"));
  const abstract = extractEnvironment(tex, "abstract", texPath);
  const { preamble, body } = splitDocument(tex, texPath);
  const tempDir = await Deno.makeTempDir({ prefix: "usd-readme-" });

  try {
    const abstractTexPath = tempPath(tempDir, "abstract.tex");
    const bodyTexPath = tempPath(tempDir, "body.tex");
    const abstractMarkdownPath = tempPath(tempDir, "abstract.md");
    const bodyMarkdownPath = tempPath(tempDir, "body.md");

    await Deno.writeTextFile(
      abstractTexPath,
      latexDocument(preamble, abstract),
    );
    await Deno.writeTextFile(bodyTexPath, latexDocument(preamble, body));
    await runPandoc(abstractTexPath, abstractMarkdownPath);
    await runPandoc(bodyTexPath, bodyMarkdownPath);

    const abstractMarkdown = normalizeGithubMath(
      (await Deno.readTextFile(abstractMarkdownPath)).trim(),
    );
    const bodyMarkdown = normalizeGithubMath(
      shiftHeadings((await Deno.readTextFile(bodyMarkdownPath)).trim(), 1),
    );
    const contents = buildContents(bodyMarkdown);
    const readme = `# ${title}

**Author:** ${author}

**Date:** ${date}

## Abstract

${abstractMarkdown}

${contents}
${bodyMarkdown}
`;

    await Deno.writeTextFile(outputPath, readme);
  } finally {
    await Deno.remove(tempDir, { recursive: true }).catch(() => undefined);
  }
}

if (import.meta.main) {
  const [
    texPath = "usd_functor_reference_implementation.tex",
    outputPath = "README.md",
  ] = Deno.args;
  await buildReadme(texPath, outputPath);
}
