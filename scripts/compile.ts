import { buildReadme } from "./build-readme.ts";

const { execa } = await import("npm:execa@9.6.0");

const texPath = "usd_functor_reference_implementation.tex";
const readmePath = "README.md";

async function run(command: string, args: string[]) {
  await execa(command, args, { stdio: "inherit" });
}

await run("latexmk", [
  "-pdf",
  "-interaction=nonstopmode",
  "-halt-on-error",
  texPath,
]);
await run("latexmk", ["-c", texPath]);
await buildReadme(texPath, readmePath);
