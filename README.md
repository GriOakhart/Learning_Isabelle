# Learning_Isabelle

A small [Isabelle/HOL](https://isabelle.in.tum.de/) project for learning formal proofs.

## Requirements

- Isabelle 2025-2 (or compatible)

## Build

From the parent of this directory (or with an absolute path):

```bash
isabelle build -D /path/to/Learning_Isabelle
```

Or, if your shell has Isabelle on `PATH` and you are in this directory:

```bash
isabelle build -D .
```

## Structure

| Path | Role |
|------|------|
| `ROOT` | Session definition (`Learning_Isabelle`, based on `HOL`) |
| `Sample.thy` | Starter theory with a few example lemmas |
| `document/root.tex` | LaTeX root (for PDF document generation if enabled) |

## Open in Isabelle/jEdit

```bash
isabelle jedit -d . -l Learning_Isabelle Sample.thy
```
