# Learning_Isabelle

A small [Isabelle/HOL](https://isabelle.in.tum.de/) project for learning formal proofs, following early chapters of the Isabelle tutorial (types, recursive functions, and induction).

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
| `Chapter_1.thy` | Main learning theory: `bool` / `nat`, recursive `conj` and `add`, induction lemma `add_02` |
| `Tests.thy` | Playground for temporary experiments (e.g. terminating vs non-terminating `modular` definitions) |
| `document/root.tex` | LaTeX root (for PDF document generation if enabled; currently `document = false` in `ROOT`) |

Session theories (from `ROOT`): `Tests`, `Chapter_1`.

## Content sketch

### `Chapter_1.thy` (sections 2.2.1–2.2.2)

- **Type `bool`:** pattern-based `conj`
- **Type `nat`:** recursive `add`, `value "add 2 3"`, and `lemma add_02: "add m 0 = m"` proved by induction

### `Tests.thy`

Scratch space for short-lived experiments. Currently compares remainder-style functions and how pattern-matching on `Suc b` helps Isabelle accept termination.

## Open in Isabelle/jEdit

```bash
isabelle jedit -d . -l Learning_Isabelle Chapter_1.thy
```

To open the playground instead:

```bash
isabelle jedit -d . -l Learning_Isabelle Tests.thy
```
