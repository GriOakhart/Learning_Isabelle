# Learning_Isabelle

A small [Isabelle/HOL](https://isabelle.in.tum.de/) project for learning formal proofs, following early chapters of the Isabelle tutorial (types, recursive functions, induction, and exercises).

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
| `Chapter_1.thy` | Main learning theory: `bool`, `nat`, `list`, `my_map`, and related lemmas |
| `Exercises.thy` | Tutorial exercises (imports `Chapter_1`) |
| `Tests.thy` | Playground for temporary experiments (`Complex_Main` for `int`/`real`) |
| `document/root.tex` | LaTeX root (for PDF document generation if enabled; currently `document = false` in `ROOT`) |

Session theories (from `ROOT`): `Tests`, `Chapter_1`, `Exercises`.

## Content sketch

### `Chapter_1.thy`

| Section | Topics |
|---------|--------|
| 2.2.1 Type `bool` | Pattern-based `conj` |
| 2.2.2 Type `nat` | Recursive `add`, `add_02 [simp]` by induction |
| 2.2.3 Type `list` | Polymorphic `app` / `rev`; lemmas `app_Nil2`, `app_assoc`, `rev_app`; theorem `rev_rev` |
| 2.2.5 | Polymorphic `my_map` with example values |
| 2.2.6 Types `int` and `real` | See `Tests.thy` |

Lemma order matters: `rev_rev` relies on the earlier `[simp]` lemmas for `app` and `rev`.

### `Exercises.thy`

- **Exercise 2.1:** `value` checks contrasting `nat` vs `int` arithmetic (truncated subtraction on `nat`)
- **Exercise 2.2:** `add_assoc`, `add_comm` (via helper `add_03`), recursive `double`, and `double m = add m m`

### `Tests.thy`

Scratch space for short-lived experiments:

- Terminating remainder-style `modular_02` (non-terminating `modular_01` kept commented)
- `int` / `real` / `nat` conversions and typed `floor` / `ceiling` evaluation under `Complex_Main`

## Open in Isabelle/jEdit

```bash
isabelle jedit -d . -l Learning_Isabelle Chapter_1.thy
```

Other theories:

```bash
isabelle jedit -d . -l Learning_Isabelle Exercises.thy
isabelle jedit -d . -l Learning_Isabelle Tests.thy
```
