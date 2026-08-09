# Learning_Isabelle

A personal [Isabelle/HOL](https://isabelle.in.tum.de/) workspace for working through the
[Concrete Semantics](http://concrete-semantics.org/) / Isabelle tutorial material on
programming and proving — currently focused on **Chapter 2** (types, recursive functions,
datatypes, and induction).

The project is organized so tutorial text lives in one theory, chapter exercises in another,
and short-lived experiments in a playground theory.

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
| `Chapter_2.thy` | Main notes for tutorial Chapter 2 (definitions, examples, key lemmas) |
| `Exercises.thy` | Chapter 2 exercises (imports `Chapter_2`) |
| `Tests.thy` | Scratch playground (`Complex_Main` for `int` / `real`) |
| `document/root.tex` | LaTeX root (PDF generation currently off: `document = false` in `ROOT`) |

Session theories (build order from `ROOT`): `Tests`, `Chapter_2`, `Exercises`.

`Exercises` depends on `Chapter_2` (e.g. custom `add`, `app`, `rev`, `tree`, `my_map`).
Algebraic facts about `add` used later in Chapter 2 are proved next to `add` itself, so
`Chapter_2` never needs to import `Exercises`.

## Progress — Chapter 2

### `Chapter_2.thy` (tutorial notes)

| Section | Topics |
|---------|--------|
| **2.2.1** Type `bool` | Pattern-based `conj` |
| **2.2.2** Type `nat` | Recursive `add`; `add_02`, `add_assoc`, `add_comm` (via `add_03`) |
| **2.2.3** Type `list` | Polymorphic `app` / `rev`; simp chain to `rev_rev` |
| **2.2.5** | Polymorphic `my_map` with sample `value`s |
| **2.2.6** `int` / `real` | Pointers; evaluation experiments live in `Tests.thy` |
| **2.3.1** Datatypes | `'a tree`, `mirror`, `lookup` into `'b option` |
| **2.3.2–2.3.3** | `definition sq` vs `abbreviation sq'` |
| **2.3.4** Recursive functions | `div2`; computation induction (`div2.induct`) vs structural induction |
| **2.4** Induction heuristics | Tail-recursive `itrev` / `itadd`; generalizing free variables with `arbitrary` |

Recurring proof habits recorded in this theory:

- Order of `[simp]` lemmas matters (e.g. `app`/`rev` before `rev_rev`).
- Prefer `f.induct` when `fun` equations are not one-per-constructor.
- Strengthen or generalize the IH when the recursive call changes a secondary argument.

### `Exercises.thy` (Chapter 2 exercises)

| Exercise | Summary |
|----------|---------|
| **2.1** | `nat` vs `int` arithmetic (`value` checks; truncated subtraction on `nat`) |
| **2.2** | Recursive `double`; `double m = add m m` (`add` algebra proved in `Chapter_2`) |
| **2.3** | `count_01`; length bound; note on linear patterns |
| **2.4** | `snoc` / `reverse`; `reverse (reverse xs) = xs` |
| **2.5** | `sum_upto` closed form `n*(n+1) div 2` |
| **2.6** | Tree `contents` / `sum_tree` related via `sum_list` |
| **2.7** | `pre_order` / `post_order`; `pre_order (mirror t) = rev (post_order t)` |
| **2.8** | `intersperse`; commutes with `my_map` via `intersperse.induct` |
| **2.10** | `tree0`, `explode`; node-count formula needs `algebra_simps` |
| **2.11** | Expression type `exp`, Horner `evalp`, `coeffs`; prove `evalp (coeffs e) x = eval e x` |

(Exercise 2.9 is not present in this repo.)

### `Tests.thy`

Scratch space only — not part of the tutorial narrative:

- Termination notes for remainder-style functions (`modular_02`; non-terminating `modular_01` kept commented)
- `int` / `real` / `nat` conversions and typed `floor` / `ceiling` under `Complex_Main`

## How to work in this project

1. Read/extend notes in `Chapter_2.thy` along the tutorial sections.
2. Solve corresponding problems in `Exercises.thy` (it can use definitions from Chapter 2).
3. Park temporary experiments in `Tests.thy` without cluttering the main theories.
4. Rebuild with `isabelle build -D .` after non-trivial edits.

## Open in Isabelle/jEdit

```bash
isabelle jedit -d . -l Learning_Isabelle Chapter_2.thy
```

Other entry points:

```bash
isabelle jedit -d . -l Learning_Isabelle Exercises.thy
isabelle jedit -d . -l Learning_Isabelle Tests.thy
```
