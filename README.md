# Learning_Isabelle

A personal [Isabelle/HOL](https://isabelle.in.tum.de/) workspace for working through the
[Concrete Semantics](http://concrete-semantics.org/) / Isabelle tutorial material on
programming and proving.

**Current coverage:** Chapter 2 (types, recursive functions, datatypes, induction) and the
start of Chapter 3 (sets; ordered trees).

The project is organized so tutorial notes and chapter exercises live in separate theories,
with a small playground for short-lived experiments.

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
| `Chapter_2.thy` | Tutorial notes for Chapter 2 |
| `Chapter_2_Ex.thy` | Chapter 2 exercises (imports `Chapter_2`) |
| `Chapter_3.thy` | Tutorial notes for Chapter 3 (sets) |
| `Chapter_3_Ex.thy` | Chapter 3 exercises (imports `Main` and `Chapter_2` for `'a tree`) |
| `Tests.thy` | Scratch playground (`Complex_Main` for `int` / `real`) |
| `document/root.tex` | LaTeX root (PDF generation currently off: `document = false` in `ROOT`) |

Session theories (build order from `ROOT`):

```text
Tests → Chapter_2 → Chapter_2_Ex → Chapter_3 → Chapter_3_Ex
```

### Dependencies

- `Chapter_2_Ex` → `Chapter_2` (custom `add`, `app`, `rev`, `tree`, `my_map`, …)
- `Chapter_3_Ex` → `Chapter_2` (reuses `'a tree` from Chapter 2)
- `Chapter_3` is independent of Chapter 2 (imports `Main` only)

Algebraic facts about `add` used later in Chapter 2 are proved next to `add` itself, so
`Chapter_2` never needs to import `Chapter_2_Ex`.

**Exercise 2.9** (`itadd` / `itadd m n = add m n`) is kept in `Chapter_2.thy` (section 2.4),
not in `Chapter_2_Ex.thy`, to avoid a cyclic import if Chapter 2 also needed those results.

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
| **2.4** Induction heuristics | Tail-recursive `itrev`; **Exercise 2.9** `itadd` / `itadd_01`; generalizing free variables with `arbitrary` |

Recurring proof habits recorded in this theory:

- Order of `[simp]` lemmas matters (e.g. `app`/`rev` before `rev_rev`).
- Prefer `f.induct` when `fun` equations are not one-per-constructor.
- Strengthen or generalize the IH when the recursive call changes a secondary argument.

### `Chapter_2_Ex.thy` (Chapter 2 exercises)

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
| **2.9** | *(in `Chapter_2.thy`)* iterative `itadd`; `itadd m n = add m n` — kept out of this file to avoid a cyclic import |
| **2.10** | `tree0`, `explode`; node-count formula needs `algebra_simps` |
| **2.11** | Expression type `exp`, Horner `evalp`, `coeffs`; prove `evalp (coeffs e) x = eval e x` |

## Progress — Chapter 3

### `Chapter_3.thy` (tutorial notes)

| Section | Topics |
|---------|--------|
| **3.2** Sets | How `'a set` is axiomatized (not a datatype); comprehension / membership |
| | Finiteness as an inductive predicate (`finite` / `infinite`); list `set` and sample lemmas |
| **3.3** Proof automation | `auto`, `fastforce`, `blast`; `by` as shorthand for `apply`…`done` |
| **3.3.1** Sledgehammer | Example using `metis` with library facts (e.g. `append_eq_conv_conj`) |
| **3.3.2** Arithmetic | Linear arithmetic via `arith` |

### `Chapter_3_Ex.thy` (Chapter 3 exercises)

| Exercise | Summary |
|----------|---------|
| **3.1** | Tree element-set `set`; BST-style `ord`; insert `ins`; `set (ins m t) = {m} ∪ set t` and `ord t ⟹ ord (ins m t)` |
| | Notes on Pure `⟹` vs HOL `⟶` for lemma assumptions |

## `Tests.thy`

Scratch space only — not part of the tutorial narrative:

- Termination notes for remainder-style functions (`modular_02`; non-terminating `modular_01` kept commented)
- `int` / `real` / `nat` conversions and typed `floor` / `ceiling` under `Complex_Main`

## How to work in this project

1. Read/extend notes in `Chapter_N.thy` along the tutorial sections.
2. Solve corresponding problems in `Chapter_N_Ex.thy` (exercises may import earlier chapter theories).
3. Park temporary experiments in `Tests.thy` without cluttering the main theories.
4. Rebuild with `isabelle build -D .` after non-trivial edits.

## Open in Isabelle/jEdit

```bash
isabelle jedit -d . -l Learning_Isabelle Chapter_2.thy
```

Other entry points:

```bash
isabelle jedit -d . -l Learning_Isabelle Chapter_2_Ex.thy
isabelle jedit -d . -l Learning_Isabelle Chapter_3.thy
isabelle jedit -d . -l Learning_Isabelle Chapter_3_Ex.thy
isabelle jedit -d . -l Learning_Isabelle Tests.thy
```
