# Learning_Isabelle

A personal [Isabelle/HOL](https://isabelle.in.tum.de/) workspace for working through the
[Concrete Semantics](http://concrete-semantics.org/) / Isabelle tutorial material on
programming and proving.

**Current coverage:** Chapters 2–3 complete; Chapter 4 through section 4.4.7 (Isar
style, case analysis, structural / computation / rule induction, rule inversion,
advanced rule induction) plus exercises 4.1–4.2.

The project is organized so tutorial notes and chapter exercises live in separate theories,
with a small playground for short-lived experiments and companion note theories for
longer digressions (rule induction, `star`/`star'` and `simp`).

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
| `Chapter_3.thy` | Tutorial notes for Chapter 3 |
| `Chapter_3_Ex.thy` | Chapter 3 exercises (imports `Chapter_2` and `Chapter_3`) |
| `Chapter_4.thy` | Tutorial notes for Chapter 4 (Isar) |
| `Chapter_4_Ex.thy` | Chapter 4 exercises |
| `Rule_Induction_Notes.thy` | What rule induction is: last lemma of 4.4.7, least fixed points, computation induction |
| `Star_Simp_Notes.thy` | Why `simp` proves one `star`/`star'` direction and not the other |
| `Tests.thy` | Scratch playground (`Complex_Main` for `int` / `real`) |
| `document/root.tex` | LaTeX root (PDF generation currently off: `document = false` in `ROOT`) |

Session theories (build order from `ROOT`):

```text
Tests → Chapter_2 → Chapter_2_Ex → Chapter_3 → Chapter_3_Ex → Chapter_4 → Chapter_4_Ex → Rule_Induction_Notes → Star_Simp_Notes
```

### Dependencies

- `Chapter_2_Ex` → `Chapter_2` (custom `add`, `app`, `rev`, `tree`, `my_map`, …)
- `Chapter_3` is independent of Chapter 2 (imports `Main` only)
- `Chapter_3_Ex` → `Chapter_2` (`'a tree`, `app`) and `Chapter_3` (`star`, `star_trans`)
- `Chapter_4` and `Chapter_4_Ex` are independent of earlier chapters (import `Main` only; redefine `ev` / `evn` locally)
- `Star_Simp_Notes` → `Chapter_3_Ex` (`star'`, `star'_trans`)
- `Rule_Induction_Notes` → `Chapter_4` (`ev`, `evn`, `ev.induct`)

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
| **3.4** Single-step proofs | Instantiating unknowns with `of` / `where`; `rule`; intro rules; forward proof with `OF` and `dest` |
| **3.5.1** Even numbers | Inductive `ev` vs recursive `evn`; rule induction vs computation induction |
| **3.5.2** Reflexive transitive closure | Inductive `star`; two readings of the curried type; `star_trans` (`metis` vs `simp`) |

### `Chapter_3_Ex.thy` (Chapter 3 exercises)

| Exercise | Summary |
|----------|---------|
| **3.1** | Tree element-set `set`; BST-style `ord`; insert `ins`; `set (ins m t) = {m} ∪ set t` and `ord t ⟹ ord (ins m t)` |
| | Notes on Pure `⟹` vs HOL `⟶` for lemma assumptions |
| **3.2** | Inductive `palindrome`; `function palind` (constructor patterns vs `app`/`@`); `palindrome xs ⟹ rev xs = xs` |
| **3.3** | Right-growing `star'`; equivalence with `star`; `star'_trans`; why `simp` closes only one direction |
| **3.4** | Inductive `iter`; `star r x y ⟹ ∃n. iter r n x y` (do not instantiate `n` before induction) |
| **3.5** | Grammars `S` / `T` on `{a,b}` lists; independent nonterminals need separate variables; `T ⊆ S` by rule induction, converse via `T_app` |

## Progress — Chapter 4

### `Chapter_4.thy` (tutorial notes)

| Section | Topics |
|---------|--------|
| **4.1** Isar by example | Cantor diagonalization; structured proofs |
| **4.1.1** | `this` / `then` / `hence` / `thus`; `using` / `with` |
| **4.1.2** | Structured lemmas: `fixes`, `assumes`, `shows`; null method `proof -` |
| **4.2** Proof patterns | Forward reasoning from `∃` via `obtain` |
| **4.2.2** | Equation / inequation chains with `also` / `finally` / `...`; `calculation` register |
| **4.3.1** | Pattern matching `(is "?L …")`, `?thesis`, `let ?t = …`, fact quotations `‹…›` |
| **4.3.2** | `moreover` / `ultimately` vs `also` / `finally` |
| **4.3.3** | Local lemmas: `have … if … for …` |
| **4.4.1** | Datatype case analysis: `cases` and the `case` idiom (`Nil` / `Cons`) |
| **4.4.2** | Structural induction in Isar; `?case`; implications and `case.prems` / `IH` |
| **4.4.3** | Computation induction (`pair_count.induct`); numbered cases and `"3.IH"(1)` |
| **4.4.4** | Rule induction for inductive `ev` vs recursive `evn` |
| **4.4.5** | Assumption naming: `.IH` / `.hyps` / `.prems`; `induction` vs `induct` |
| **4.4.6** | Rule inversion (`cases` on `ev`); syntactic vs semantic simp matching |
| **4.4.7** | Advanced rule induction: `ev (Suc m) ⟹ ¬ ev m` with `arbitrary`; see `Rule_Induction_Notes.thy` |

### `Chapter_4_Ex.thy` (Chapter 4 exercises)

| Exercise | Summary |
|----------|---------|
| **4.1** | Totality / antisymmetry style lemma on `T` and `A`; several Isar styles (`ccontr`, `classical`, `with`, case split with `next` vs `.`) |
| **4.2** | Split a list into nearly equal halves via `take` / `drop`; even/odd case split, then `moreover`/`ultimately`, then nested `exI` with `force` |

### `Rule_Induction_Notes.thy`

Companion to section 4.4.7 of `Chapter_4.thy`. Rule induction is the elimination
principle for the least fixed point of the operator assembled from the
introduction rules (shown concretely as `ev_Φ` for `ev`). Isabelle writes
`I.induct` by keeping each rule's side conditions and `hyps`, and adding an IH
for every recursive premise — which is why the `evSS` induction case has two
assumptions while the introduction rule has one. Computation induction is the
same idea for a `fun`: cases follow equations, IHs follow recursive calls, and
the induction ranges over the whole domain. For `ev (Suc m) ⟹ ¬ ev m`, `P` is
not the whole lemma but the generalized conclusion `odd_pred`;
`induction "Suc m" arbitrary: m` inlines that generalization.

### `Star_Simp_Notes.thy`

Companion to Exercise 3.3. The two `star`/`star'` directions are logical duals, but
`simp` solves conditional premises left to right and can instantiate an unknown
midpoint only by unifying a premise with an assumption. `star.step` lists the atomic
`r`-premise first, so the midpoint is pinned down; `star'.step` lists the recursive
premise first and the search can diverge. `metis` backtracks, so premise order does
not matter. A swapped-premise copy of `star'.step` makes the mirror `simp` one-liner
succeed.

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
isabelle jedit -d . -l Learning_Isabelle Chapter_4.thy
isabelle jedit -d . -l Learning_Isabelle Chapter_4_Ex.thy
isabelle jedit -d . -l Learning_Isabelle Rule_Induction_Notes.thy
isabelle jedit -d . -l Learning_Isabelle Star_Simp_Notes.thy
isabelle jedit -d . -l Learning_Isabelle Tests.thy
```
