theory Chapter_3_Ex
  imports Main Chapter_2

begin

text \<open>Exercise 3.1\<close>

fun set :: "'a tree \<Rightarrow> 'a set" where
  "set Tip = {}"
| "set (Node ltree m rtree) = insert m (set ltree \<union> set rtree)"

fun ord :: "int tree \<Rightarrow> bool" where
  "ord Tip = True"
| "ord (Node ltree m rtree) = (
    ord ltree
  \<and> ord rtree
  \<and> (\<forall>x\<in>set ltree. x < m)
  \<and> (\<forall>y\<in>set rtree. m < y)
)"

(*
fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
  "ins m Tip = Node Tip m Tip"
| "ins m (Node ltree n rtree) = (
    if m = n then
      Node ltree n rtree
    else (
      if m < n then
        ins m ltree - root and other subtrees dropped!
      else
        ins m rtree - same here
    )
)"
*)
fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
  "ins m Tip = Node Tip m Tip"
| "ins m (Node ltree n rtree) = (
    if m = n then
      Node ltree n rtree
    else (
      if m < n then
        Node (ins m ltree) n rtree
      else
        Node ltree n (ins m rtree)
    )
)"

(* Combined form works only with HOL implication:
lemma "... = ... \<and> (ord tree \<longrightarrow> ord (ins m tree))"  — ok: both sides are HOL bool
lemma "... = ... \<and> (ord tree \<Longrightarrow> ord (ins m tree))"  — fails: \<Longrightarrow> is Pure/meta, not HOL
Prefer two separate lemmas (below) so each fact is a clean rule. *)

lemma ins_01 [simp]: "set (ins m tree) = {m} \<union> set tree"
  apply(induction tree)
   apply(simp_all)
  done

lemma ins_02: "ord tree \<Longrightarrow> ord (ins m tree)"
  \<comment> \<open>Top-level: both \<longrightarrow> and \<Longrightarrow> prove with the same script; prefer \<Longrightarrow> (rule form).\<close>
  apply(induction tree)
   apply(simp_all) \<comment> \<open>needs ins_01\<close>
  done

text \<open>
  @{prop "ord tree \<Longrightarrow> ord (ins m tree)"} — Pure/meta implication.
  Assumptions are available in the proof; usable with rule/erule/drule/frule.
  Preferred for top-level lemmas and Isar (@{text "assumes"}/@{text "shows"} is the same idea).

  @{prop "ord tree \<longrightarrow> ord (ins m tree)"} — HOL (object) implication, type @{typ bool}.
  Nestable under @{text "\<and>"}, @{text "\<forall>"}, definitions, etc.
  For rule-style use: mp/impE; simp/auto/blast usually need no conversion.

  Best practice: @{text "\<Longrightarrow>"} (==>) for lemma assumptions; @{text "\<longrightarrow>"} (-->) only
  when implication is part of a larger HOL formula.\<close>

text \<open>Exercise 3.2\<close>

inductive palindrome :: "'a list \<Rightarrow> bool" where
  empty: "palindrome Nil"
| singleton: "palindrome [a]"
| step: "palindrome xs \<Longrightarrow> palindrome (app (a # xs) [a])"
  \<comment> \<open>note: some properties have been proved for app, but not for @\<close>

(*
  INVALID: fun allows only constructor patterns. app is a defined
  function, not a constructor of 'a list (those are Nil and #).
  Contrast evn (Suc (Suc x)) = evn x in Chapter_3: Suc is a constructor,
  so peeling two Sucs is a legal pattern. There is no constructor that
  exposes the last element of a list, so
    palind (app (a # xs) [b]) = ...
  cannot be a fun equation — writing xs @ [b] fails for the same reason.
*)

function palind :: "'a list \<Rightarrow> bool" where
  "palind Nil = True"
| "palind [a] = True"
| "palind (a # b # xs) =
    (a = last (b # xs) \<and> palind (butlast (b # xs)))"
  by pat_completeness auto
termination by (relation "measure length") simp_all
  \<comment> \<open>
    Same idea as the inductive step: compare the two ends and recurse
    on the middle. The patterns are the list constructors ([], singleton,
    length \<ge> 2). The recursive call is on butlast (b # xs), which is not
    a constructor subterm, so fun cannot prove termination. function plus
    measure length works: the middle is shorter by 2.
    Non-recursive alternative: definition palind xs = (rev xs = xs).\<close>

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction rule: palindrome.induct)
    apply(simp_all)
  done

end