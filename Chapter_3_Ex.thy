theory Chapter_3_Ex
  imports Main Chapter_2 Chapter_3

begin

section \<open>Exercise 3.1\<close>

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

section \<open>Exercise 3.2\<close>

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

section \<open>Exercise 3.3\<close>

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl: "star' r x x"
| step: "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma "star' r x y \<Longrightarrow> star r x y"
  apply(induction rule: star'.induct)
   apply(simp_all add: star.intros star_trans)
    \<comment> \<open>note star_trans has been proved, but need to be added here manually\<close>
  done

lemma star'_trans: "star' r y z \<Longrightarrow> star' r x y \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
   apply(assumption)
  apply(metis step)
    \<comment> \<open>note: if th statement is:
        "star' r x y \<Longrightarrow> star' r y z \<Longrightarrow> star' r x z"
        then cannot be proved this way. Why?\<close>
  done

(*Similiarly,*)
lemma "star r x y \<Longrightarrow> star' r x y"
  apply(induction rule: star.induct)
   apply(simp_all add:star'.intros)
  apply(metis star'.intros star'_trans)
    \<comment> \<open>step case: from r x y build star' r x y (refl then step),
        then glue it to star' r y z with star'_trans\<close>
  done

text \<open>
  This lemma and @{prop "star' r x y \<Longrightarrow> star r x y"} are exact duals, and so are
  their proofs: @{const star} grows paths on the left, @{const star'} on the right,
  so in both directions the induction step hands you a single r-step at the "wrong"
  end, which is glued on with the respective transitivity lemma plus a singleton path
  built from refl and step.

  Yet the simp one-liner only closes @{prop "star' r x y \<Longrightarrow> star r x y"}. The reason
  is not logical but operational: simp solves a conditional rule's premises left to
  right and can instantiate an unknown midpoint only by unifying a premise with an
  assumption. @{thm [source] star.step} lists the atomic premise @{prop "r x y"}
  first, which pins the midpoint down before the recursive premise is attempted.
  @{thm [source] star'.step} lists the recursive premise first, so simp meets
  the condition \<open>star' r x ?y\<close> with \<open>?y\<close> unknown and recurses into a runaway
  search. metis performs proof search with backtracking, so premise order does not
  matter to it.

  See Star_Simp_Notes.thy for the full explanation and the experiments.\<close>

section \<open>Exercise 3.4\<close>

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  init: "iter r 0 x x"
| step: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

(* lemma "star r x y \<Longrightarrow> iter r n x y" - need quantifier for n *)
lemma "star r x y \<Longrightarrow> \<exists>n. iter r n x y"
  (* apply(rule exI) *)
    \<comment> \<open>should not instantiate n here, witness ?n must differ per case\<close>
  apply(induction rule: star.induct)
   apply(metis init)
  apply(metis step)
  done

section \<open>Exercise 3.5\<close>

datatype alpha = a | b

(*
inductive S :: "alpha list \<Rightarrow> bool" where
  empty: "S Nil"
| mid: "S xs \<Longrightarrow> S (a # (app xs (b # Nil)))"
| doub: "S xs \<Longrightarrow> S (app xs xs)"

lemma "S [(a::alpha), b]"
  using S.mid[OF S.empty]
  by simp

lemma "S [a, b, a, b]"
  apply (rule S.doub[where xs="[a, b]", simplified])
  apply (rule S.mid[where xs="[]", simplified])
  apply (rule S.empty)
  done

inductive T :: "alpha list \<Rightarrow> bool" where
  empty: "T Nil"
| step: "T xs \<Longrightarrow> T (app xs (a # app xs (b # Nil)))"

lemma "T [a, b, a, a, b, b]"
  apply(rule T.step[of "[a, b]", simplified])
  using T.step[of "Nil"]
  apply(simp add: T.empty)
  done
*)

text \<open>
   Although [a, b, a, a, b, b] is a T-string, it is not an S-string:
   S.mid yields only aaabbb or aababb at length 6, while S.doub would
   require an odd-length S-string. Hence the original definitions are
   incorrect for the intended inclusion T xs \<Longrightarrow> S xs.

   The two Ss and two Ts do not necessarily be identical. They are independent!!! \<close>

inductive S :: "alpha list \<Rightarrow> bool" where
  empty: "S Nil"
| mid: "S xs \<Longrightarrow> S (a # (app xs (b # Nil)))"
| doub: "S xs \<Longrightarrow> S ys \<Longrightarrow> S (app xs ys)"

inductive T :: "alpha list \<Rightarrow> bool" where
  empty: "T Nil"
| step: "T xs \<Longrightarrow> T ys \<Longrightarrow> T (app xs (a # app ys (b # Nil)))"

lemma "T xs \<Longrightarrow> S xs"
  apply(induction rule: T.induct)
   apply(metis S.empty)
  apply(metis S.mid S.doub)
  done

lemma T_app: "T ys \<Longrightarrow> T xs \<Longrightarrow> T (app xs ys)"
  apply(induction arbitrary: xs rule: T.induct)
   apply(simp)
    \<comment> \<open>goal (1 subgoal):
         1. \<And>xs ys xsa.
               T xs \<Longrightarrow>
               (\<And>xsa. T xsa \<Longrightarrow> T (app xsa xs)) \<Longrightarrow>
               T ys \<Longrightarrow> (\<And>xs. T xs \<Longrightarrow> T (app xs ys)) \<Longrightarrow> T xsa \<Longrightarrow> T (app xsa (app xs (a # app ys [b])))\<close>
  (* apply(metis T.step app_assoc) *)
    \<comment> \<open>metis can use an equation in both directions. This finishes the proof. Or:\<close>
  apply(simp only: app_assoc[symmetric])
    \<comment> \<open>simp rules are directed rewrites, applied left-to-right only. And app_assoc is directional.\<close>
  apply(rule T.step)
    \<comment> \<open>split the regrouped goal into the two premises of T.step\<close>
   apply(blast)
    \<comment> \<open>derive T (app xsa xs) from the induction hypothesis and T xsa\<close>
  apply(assumption)
    \<comment> \<open>solve the remaining goal with the assumption T ys\<close>
  done

lemma "S xs \<Longrightarrow> T xs"
  apply(induction rule: S.induct)
    apply(metis T.empty)
   apply(rule T.step[where xs="Nil", simplified])
    apply(simp_all add: T.empty)
      \<comment> \<open>goal (1 subgoal):
           1. \<And>xs ys. S xs \<Longrightarrow> T xs \<Longrightarrow> S ys \<Longrightarrow> T ys \<Longrightarrow> T (app xs ys)\<close>
  apply(simp add: T_app)
  done

text \<open>
  Summary: Repeated nonterminals in SS and TaTb generate independently, so
  their Isabelle rules need separate variables. T is included in S directly by
  rule induction; the converse also needs closure of T under app. Proving that
  closure requires induction on the right T-string and reverse associativity to
  match T.step.\<close>

end