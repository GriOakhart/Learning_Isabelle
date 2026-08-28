theory Chapter_5_Ex
  imports Main Chapter_5

begin

section \<open>Exercise 5.1\<close>

(* Check all subexpressions of Plus (N m) (N n) do not exist: *)
fun optimal :: "aexp \<Rightarrow> bool" where
  "optimal (N m) = True"
| "optimal (V x) = True"
| "optimal (Plus (N m) (N n)) = False"
(*
| "optimal (Plus exp1 exp2) = (
    case (exp1, exp2) of
      (N m, N n) \<Rightarrow> False
    | (exp3, exp4) \<Rightarrow> optimal exp3 \<and> optimal exp4)" *)
| "optimal (Plus exp1 exp2) = (optimal exp1 & optimal exp2)"
  \<comment> \<open>Pattern matching on the LHS, not a @{text case} on the RHS:
      the later lemma @{prop "optimal (asimp_const a)"} needs
      @{text "split: aexp.split"}, and a case expression gives the
      simplifier extra equations that can loop.\<close>

lemma "optimal (asimp_const exp)"
  (* apply(induction exp rule: asimp_const.induct)  - this is the same as: *)
  apply(induction exp)
    apply(auto split: aexp.split)
  done

lemma "optimal (asimp_const exp)"
  apply(induction rule: optimal.induct)
        apply(auto)
          \<comment> \<open>goal (1 subgoal):
               1. False\<close>
  oops
  \<comment> \<open>@{text optimal.induct} hooks onto @{const optimal}'s argument,
      i.e. @{term "asimp_const exp"}.  One equation is
      @{prop "optimal (Plus (N m) (N n)) = False"}, so that case
      is @{term False}.  Induct on @{term exp}, not on @{const optimal}.\<close>

lemma "optimal (asimp_const exp)"
  apply(induction rule: asimp_const.induct)  \<comment> \<open>compare with line 25\<close>
    apply(auto split: aexp.split)
      \<comment> \<open>goal (1 subgoal):
           1. \<And>exp1 exp2. optimal exp1 \<Longrightarrow> optimal exp2 \<Longrightarrow> optimal (Plus exp1 exp2)
          - this is a false subgoal, hence cannot be proved\<close>
  oops

section \<open>Exercise 5.2\<close>

(* sum up all the constants in an expersion: *)
fun sum_const :: "aexp \<Rightarrow> val" where
  "sum_const (N m) = m"
| "sum_const (V x) = 0"
| "sum_const (Plus exp1 exp2) = sum_const exp1 + sum_const exp2"

value "sum_const (Plus (N 1) (Plus (V ''x'') (N 2)))"
  \<comment> \<open>"3" :: "int"\<close>

(* eliminate all constants in an experssion,
   if none, then (N 0): *)
fun aexp_skeleton_f :: "aexp \<Rightarrow> aexp" where
  "aexp_skeleton_f (N m) = N 0"
| "aexp_skeleton_f (V x) = V x"
| "aexp_skeleton_f (Plus (N m) exp) = aexp_skeleton_f exp"
| "aexp_skeleton_f (Plus exp (N m)) = aexp_skeleton_f exp"
| "aexp_skeleton_f (Plus exp1 exp2) = Plus (aexp_skeleton_f exp1) (aexp_skeleton_f exp2)"
    \<comment> \<open>@{const Plus} keeps a leftover @{term "N 0"} from a
        constant-only subtree; @{const plus} would drop it.\<close>

value "aexp_skeleton_f (Plus (N 1) (Plus (V ''x'') (N 2)))"
  \<comment> \<open>"V ''x''" :: "aexp"\<close>
value "aexp_skeleton_f (Plus (N 1) (N 2))"
  \<comment> \<open>"N 0" :: "aexp"\<close>
value "aexp_skeleton_f (Plus (Plus (N 1) (N 2)) (V ''x''))"
  \<comment> \<open>"Plus (N 0) (V ''x'')" :: "aexp"
        - neither child is @{text "N _"}, so the last equation
          keeps @{term "N 0"} from @{term "Plus (N 1) (N 2)"}\<close>

definition full_asimp_f :: "aexp \<Rightarrow> aexp" where
  "full_asimp_f exp = plus (aexp_skeleton_f exp) (N (sum_const exp))"

value "full_asimp_f (Plus (N 1) (Plus (V ''x'') (N 2)))"
  \<comment> \<open>"Plus (V ''x'') (N 3)" :: "aexp"\<close>
value "full_asimp_f (Plus (Plus (N 1) (N 2)) (V ''x''))"
  \<comment> \<open>"Plus (Plus (N 0) (V ''x'')) (N 3)" :: "aexp"
        - @{const plus} only sees the top constructors, so the
          buried @{term "N 0"} in the skeleton remains\<close>

fun aexp_skeleton :: "aexp \<Rightarrow> aexp" where
  "aexp_skeleton (N m) = N 0"
| "aexp_skeleton (V x) = V x"
| "aexp_skeleton (Plus (N m) exp) = aexp_skeleton exp"
| "aexp_skeleton (Plus exp (N m)) = aexp_skeleton exp"
| "aexp_skeleton (Plus exp1 exp2) = plus (aexp_skeleton exp1) (aexp_skeleton exp2)"
    \<comment> \<open>                             ^^^^
        Note here, we use plus, rather than Plus here, defined in Chapter_5.thy\<close>

text \<open>To check this, define:\<close>
fun no_constant :: "aexp \<Rightarrow> bool" where
  "no_constant (N m) = False"
| "no_constant (V x) = True"
| "no_constant (Plus exp1 exp2) = (no_constant exp1 \<and> no_constant exp2)"

lemma plus_N0_or_no_constant:
  "(e1 = N 0 \<or> no_constant e1) \<Longrightarrow>
   (e2 = N 0 \<or> no_constant e2) \<Longrightarrow>
   plus e1 e2 = N 0 \<or> no_constant (plus e1 e2)"
  apply(induction e1 e2 rule: plus.induct)
  apply(auto)
  done
  \<comment> \<open>Needed for the last @{const aexp_skeleton} equation: @{const plus}
      either drops @{term "N 0"}, or joins two constant-free trees.\<close>

lemma "aexp_skeleton exp = N 0 \<or> no_constant (aexp_skeleton exp)"
  apply(induction exp rule: aexp_skeleton.induct)
  apply(auto simp: plus_N0_or_no_constant)
  done
  \<comment> \<open>@{text aexp_skeleton.induct} follows the @{text fun} equations.
      The first four cases are immediate; the last uses the lemma above.
      @{text no_constant.induct} would be wrong: the claim is about
      @{term "aexp_skeleton exp"}, not an arbitrary @{const no_constant} term.\<close>
end