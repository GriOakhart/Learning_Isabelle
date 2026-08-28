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

end