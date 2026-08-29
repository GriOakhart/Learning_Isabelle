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

(* This shows the correctness of aexp_skeleton: *)
lemma "aexp_skeleton exp = N 0 \<or> no_constant (aexp_skeleton exp)"
  apply(induction exp rule: aexp_skeleton.induct)
  apply(auto simp: plus_N0_or_no_constant)
  done
  \<comment> \<open>@{text aexp_skeleton.induct} follows the @{text fun} equations.
      The first four cases are immediate; the last uses the lemma above.
      @{text no_constant.induct} would be wrong: the claim is about
      @{term "aexp_skeleton exp"}, not an arbitrary @{const no_constant} term.\<close>

definition full_asimp :: "aexp \<Rightarrow> aexp" where
  \<comment> \<open>definition produces the equation full_asimp_def and does not put it in the simp set.\<close>
  "full_asimp exp = plus (aexp_skeleton exp) (N (sum_const exp))"
    \<comment> \<open>plus again, to eliminate if the overall sum is (N 0)\<close>

(* Correctness of full_asimp: *)
lemma "aval (full_asimp exp) s = aval exp s"
  apply (induction exp rule: aexp_skeleton.induct)
          apply (auto simp: full_asimp_def aval_plus split: aexp.split)
            \<comment> \<open>full_asimp_def should be added explicitly and manually, see line 126.\<close>
            \<comment> \<open>from the subgoals we found the need for \<open>aval (plus e1 e2)\<close>,
                which is exactly what lemma \<open>aval_plus\<close> stated.\<close>
  done

section \<open>Exercise 5.3\<close>

(* subst x a e is the result of replacing every occurrence of variable x by a in e: *)
fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst y a (N m) = N m"
| "subst y a (V x) = (if y = x then a else (V x))"
| "subst y a (Plus exp1 exp2) = Plus (subst y a exp1) (subst y a exp2)"

value "subst ''x'' (N 3) (Plus (V ''x'') (V ''y''))"
  \<comment> \<open>"Plus (N 3) (V ''y'')" :: "aexp"\<close>

lemma substitution_lemma: "aval (subst x a exp) s = aval exp (s(x := aval a s))"
  apply (induction exp)  \<comment> \<open>induction on \<open>exp\<close>\<close>
    apply (simp_all)
  done

corollary "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  by (auto simp: substitution_lemma)

section \<open>Exercise 5.4\<close>

datatype aexp2 = N int | V vname | Plus aexp2 aexp2 | Multiply aexp2 aexp2

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> val" where
  "aval2 (N m) n = m"
| "aval2 (V x) n = n x"
| "aval2 (Plus exp1 exp2) n = aval2 exp1 n + aval2 exp2 n"
| "aval2 (Multiply exp1 exp2) n = aval2 exp1 n * aval2 exp2 n"

value "aval2 (Plus (Multiply (V ''x'') (N 3)) (Multiply (N 4) (V ''y'')))
      (((\<lambda>x. 0)(''x'' := 3))(''y'' := 4))"

fun plus2 :: "aexp2 \<Rightarrow> aexp2 \<Rightarrow> aexp2" where
  "plus2 (N m) (N n) = N (m + n)"
| "plus2 (N m) exp = (if m = 0 then exp else Plus (N m) exp)"
| "plus2 exp (N m) = (if m = 0 then exp else Plus exp (N m))"
| "plus2 exp1 exp2 = Plus exp1 exp2"

lemma aval2_plus2: "aval2 (plus2 exp1 exp2) s = aval2 exp1 s + aval2 exp2 s"
  apply(induction rule: plus2.induct)
                      apply(simp_all)
  done

fun multiply2 :: "aexp2 \<Rightarrow> aexp2 \<Rightarrow> aexp2" where
  "multiply2 (N m) (N n) = N (m * n)"
| "multiply2 (N m) exp = (if m = 0 then (N 0) else (if m = 1 then exp else Multiply (N m) exp))"
| "multiply2 exp (N m) = (if m = 0 then (N 0) else (if m = 1 then exp else Multiply exp (N m)))"
| "multiply2 exp1 exp2 = Multiply exp1 exp2"

lemma aval2_multiply2: "aval2 (multiply2 exp1 exp2) s = aval2 exp1 s * aval2 exp2 s"
  apply(induction rule: multiply2.induct)
                      apply(simp_all)
  done

fun asimp2 :: "aexp2 \<Rightarrow> aexp2" where
  "asimp2 (N m) = N m"
| "asimp2 (V x) = V x"
| "asimp2 (Plus exp1 exp2) = plus2 (asimp2 exp1) (asimp2 exp2)"
| "asimp2 (Multiply exp1 exp2) = multiply2 (asimp2 exp1) (asimp2 exp2)"

lemma "aval2 (asimp2 exp) s = aval2 exp s"
  apply (induction exp)
     apply (simp_all add: aval2_plus2 aval2_multiply2)
  done

text \<open>
  A @{const full_asimp}-style gatherer for @{typ aexp2} is a different problem.
  With only @{const Plus}, every @{const N} is an addend, so @{const sum_const}
  plus a skeleton works.  @{const Multiply} puts constants in different roles:
  @{term "Plus (N 1) (Multiply (V x) (N 2))"} is @{text "2x + 1"}, not @{text "x + 3"};
  @{term "Plus (Multiply (N 2) (V x)) (Multiply (N 3) (V x))"} has no free constants
  but should become @{text "5x"}.  A complete simplifier needs a polynomial normal
  form, distributivity, and like-term collection --- a small algebra theory, not
  another homework function.  @{const asimp2} is the intended local layer
  (@{text 0}, @{text 1}, @{text "N * N"}, @{text "N + N"}).\<close>

end