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

section \<open>Exercise 5.5\<close>

datatype aexp3 = N int | V vname | Increment vname | Plus aexp3 aexp3

fun aval3 :: "aexp3 \<Rightarrow> state \<Rightarrow> val \<times> state" where
  "aval3 (N m) s = (m, s)"
| "aval3 (V x) s = (s x, s)"
(* | "aval3 (Increment x) s = (s x, s(x := x + 1)))" *)
(* | "aval3 (Increment x) s = (s x, s(x := (Plus (V x) (N 1))))" *)
(* | "aval3 (Increment x) s = (s x, s(x := Suc (s x)))" *)
| "aval3 (Increment x) s = (s x, s(x := s x + 1))"
(* | "aval3 (Plus e1 e2) s = (fst (aval3 e1 s) + fst (aval3 e2 s), s)" *)
    \<comment> \<open>final state should depend on the states returned by aval3 e1 and e2\<close>
(* | "aval3 (Plus e1 e2) s = (fst (aval3 e1 s) + fst (aval3 e2 s), snd (aval3 e2 (snd (aval3 e1 s))))" *)
    \<comment> \<open>still incorrect, see comments below\<close>
(* | "aval3 (Plus e1 e2) s = (fst (aval3 e1 s) + fst (aval3 e2 (snd (aval3 e1 s))), snd (aval3 e2 (snd (aval3 e1 s))))" *)
    \<comment> \<open>this works, but ugly and low-efficient\<close>
| "aval3 (Plus e1 e2) s = (
    case aval3 e1 s of
      (v1, t1) \<Rightarrow> case aval3 e2 t1 of
        (v2, t2) \<Rightarrow> (v1 + v2, t2))"
  \<comment> \<open>Do not pattern-match as @{text "(v1, s1)"}: @{const s1} is already
      a @{typ state} constant in @{file \<open>Chapter_5.thy\<close>}, so the clause
      is read as a constructor pattern and @{command fun} fails.\<close>

value "aval3 (Increment ''x'') ((\<lambda>x. 0)(''x'' := 5))"
  \<comment> \<open>"(5, _)" :: "int \<times> (char list \<Rightarrow> int)"
      @{command value} evaluates via the code generator, then tries to
      rebuild a HOL term.  A state is @{typ "vname \<Rightarrow> val"} --- infinite,
      so no finite term, hence @{text "_"}.  Apply it to inspect (next).\<close>
value "snd (aval3 (Increment ''x'') ((\<lambda>x. 0)(''x'' := 5))) ''x''"
  \<comment> \<open>"6" :: "int"\<close>
value "aval3 (Plus (Increment ''x'') (Increment ''x'')) ((\<lambda>x. 0)(''x'' := 5))"
  \<comment> \<open>"(10, _)" :: "int \<times> (char list \<Rightarrow> int)"
        - here arises another problem:
          when there are multiple increments for the same variable,
          should we apply the side effect immediately when meet one instance,
          or apply them all only after the evaluation for the entire expression?
          i.e. should this expression be evaluated to 10 or 11?

          Immediate, left-to-right (the exercise convention, like Java):
          first @{text "x++"} yields 5 and sets @{text "x = 6"}; the second
          then yields 6 and sets @{text "x = 7"}.  So 11, not 10.
          Line 228 still gets 10 because both @{text fst}s use the original
          @{text s}; @{text e2}'s value must use @{term "snd (aval3 e1 s)"}
          as well (or @{text case}/@{text let}, evaluating each child once).\<close>
value "snd (aval3 (Plus (Increment ''x'') (Increment ''x'')) ((\<lambda>x. 0)(''x'' := 5))) ''x''"
  \<comment> \<open>With line 228 the final @{text x} is 7 (state is threaded).
      The old equation on line 226 discarded updates and left @{text "x = 5"}.\<close>

datatype aexp4 = N int | V vname | Increment vname | Plus aexp4 aexp4 | Divide aexp4 aexp4

fun aval4 :: "aexp4 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
  "aval4 (N m) s = Some (m, s)"
| "aval4 (V x) s = Some (s x, s)"
| "aval4 (Increment x) s = Some (s x, s(x := s x + 1))"
(*
| "aval4 (Plus e1 e2) s = (
    case aval4 e1 s of
      None \<Rightarrow> None |
      Some (v1, t1) \<Rightarrow>
        case aval4 e2 t1 of
          None \<Rightarrow> None |
          Some (v2, t2) \<Rightarrow> Some (v1 + v2, t2))" *)
    \<comment> \<open>@{text "|"} is not scoped by indentation: a @{text "\<Rightarrow>"} term
        stops at the next @{text "|"}.  The inner @{text case} therefore
        only gets @{text "None \<Rightarrow> None"}; @{text "Some (v2, t2)"} is a
        third outer clause --- redundant (covered by @{text "Some (v1, t1)"})
        and the inner @{text case} is incomplete.  Parenthesize the inner
        @{text case}.\<close>
| "aval4 (Plus e1 e2) s = (
    case aval4 e1 s of
      None \<Rightarrow> None
    | Some (v1, t1) \<Rightarrow>
        (case aval4 e2 t1 of
          None \<Rightarrow> None
        | Some (v2, t2) \<Rightarrow> Some (v1 + v2, t2)))"
(*
| "aval4 (Divide e1 e2) s = (
    case aval4 e1 s of
      None \<Rightarrow> None |
      Some (v1, t1) \<Rightarrow>
        case aval4 e2 s of
          None \<Rightarrow> None |
          Some (0, t2) \<Rightarrow> None |  \<comment> \<open>partiality of division: the divider is 0\<close>
          Some (v2, t2) \<Rightarrow> Some (v1 div v2, t2))" *)
| "aval4 (Divide e1 e2) s = (
    case aval4 e1 s of
      None \<Rightarrow> None
    | Some (v1, t1) \<Rightarrow>
        (case aval4 e2 t1 of
          None \<Rightarrow> None
        | Some (v2, t2) \<Rightarrow>
            if v2 = 0 then None else Some (v1 div v2, t2)))"
  \<comment> \<open>Traps:
      parenthesize a nested @{text case} (see @{const Plus} above);
      match @{text "Some (v, t)"}, not a bare pair;
      thread @{text t1} into @{text e2}, not the original @{text s};
      test zero with @{text "if v2 = 0"} --- @{text "Some (0, t2)"} is not a constructor split.\<close>

section \<open>Exercise 5.6\<close>

text \<open>
  The x++ of 5.5 really changes the state that remains after evaluation,
  which is why the return type is val \<times> state (and later option).

  The LET of 5.6 does not leave the binding outside the expression;
  the return type is still a single int.

  One is a side effect, the other is a local scope. They are different extensions.\<close>

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> val" where
  "lval (Nl m) s = m"
| "lval (Vl x) s = s x"
| "lval (Plusl e1 e2) s = lval e1 s + lval e2 s"
| "lval (LET x e1 e2) s = lval e2 (\<lambda>x. lval e1 s)"
  \<comment> \<open>first evaluate e1, then bind it to x, to evaluate e2\<close>

value "lval (LET ''x'' (Nl 3) (Plusl (Vl ''x'') (Nl 1))) ((\<lambda>x. 0)(''x'' := 5))"
  \<comment> \<open>"4" :: "int"
        - the binding hides the outer \<open>x\<close>, so the outer state is never used\<close>
value "lval (LET ''x'' (Plusl (Vl ''x'') (Nl 1)) (Plusl (Vl ''x'') (Vl ''x''))) ((\<lambda>x. 0)(''x'' := 5))"
  \<comment> \<open>"12" :: "int"
        - e1 is evaluated in the original state, so 5+1=6, and e2 is evaluated using ''x'':=6\<close>
value "lval (LET ''x'' (Nl 1) (LET ''x'' (Nl 2) (Vl ''x''))) ((\<lambda>x. 0)(''x'' := 5))"
  \<comment> \<open>"2" :: "int"
        - nesting and shadowing\<close>
value "lval (LET ''x'' (Nl 10) (Plusl (Vl ''x'') (LET ''x'' (Nl 1) (Vl ''x'')))) ((\<lambda>x. 0)(''x'' := 5))"
  \<comment> \<open>"11" :: "int"
        - an inner binding does not affect an outer use of the same name\<close>
end