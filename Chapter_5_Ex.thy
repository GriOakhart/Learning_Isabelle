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
(*
| "lval (LET x e1 e2) s = lval e2 (\<lambda>x. lval e1 s)" *)
  \<comment> \<open>first evaluate e1, then bind it to x, to evaluate e2.
      However, this is INCORRECT:
      @{text "\<lambda>x. lval e1 s"} is constant --- the binder shadows the
      @{text vname} and the body ignores it --- so every name maps to
      @{text "lval e1 s"} and the rest of @{text s} is lost.
      Need @{text "s(x := lval e1 s)"}.\<close>
| "lval (LET x e1 e2) s = lval e2 (s(x := lval e1 s))"

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

value "lval (LET ''x'' (Nl 3) (Plusl (Vl ''x'') (Vl ''y'')))
           ((\<lambda>_. 0)(''y'' := 10))"
  \<comment> \<open>"6" :: "int"
        - this yields incorrect answer using the equation in line 332\<close>

fun inline :: "lexp \<Rightarrow> aexp" where
  "inline (Nl m) = aexp.N m"
| "inline (Vl x) = aexp.V x"
| "inline (Plusl e1 e2) = aexp.Plus (inline e1) (inline e2)"
| "inline (LET x e1 e2) = subst x (inline e1) (inline e2)"
  \<comment> \<open>                          ^^
      same @{text vname} as the @{const LET} binder: @{const subst}'s
      first argument is the name to replace, not an expression.
      @{text "inline (Vl x)"} is @{text "aexp.V x"} --- that would be a
      replacement term, not a name.\<close>

(* Correctness of inline for evaluation: *)
lemma "aval (inline exp) s = lval exp s"
  apply (induction exp arbitrary: s rule: inline.induct)
     apply (simp_all add: substitution_lemma)
      \<comment> \<open>substitution lemma should be add manually
      goal (1 subgoal):
       1. \<And>x e1 e2.
             aval (inline e1) s = lval e1 s \<Longrightarrow>
             aval (inline e2) s = lval e2 s \<Longrightarrow>
             aval (inline e2) (s(x := lval e1 s)) =
             lval e2 (s(x := lval e1 s))
      - need to generalize s!
      hence add arbitrary: s in induction\<close>
  done

section \<open>Exercise 5.7\<close>
(*
datatype aexp = N int | V vname | Plus aexp aexp
datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp *)
fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Eq e1 e2 = And (Not (Less e1 e2)) (Not (Less e2 e1))"
    \<comment> \<open>The book asks to show @{text "="} and @{text "\<le>"} are
        definable from the existing @{typ bexp} constructors
        --- not to add constructors or recurse on @{typ aexp}.
        @{const Eq} is a smart constructor: on @{typ int} (a linear order),
        @{text "x = y"} iff @{text "\<not>(x < y) \<and> \<not>(y < x)"}.\<close>

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Le e1 e2 = Not (Less e2 e1)"
    \<comment> \<open>Same idea: @{text "x \<le> y"} iff @{text "\<not>(y < x)"}.\<close>

lemma "bval (Eq e1 e2) s = (aval e1 s = aval e2 s)"
(*  the detailed proof is too crazy...
  apply (simp only: Eq.simps bval.simps)
    \<comment> \<open>@{const Eq} and @{const bval} only --- no order lemmas yet:
         (\<not> aval e1 s < aval e2 s \<and> \<not> aval e2 s < aval e1 s) =
         (aval e1 s = aval e2 s)\<close>
  apply (rule iffI)
   apply (erule conjE)
   apply (drule leI)+
     \<comment> \<open>@{thm leI}: @{text "\<not> x < y"} implies @{text "y \<le> x"}, so
          @{text "e2 \<le> e1"} and @{text "e1 \<le> e2"}\<close>
   apply (rule antisym)
    apply assumption
    apply assumption
  apply (rule conjI)
   apply (erule ssubst[where P="\<lambda>x. \<not> x < aval e2 s"])
   apply (rule less_irrefl)
  apply (erule ssubst[where P="\<lambda>x. \<not> aval e2 s < x"])
  apply (rule less_irrefl)
  done *)
  by auto

lemma "bval (Le e1 e2) s = (aval e1 s \<le> aval e2 s)"
  by auto

section \<open>Exercise 5.8\<close>

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
  "ifval (Bc2 v) s = v"
| "ifval (If e1 e2 e3) s = (if (ifval e1 s) then (ifval e2 s) else (ifval e3 s))"
| "ifval (Less2 e1 e2) s = (aval e1 s < aval e2 s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
  "b2ifexp (Bc v) = (Bc2 v)"
| "b2ifexp (Not e) = (If (b2ifexp e) (Bc2 False) (Bc2 True))"
  \<comment> \<open>note: exp = if (exp) then True else False, - exp is also boolean expression
      - evaluated to True/False\<close>
| "b2ifexp (And e1 e2) = (If (b2ifexp e1) (If (b2ifexp e2) (Bc2 True) (Bc2 False)) (Bc2 False))"
(* | "b2ifexp (Less e1 e2) = (Less2 (b2ifexp e1) (b2ifexp e2))" *)
    \<comment> \<open>arguments for both Less and Less2 are aexp!\<close>
| "b2ifexp (Less e1 e2) = (Less2 e1 e2)"

(* Correctness for b2ifexp: *)
lemma "ifval (b2ifexp e) s = bval e s"
  apply (induction e rule: b2ifexp.induct)
     apply (simp_all)
  done

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
  "if2bexp (Bc2 v) = (Bc v)"
| "if2bexp (If e1 e2 e3) =
    (And (Not (And (if2bexp e1) (Not (if2bexp e2)))) (Not (And (Not (if2bexp e1)) (Not (if2bexp e3)))))"
  \<comment> \<open>(if p then q else r) = (p \<rightarrow> q) \<and> (\<not>p \<rightarrow> r)\<close>
| "if2bexp (Less2 e1 e2) = (Less e1 e2)"

(* Correctness for if2bexp: *)
lemma "bval (if2bexp e) s = ifval e s"
  apply (induction e rule: if2bexp.induct)
    apply (simp_all)
  done

section \<open>Exercise 5.9\<close>
text \<open>purely boolean expression\<close>

datatype pbexp = VAR vname | NEG pbexp | AND pbexp pbexp | OR pbexp pbexp
(* where variables range over values of type bool. *)

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
  \<comment> \<open>the original state is vname \<Rightarrow> val, not fits here\<close>
  "pbval (VAR x) s = s x"
| "pbval (NEG e) s = (\<not> pbval e s)"
| "pbval (AND e1 e2) s = (pbval e1 s \<and> pbval e2 s)"
| "pbval (OR e1 e2) s = (pbval e1 s \<or> pbval e2 s)"

(* check whether a boolean expression is in NNF (negation normal form): *)
fun is_nnf :: "pbexp \<Rightarrow> bool" where
  "is_nnf (VAR x) = True"
| "is_nnf (NEG (VAR x)) = True"
| "is_nnf (NEG e) = False"
| "is_nnf (AND e1 e2) = (is_nnf e1 \<and> is_nnf e2)"
| "is_nnf (OR e1 e2) = (is_nnf e1 \<and> is_nnf e2)"

value "is_nnf (NEG (VAR x))"
  \<comment> \<open>"True" :: "bool"\<close>
value "is_nnf (NEG (NEG (VAR x)))"
  \<comment> \<open>"False" :: "bool"\<close>

(* convert a pbexp into NNF by pushing: *)
fun nnf :: "pbexp \<Rightarrow> pbexp" where
  "nnf (VAR x) = (VAR x)"
| "nnf (NEG (VAR x)) = (NEG (VAR x))"
  \<comment> \<open>pushing cases:\<close>
| "nnf (NEG (NEG e)) = nnf e"
| "nnf (NEG (AND e1 e2)) = (OR (nnf (NEG e1)) (nnf (NEG e2)))"
  \<comment> \<open>Recur as @{text "nnf (NEG ei)"}, not @{text "NEG (nnf ei)"}:
      De Morgan leaves a @{const NEG} on each child; those leftovers
      still have to be pushed inward.\<close>
| "nnf (NEG (OR e1 e2)) = (AND (nnf (NEG e1)) (nnf (NEG e2)))"
  \<comment> \<open>other cases: (not pushing)\<close>
| "nnf (AND e1 e2) = AND (nnf e1) (nnf e2)"
| "nnf (OR e1 e2) = OR (nnf e1) (nnf e2)"

(* nnf preserves the value: *)
lemma "pbval (nnf e) s = pbval e s"
  apply (induction e rule: nnf.induct)
        apply (simp_all)
  done

(* nnf returns a NNF: *)
lemma "is_nnf (nnf e)"
  apply (induction e rule: nnf.induct)
        apply (simp_all)
  done

(* DNF = NNF and no OR occurs below an AND: *)
fun is_dnf :: "pbexp \<Rightarrow> bool" where
  "is_dnf (VAR x) = True"
| "is_dnf (NEG (VAR x)) = True"
| "is_dnf (NEG e) = False"
  \<comment> \<open>Immediate @{const OR} child of @{const AND}: rejected.
      A deeper @{const OR} is caught by an inner @{const AND}
      (or by @{const NEG} of a non-variable, which is not NNF).\<close>
| "is_dnf (AND (OR e1 e2) e3) = False"
| "is_dnf (AND e1 (OR e2 e3)) = False"
  \<comment> \<open>Safe to recurse: neither child is an @{const OR}, so any
      leftover @{const OR} sits under a nested @{const AND}.\<close>
| "is_dnf (AND e1 e2) = (is_dnf e1 \<and> is_dnf e2)"
  \<comment> \<open>@{const OR} may sit above @{const AND}; just check the children.\<close>
| "is_dnf (OR e1 e2) = (is_dnf e1 \<and> is_dnf e2)"

(* Incomplete converter: a 4-way @{text case} only splits the
   outermost @{const OR} of each converted child. *)
fun dnf_of_nnf_incorrect :: "pbexp \<Rightarrow> pbexp" where
  "dnf_of_nnf_incorrect (VAR x) = (VAR x)"
| "dnf_of_nnf_incorrect (NEG e) = (NEG e)"
| "dnf_of_nnf_incorrect (AND e1 e2) = (
    case (dnf_of_nnf_incorrect e1, dnf_of_nnf_incorrect e2) of
      \<comment> \<open>Convert the children first, then match their roots.
          Nested disjunctions are never walked, so an inner
          @{const OR} can remain under this @{const AND}.\<close>
      ((OR e3 e4), (OR e5 e6)) \<Rightarrow> (OR (OR (AND e3 e5) (AND e3 e6)) (OR (AND e4 e5) (AND e4 e6)))
    | ((OR e3 e4), e5) \<Rightarrow> (OR (AND e3 e5) (AND e4 e5))
    | (e3, (OR e4 e5)) \<Rightarrow> (OR (AND e3 e4) (AND e3 e5))
    | (e3, e4) \<Rightarrow> (AND e3 e4)
)"
| "dnf_of_nnf_incorrect (OR e1 e2) = (OR (dnf_of_nnf_incorrect e1) (dnf_of_nnf_incorrect e2))"

value "dnf_of_nnf_incorrect (AND (OR (VAR ''x'') (VAR ''y'')) (OR (VAR ''u'') (VAR ''v'')))"
  \<comment> \<open>"OR (OR (AND (VAR ''x'') (VAR ''u'')) (AND (VAR ''x'') (VAR ''v'')))
  (OR (AND (VAR ''y'') (VAR ''u'')) (AND (VAR ''y'') (VAR ''v'')))"
  :: "pbexp"
      Happens to be DNF: each side is a single @{const OR} of literals.\<close>

value "dnf_of_nnf_incorrect (AND (OR (OR (VAR ''a'') (VAR ''b'')) (VAR ''c'')) (VAR ''d''))"
  \<comment> \<open>"OR (AND (OR (VAR ''a'') (VAR ''b'')) (VAR ''d'')) (AND (VAR ''c'') (VAR ''d''))"
  :: "pbexp"
      Not DNF: @{text "AND (OR a b) d"} is left intact.\<close>

(* Push @{const AND} through every top-level @{const OR} in both arguments: *)
fun distribute_AND :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
  "distribute_AND (OR e1 e2) e3 = OR (distribute_AND e1 e3) (distribute_AND e2 e3)"
  \<comment> \<open>Left @{const OR} first, so @{text "distribute_AND (OR _ _) (OR _ _)"}
      splits the left and then the right on the recursive calls.\<close>
| "distribute_AND e1 (OR e2 e3) = OR (distribute_AND e1 e2) (distribute_AND e1 e3)"
| "distribute_AND e1 e2 = AND e1 e2"
  \<comment> \<open>Neither root is @{const OR}. If both arguments are already DNF,
      they contain no @{const OR} at all, so this @{const AND} is a cube.
      @{text dnf_of_nnf} supplies that guarantee by converting first.\<close>

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
  "dnf_of_nnf (VAR x) = (VAR x)"
| "dnf_of_nnf (NEG e) = (NEG e)"
  \<comment> \<open>If the input is NNF, @{text e} is already a variable.\<close>
| "dnf_of_nnf (AND e1 e2) = distribute_AND (dnf_of_nnf e1) (dnf_of_nnf e2)"
  \<comment> \<open>Bottom-up: convert both children to DNF, then distribute
      this @{const AND} over their disjuncts.\<close>
| "dnf_of_nnf (OR e1 e2) = OR (dnf_of_nnf e1) (dnf_of_nnf e2)"
  \<comment> \<open>An @{const OR} of DNFs is already DNF.\<close>

value "dnf_of_nnf (AND (OR (OR (VAR ''a'') (VAR ''b'')) (VAR ''c'')) (VAR ''d''))"
  \<comment> \<open>"OR (OR (AND (VAR ''a'') (VAR ''d'')) (AND (VAR ''b'') (VAR ''d'')))
  (AND (VAR ''c'') (VAR ''d''))"
  :: "pbexp"
      Same nested-OR input, now fully distributed.\<close>

(* distribute_AND preserves the value: *)
lemma dist_val: "pbval (distribute_AND e1 e2) s = ((pbval e1 s) \<and> (pbval e2 s))"
  apply (induction rule: distribute_AND.induct)
              apply (auto)
  done

lemma "pbval (dnf_of_nnf e) s = pbval e s"
  apply (induction e)
     apply (simp_all add: dist_val)
      \<comment> \<open>proof (prove)
          goal (1 subgoal):
           1. \<And>e1 e2.
                 pbval (dnf_of_nnf e1) s = pbval e1 s \<Longrightarrow>
                 pbval (dnf_of_nnf e2) s = pbval e2 s \<Longrightarrow>
                 pbval (distribute_AND (dnf_of_nnf e1) (dnf_of_nnf e2)) s = (pbval e1 s \<and> pbval e2 s)
          - we prove a more generalized lemma for this case\<close>
  done

(* distribution preserves DNF: *)
lemma dist_dnf: "is_dnf e1 \<Longrightarrow> is_dnf e2 \<Longrightarrow> is_dnf (distribute_AND e1 e2)"
  apply (induction e1 e2 rule: distribute_AND.induct)  \<comment> \<open>analog to line 109\<close>
    \<comment> \<open>Not two independent inductions: @{text "f.induct"} for a
        two-argument @{text fun} is computation induction on both
        arguments at once (same hook as @{text "plus.induct"}).
        Name @{text e1} @{text e2}: the goal is an implication, so a
        bare @{text "induction rule: distribute_AND.induct"} latches
        onto the wrong @{const is_dnf} (unlike @{text dist_val},
        whose conclusion is already an equation on
        @{const distribute_AND}).\<close>
              apply (simp_all)
    \<comment> \<open>@{const OR} cases unfold @{text "is_dnf (OR ...)"} and use
        the IHs. Last case is @{const AND} of two non-@{const OR}
        DNFs, so the third @{const is_dnf}/@{const AND} equation
        applies.\<close>
  done

lemma "is_nnf e \<Longrightarrow> is_dnf (dnf_of_nnf e)"
  apply (induction e rule: is_nnf.induct)
        apply (simp_all add: dist_dnf)
          \<comment> \<open>proof (prove)
              goal (1 subgoal):
               1. \<And>e1 e2.
                     is_dnf (dnf_of_nnf e1) \<Longrightarrow>
                     is_dnf (dnf_of_nnf e2) \<Longrightarrow>
                     is_nnf e1 \<and> is_nnf e2 \<Longrightarrow> is_dnf (distribute_AND (dnf_of_nnf e1) (dnf_of_nnf e2))\<close>
  done

end