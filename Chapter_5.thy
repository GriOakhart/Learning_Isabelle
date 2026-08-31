theory Chapter_5
  imports Main

begin

section \<open>5.1 Arithmetic Expressions\<close>
subsection \<open>5.1.1 Syntax\<close>

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

term "N 5"
term "V ''y''"
term "Plus (N 5) (V ''y'')"
  \<comment> \<open>better use ''y'' rather than simply y,
      because ''y'' is a string, while y is only 'a\<close>

subsection "5.1.2 Semantics"

text \<open>The semantics, or meaning of an expression, is its value.\<close>

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"
  \<comment> \<open>a mapping from variable names to their current values\<close>

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  \<comment> \<open>given an experssion, given an assignment for the variables,
      function computes the value for the experssion\<close>
  "aval (N m) n = m"
(*| "aval (V x) n = n"*)
| "aval (V x) n = n x"
  \<comment> \<open>n is the state, a function; apply it to x to get x's value\<close>
| "aval (Plus exp1 exp2) n = aval exp1 n + aval exp2 n"

value "aval (Plus (N 3) (V ''x'')) (\<lambda>x. 3)"
term "(\<lambda>(x::aexp). (3::nat))"
term "aval (Plus (N 3) (V x)) (\<lambda>x. 3)"
  \<comment> \<open>state is a function, so here is a lambda term\<close>

text \<open>
  the generic function update notation:
  f(a := b) = (\<lambda>x. if x = a then b else f x)
    - the result is the same as f, except that it maps a to b.

  a         :: vname
  b         :: val
  x         :: vname
  f         :: state
  f(a := b) :: state
\<close>

definition s0 :: state where
  "s0 = (\<lambda>x. 0)"
  \<comment> \<open>assign all vars to 0\<close>
definition s1 :: state where
  "s1 = s0 (''x'' := 7)"
  \<comment> \<open>like s0, except ''x'' is mapped to 7\<close>

value "aval (Plus (V ''x'') (V ''y'')) s0"
  \<comment> \<open>"0" :: "int"\<close>
value "aval (Plus (V ''x'') (V ''y'')) s1"
  \<comment> \<open>"7" :: "int"\<close>
value "aval (Plus (V ''x'') (V ''y'')) (((\<lambda>x. 0)(''x'' := 7))(''y'' := 3))"
  \<comment> \<open>"10" :: "int"\<close>

value "(\<lambda>n::nat. n)(3 := 0)"

subsection \<open>5.1.3 Constant Folding\<close>
text \<open>
  For example, the expression Plus (V ''x'') (Plus (N 3) (N 1))
  is simplified to Plus (V ''x'') (N 4)\<close>

(* this is incorrect: *)
fun asimp_const' :: "aexp \<Rightarrow> aexp" where
  "asimp_const' (N m) = N m"
| "asimp_const' (V x) = V x"
| "asimp_const' (Plus (N m) (N n)) = N (m + n)"
| "asimp_const' (Plus exp1 exp2) = Plus (asimp_const' exp1) (asimp_const' exp2)"
  \<comment> \<open>rebuilds Plus without checking if the simplified children became N\<close>

value "asimp_const' (Plus (N 7) (Plus (V ''x'') (Plus (N 3) (N 5))))"
value "asimp_const' (Plus (Plus (N 1) (N 2)) (N 3))"
  \<comment> \<open>"Plus (N 3) (N 3)" :: "aexp"
      this doesn't work!\<close>

(* the definition from book: *)
fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (N m) = N m"
| "asimp_const (V x) = V x"
| "asimp_const (Plus exp1 exp2) = (
    case (asimp_const exp1, asimp_const exp2) of
      \<comment> \<open>fold if the simplified children are both N\<close>
      (N m, N n) \<Rightarrow> N (m + n)
    | (exp3, exp4) \<Rightarrow> Plus exp3 exp4 )"

thm aexp.split

(* the correctness of asimp_const means that it does not change the semantics: *)
lemma "aval (asimp_const exp) s = aval exp s"
  apply (induction exp)
(*  apply(auto)

goal (1 subgoal):
 1. \<And>exp1 exp2.
       aval (asimp_const exp1) s = aval exp1 s \<Longrightarrow>
       aval (asimp_const exp2) s = aval exp2 s \<Longrightarrow>
       aval
        (case asimp_const exp1 of
         N m \<Rightarrow>
           case asimp_const exp2 of N n \<Rightarrow> N (m + n) | V list \<Rightarrow> Plus (N m) (V list)
           | Plus aexp1 aexp2 \<Rightarrow> Plus (N m) (Plus aexp1 aexp2)
         | V list \<Rightarrow> Plus (V list) (asimp_const exp2)
         | Plus aexp1 aexp2 \<Rightarrow> Plus (Plus aexp1 aexp2) (asimp_const exp2))
        s =
       aval exp1 s + aval exp2 s
*)
    apply (auto split: aexp.split)
  done

text \<open>
  The long case analysis is real, but mechanical, so @{text auto} can do it.

  @{text "induction exp"} follows the datatype: @{const N} and @{const V} are
  immediate; @{const Plus} gets IHs
  @{prop "aval (asimp_const exp1) s = aval exp1 s"} and the same for @{term exp2}.
  @{command fun} already installed the equations of @{const asimp_const} and
  @{const aval} as simp rules, so @{text auto} unfolds both.

  The remaining @{const Plus} goal still has a @{text case} on
  @{term "asimp_const exp1"} and @{term "asimp_const exp2"} (see the
  @{text auto}-only subgoal above).  A human would split on the three
  constructors of each, 9 combinations.  @{thm aexp.split} rewrites
  @{text "P (case e of \<dots>)"} into a conjunction over those constructors;
  @{text "split: aexp.split"} hands that rule to @{text auto}.

  Every branch is then trivial: if both results are @{const N}, fold
  @{term "m + n"} and the IHs identify @{term m} and @{term n} with
  @{term "aval exp1 s"} and @{term "aval exp2 s"}; otherwise rebuild
  @{const Plus}, @{const aval} distributes over it, and the IHs finish.
\<close>

value "asimp_const (Plus (V ''x'') (N 0))"
  \<comment> \<open>"Plus (V ''x'') (N 0)" :: "aexp"
      - this should be folded too\<close>

(* this performs the local optimization: *)
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N m) (N n) = N (m + n)"
| "plus (N m) exp = (if m = 0 then exp else Plus (N m) exp)"
| "plus exp (N m) = (if m = 0 then exp else Plus exp (N m))"
| "plus exp1 exp2 = Plus exp1 exp2"
  \<comment> \<open>not recursive: only the top constructors of the two arguments\<close>

(* Correctness for plus: *)
lemma aval_plus: "aval (plus exp1 exp2) s = aval exp1 s + aval exp2 s"
  apply(induction rule: plus.induct)
              apply(simp_all)
  done

(* this version traverses the term: *)
fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N m) = N m"
| "asimp (V x) = V x"
| "asimp (Plus exp1 exp2) = plus (asimp exp1) (asimp exp2)"
    \<comment> \<open>recursion: simplify both children, then combine with the local plus\<close>

thm Chapter_5.plus.cases

(* Correctness for asimp: *)
lemma "aval (asimp exp) s = aval exp s"
  apply (induction exp)
  \<comment> \<open>goal (1 subgoal):
       1. \<And>exp1 exp2.
             aval (asimp exp1) s = aval exp1 s \<Longrightarrow>
             aval (asimp exp2) s = aval exp2 s \<Longrightarrow>
             aval (Chapter_5.plus (asimp exp1) (asimp exp2)) s = aval exp1 s + aval exp2 s
      need lemma \<open>aval_plus\<close>\<close>
    apply(simp_all add: aval_plus)
  done

section \<open>5.2 Boolean Expressions\<close>

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp
  \<comment> \<open>Note a  comparison of arithmetic expressions for less-than,
      there are no boolean variables in this language\<close>

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
  "bval (Bc v) s = v"
| "bval (Not e) s = (\<not> bval e s)"
| "bval (And e1 e2) s = (bval e1 s \<and> bval e2 s)"
| "bval (Less e1 e2) s = (aval e1 s < aval e2 s)"

subsection \<open>5.2.1 Constant Folding\<close>

text \<open>
  Define optimizing versions of the constructors,
  like we defined plus in 5.1 for constructor Plus:\<close>
fun not :: "bexp \<Rightarrow> bexp" where
  "not (Bc False) = Bc True"
| "not (Bc True) = Bc False"
| "not e = Not e"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  \<comment> \<open>and is a keyword; the quotes make it a legal identifier\<close>
  "and (Bc False) e = Bc False"
| "and e (Bc False) = Bc False"
| "and (Bc True) e = e"
| "and e (Bc True) = e"
| "and e1 e2 = And e1 e2"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "less (N n1) (N n2) = Bc (n1 < n2)"
| "less e1 e2 = Less e1 e2"

fun bsimp :: "bexp \<Rightarrow> bexp" where
  "bsimp (Bc v) = Bc v"
| "bsimp (Not e) = not (bsimp e)"
| "bsimp (And e1 e2) = and (bsimp e1) (bsimp e2)"
| "bsimp (Less e1 e2) = less (asimp e1) (asimp e2)"
  \<comment> \<open>Less holds two aexp, not bexp: asimp them, then rebuild with less\<close>

value "bsimp (Not (Not (Bc True)))"
  \<comment> \<open>"Bc True" :: "bexp"\<close>
end