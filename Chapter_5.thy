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
  \<comment> \<open>"10" :: "int"

      more compact notation:
      <''x'' := 7, ''y'' := 3>\<close>
(* <> - is the syntatic sugar for \<lambda>x.0 *)

value "(\<lambda>n::nat. n)(3 := 0)"

end