theory Tests
  imports Complex_Main

begin

text "
  This is the playground for running some
  temporary tests.
"

(*
  this does not work,
  the function does not terminate when b = 0
fun modular_01 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "modular_01 a b = (if a < b then a else modular_01 (a - b) b)"
*)

(*this works, using pattern-match.
  The Suc b pattern guarantees that the second argument is at least 1*)
fun modular_02 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "modular_02 a 0 = a"
| "modular_02 a (Suc b) = (if a < (Suc b) then a else modular_02 (a - (Suc b)) (Suc b))"

text \<open>Section 2.2.6: Types int and real\<close>

value "int 5"
value "real 5"
value "real_of_int 5"

value "nat 5"

(*
  These fail with: "Term to be evaluated contains free dictionaries".
  floor / ceiling are type-class operations ('a::floor_ceiling \<Rightarrow> int);
  the bare numeral 5 is polymorphic, so value cannot resolve the
  floor_ceiling dictionary for evaluation.
value "floor 5"
value "ceiling 5"
*)

(* Fix: annotate the numeral with a concrete floor_ceiling type, e.g. real. *)
value "floor (5::real)"
value "ceiling (5::real)"

end