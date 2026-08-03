theory Tests
  imports Main

begin

text "
  This is the playground for running some
  temporary tests.
"

(*this does not work,
  the function does not terminate when b = 0*)
fun modular_01 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "modular_01 a b = (if a < b then a else modular_01 (a - b) b)"

(*this works, using pattern-match.
  The Suc b pattern guarantees that the second argument is at least 1*)
fun modular_02 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "modular_02 a 0 = a"
| "modular_02 a (Suc b) = (if a < (Suc b) then a else modular_02 (a - (Suc b)) (Suc b))"

end