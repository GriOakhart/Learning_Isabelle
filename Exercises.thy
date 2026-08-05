theory Exercises
  imports Main Chapter_1

begin

text \<open>Exercise 2.1\<close>

value "1 + (2 :: nat)"
  \<comment> \<open>"3" :: "nat"\<close>

value "1 + (2 :: int)"
  \<comment> \<open>"3" :: "int"\<close>

value "1 - (2 :: nat)"
  \<comment> \<open>"0" :: "nat"
    on type nat, subtraction is truncated: if the
    subtrahend is larger than the minuend, the result is 0 rather than
    a negative number (which does not exist in nat)\<close>

value "1 - (2 :: int)"
  \<comment> \<open>"- 1" :: "int"\<close>

text \<open>Exercise 2.2\<close>

(*add is associative*)
lemma add_assoc: "add (add x y) z = add x (add y z)"
  apply(induction x)
   apply(auto)
  done

lemma add_03 [simp]: "add m (Suc n) = Suc (add m n)"
  apply(induction m)
   apply(auto)
  done  \<comment> \<open>required by the 2nd subgoal in law of commutative\<close>

(*add is commutative*)
lemma add_comm: "add x y = add y x"
  apply(induction x)
   apply(auto)
  done

(*define double in recursive method*)
fun double :: "nat \<Rightarrow> nat" where
  "double 0 = 0"
| "double (Suc m) = Suc (Suc (double m))"

(*prove the equivalence of double and add*)
lemma double_01: "double m = add m m"
  apply(induction m)
   apply(auto)
  done

end