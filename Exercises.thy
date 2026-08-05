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

text \<open>Exercise 2.3\<close>

fun count_01 :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count_01 m Nil = 0"
| "count_01 m (x # xs) = (if m = x then Suc (count_01 m xs) else count_01 m xs)"
  \<comment> \<open>On the right-hand side of a fun equation,
      bare if \<dots> then \<dots> else \<dots> does not parse.
      The conditional must be wrapped in parentheses
      so the whole expression is one term.\<close>

(*
  INVALID: Isabelle’s fun package requires linear patterns:
  each variable may occur only once on the left.
fun count_02 :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count_02 m Nil = 0"
| "count_02 m (m # xs) = Suc (count_02 m xs)" \<comment> \<open>twice here\<close>
| "count_02 m (_ # xs) = count_02 m xs"
*)

lemma count_03: "count_01 m xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done

text \<open>Exercise 2.4\<close>

(*append an element to the end of the list*)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc Nil m = m # Nil"
| "snoc (x # xs) m = x # snoc xs m"

value "snoc [(2::nat), 4, 6] 5"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse Nil = Nil"
| "reverse (x # xs) = snoc (reverse xs) x"

value "reverse (''apple''::string)"

(*from the 2nd subgoal in proof of double_reverse,
  we need a helper lemma of reverse interacting on snoc*)
lemma reverse_snoc [simp]: "reverse (snoc xs m) = m # reverse xs"
  apply(induction xs)
   apply(auto)
  done

lemma double_reverse: "reverse (reverse xs) = xs"
  apply(induction xs)
   apply(auto)
  done
end