theory Sample
  imports Main
begin

section \<open>Learning Isabelle — starter theory\<close>

text \<open>
  A small working example to verify the session builds.
  Replace or extend this theory as you learn.
\<close>

definition double :: "nat \<Rightarrow> nat" where
  "double n = n + n"

lemma double_0 [simp]: "double 0 = 0"
  by (simp add: double_def)

lemma double_Suc: "double (Suc n) = Suc (Suc (double n))"
  by (simp add: double_def)

fun sum_to :: "nat \<Rightarrow> nat" where
  "sum_to 0 = 0"
| "sum_to (Suc n) = Suc n + sum_to n"

lemma sum_to_closed_form: "2 * sum_to n = n * Suc n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

end
