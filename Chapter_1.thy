theory Chapter_1
  imports Main

begin

text \<open>section 2.2.1 Type bool\<close>

(*datatype bool = True | False*)

fun conj :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "conj True True = True"
| "conj _ _ = False"

text \<open>section 2.2.2 Type nat\<close>

(*datatype nat = 0 | Suc nat*)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n"
| "add (Suc m) n = Suc (add m n)"

value "add 2 3"

lemma add_02: "add m 0 = m"
  apply(induction m)
   apply(auto)
  done

thm add_02

(*the keywords "lemma", "theorem", "corollary", "proposition" are essentially synonyms,
the difference is purely conventional / documentary.*)



end