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

text \<open>section 2.2.3 Type list\<close>

(*Occurrences of nonatomic types on the right-hand side of the equal sign
  must be enclosed in double quotes, as is customary in Isabelle.*)
(*datatype 'a list = Nil | Cons 'a "'a list"*)

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app Nil ys = ys"
| "app (Cons x xs) ys = Cons x (app xs ys)"

value "app [1::nat, 2] [3, 4]"
value "app [''a'', ''b''] [''c'']" \<comment> \<open>this is a char list list\<close>

(*
  this is incorrect, because Cons has type
  'a \<Rightarrow> 'a list \<Rightarrow> 'a list,
  it must accept an element as its first argument
fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev Nil = Nil"
| "rev (Cons x xs) = Cons (rev xs) x"
*)

fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev Nil = Nil"
| "rev (Cons x xs) = app (rev xs) (Cons x Nil)"

value "rev [1::nat, 2, 3]"
value "rev (''hello''::string)"
value "rev [True, False, True]"

end
