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

lemma add_02 [simp]: "add m 0 = m"
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


\<comment> \<open>!!!THE ARRANGEMENT OF STATEMENTS MATTERS!!!\<close>
lemma app_Nil2 [simp]: "app xs Nil = xs" \<comment> \<open>required by first subgoal in rev_app\<close>
  apply(induction xs)
   apply(auto)
  done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply(induction xs)
   apply(auto)
  done

lemma rev_app [simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
  apply(induction xs) \<comment> \<open>the second subgoal requires associativity of app\<close>
   apply(auto)
  done

(*the purpose of [simp] here is
  to add this theorem rev_rev to ruleset simplification for future use*)
theorem rev_rev [simp]: "rev (rev xs) = xs"
  apply(induction xs) \<comment> \<open>induction on length of the list\<close>
   apply(auto) \<comment> \<open>solve both goals automatically\<close>
  done

\<comment> \<open>
  Summary: rev (rev xs) = xs is proved by induction on xs, but only after
  three [simp] lemmas: app xs Nil = xs, associativity of app, and
  rev (app xs ys) = app (rev ys) (rev xs). Each of those is itself by
  induction + auto; then auto finishes both goals of rev_rev.\<close>

text \<open>section 2.2.5\<close>

fun my_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "my_map f Nil = Nil"
| "my_map f (x # xs) = (f x) # (my_map f xs)"

\<comment> \<open>
  my_map applies a function f to every element of a list, producing a new list
  of the results. Empty list maps to empty list; on Cons, apply f to the head
  and recurse on the tail.
\<close>

value "my_map (\<lambda>n::nat. n + 1) [0, 1, 2]"
  \<comment> \<open>result: [1, 2, 3]\<close>

value "my_map even [0::nat, 1, 2, 3]"
  \<comment> \<open>result: [True, False, True, False]\<close>

value "my_map (\<lambda>x::nat. x * 2) Nil"
  \<comment> \<open>result: []\<close>

value "my_map rev [[1::nat, 2], [3, 4, 5]]"
  \<comment> \<open>result: [[2, 1], [5, 4, 3]]\<close>

text \<open>Section 2.2.6: Types int and real\<close>

(*See Tests.thy*)

text \<open>Section 2.3 Type and Function Definitions\<close>
text \<open>Section 2.3.1 Datatypes\<close>

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"
  \<comment> \<open>Leaf and Node are constructors. A tree is either a bare leaf,
      or a node with three parts: a left subtree, a value, and a right subtree.\<close>

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror Leaf = Leaf"
| "mirror (Node ltree m rtree) = Node (mirror ltree) m (mirror rtree)"
  \<comment> \<open>Parentheses are required: (Node ltree m rtree) groups the constructor
      pattern as a single argument to mirror; (mirror ltree) and (mirror rtree)
      group the recursive calls as arguments to Node.\<close>

lemma mirror_02: "mirror (mirror tree) = tree"
  apply(induction tree)
    \<comment> \<open>apply Constructor twice to move Node to outermost\<close>
   apply(auto)
  done

(*
  datatype 'a option = None | Some 'a
  'a option is a type of optional values: either None (no value),
  or Some x for some value x of type 'a.
*)

fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "lookup Nil m = None"
| "lookup ((x, y) # xs) m = (if x = m then (Some y) else lookup xs m)"
  \<comment> \<open>List of pairs (Cartesian product):
      write ('a * 'b) list in the type (not 'a * 'b list,
      which parses as 'a * ('b list));
      write ((x, y) # xs) in the pattern so (x, y) is one element of the list.\<close>

text \<open>Section 2.3.2 Definitions\<close>

text \<open>
  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  Non-recursive functions can be defined as Definitions.
  Such definitions do not allow pattern matching,
  but only f x_1 \<dots> x_n = t, where f does not occur in t.
  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
\<close>
definition sq :: "nat \<Rightarrow> nat" where
  "sq n = n * n"

text \<open>Section 2.3.3 Abbreviations\<close>

text \<open>
  Abbreviation is only a syntactic sugar.
  definitions need to be expanded explicitly,
  whereas abbreviations are already expanded upon parsing.\<close>
abbreviation sq' :: "nat \<Rightarrow> nat" where
  "sq' n \<equiv> n * n"
(*BEST PRACTICE:
  Default to definition.
  Reach for abbreviation only when you have a clear, conscious reason
  that the pure syntactic-sugar behaviour is what you want.*)
end
