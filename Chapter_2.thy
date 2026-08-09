theory Chapter_2
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

(* Basic algebraic properties of add (also Exercise 2.2).
   Placed here so later material in this theory (e.g. itadd) can use them
   without a cyclic import of Chapter_2_Ex. *)

lemma add_assoc: "add (add x y) z = add x (add y z)"
  apply(induction x)
   apply(auto)
  done

lemma add_03 [simp]: "add m (Suc n) = Suc (add m n)"
  apply(induction m)
   apply(auto)
  done  \<comment> \<open>required by the 2nd subgoal of add_comm, and by itadd_01\<close>

lemma add_comm: "add x y = add y x"
  apply(induction x)
   apply(auto)
  done

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

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"
  \<comment> \<open>Tip and Node are constructors. A tree is either a bare leaf,
      or a node with three parts: a left subtree, a value, and a right subtree.\<close>

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror Tip = Tip"
| "mirror (Node ltree m rtree) = Node (mirror rtree) m (mirror ltree)"
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

text \<open>Section 2.3.4 Recursive Functions\<close>

fun div2 :: "nat \<Rightarrow> nat" where
  "div2 0 = 0"
| "div2 (Suc 0) = 0"
| "div2 (Suc (Suc m)) = Suc (div2 m)"
  \<comment> \<open>div2 is not one equation per datatype constructor of nat (0 and Suc).
      It has two base cases (0 and Suc 0) and recurses by stripping two Suc
      constructors at once. fun still proves termination and derives a custom
      induction rule div2.induct that mirrors this recursion schema — unlike
      ordinary structural induction on nat, which only has cases for 0 and Suc.\<close>

lemma div2_01: "div2 m = m div 2"
  apply(induction m rule: div2.induct)
    apply(auto)
  done
  \<comment> \<open>Computation induction: we induct with div2.induct, which follows the
      recursive definition of div2 (cases 0, Suc 0, and Suc (Suc m) with IH
      for m), not the structure of the datatype nat. The three goals match the
      three defining equations, so auto finishes immediately.\<close>

(* Structural induction on the datatype needs a stronger intermediate claim:
   the plain IH "div2 m = m div 2" is too weak for the step on Suc m, because
   div2 peels two constructors and would need a fact about the predecessor of m. *)
lemma div2_02: "div2 m = m div 2"
  apply(subgoal_tac "div2 m = m div 2 \<and> div2 (Suc m) = Suc m div 2")
   apply(simp)
  apply(induction m)
   apply(auto)
  done
  \<comment> \<open>Structural induction on nat: strengthen the goal so each step carries
      facts about both m and Suc m; then the original claim is the first conjunct.
      Plain apply(induction m) plus case analysis on m is not enough, because the
      recursive call is on the value two steps smaller, not on m itself.\<close>

\<comment> \<open>Heuristic: if f's definition is more than one equation per datatype constructor,
    prove properties of f via f.induct (computation induction). If it is one equation
    per constructor, structural induction and f.induct amount to the same thing.\<close>

text \<open>Section 2.4 Induction Heuristics\<close>

fun itrev_helper :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev_helper Nil ys = ys"
| "itrev_helper (x # xs) ys = itrev_helper xs (x # ys)"
  \<comment> \<open>it reverses its first argument by stacking its elements onto the second argument;
      tail-recursive: it can be compiled into a loop; no stack\<close>

definition itrev :: "'a list \<Rightarrow> 'a list" where
  "itrev xs = itrev_helper xs Nil"

value "itrev [(2::nat), 3, 4, 5]"
  \<comment> \<open>"[5, 4, 3, 2]" :: "nat list"\<close>
value "itrev (''apple''::string)"
  \<comment> \<open>"''elppa''" :: "char list"\<close>

(*
lemma itrev_01: "itrev_helper xs Nil = rev xs"
  apply(induction xs)
   apply(auto)
    goal (1 subgoal):
      1. \<And>a xs.
        itrev_helper xs [] = Chapter_2.rev xs \<Longrightarrow> itrev_helper xs [a] = app (Chapter_2.rev xs) [a]
      the induction assumption is too weak: it specialized to a fixed 2nd argument Nil,
      but the recursive step calls [a] as the 2nd argument, which is different

lemma itrev_01: "itrev_helper xs ys = app (rev xs) ys"
  apply(induction xs)
   apply(auto)
    goal (1 subgoal):
      1. \<And>a xs.
       itrev_helper xs ys = app (Chapter_2.rev xs) ys \<Longrightarrow>
       itrev_helper xs (a # ys) = app (Chapter_2.rev xs) (a # ys)
      the 2nd argument on LHS is ys, while the 2nd argument on RHS is (a # ys),
      which is still weak as above
*)

lemma itrev_01: "itrev_helper xs ys = app (rev xs) ys"
  apply(induction xs arbitrary: ys)
    \<comment> \<open>we need arbitrary on ys\<close>
   apply(auto)
  done

text \<open>
  !!!HINT!!!
  Generalize induction by generalizing all free variables
  (except the induction variable itself).\<close>

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd 0 n = n"
| "itadd (Suc m) n = itadd m (Suc n)"

lemma itadd_01: "itadd m n = add m n"
  apply(induction m arbitrary: n)
    \<comment> \<open>generalize the free variable n\<close>
   apply(auto)
    \<comment> \<open>needs add_03 (and ultimately add_comm's helper):
        add m (Suc n) = Suc (add m n)\<close>
  done

end
