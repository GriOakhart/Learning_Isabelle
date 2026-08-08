theory Exercises
  imports Main Chapter_1

begin

text \<open>Exercise 2.1\<close>

text \<open>
  The associativity and commutativity of @{const add}
  (and the helper @{thm add_03}) have already been proved in
  @{file \<open>Chapter_1.thy\<close>} next to the definition of @{const add},
  so that later proofs in that theory (e.g. @{thm itadd_01}) can use
  them without a cyclic import of this file.
  Available lemmas: @{thm add_assoc}, @{thm add_comm}, @{thm add_03}.
\<close>

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

text \<open>Exercise 2.5\<close>

fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0"
| "sum_upto (Suc m) = add (sum_upto m) (Suc m)"
  \<comment> \<open>add is defined by us in Chapter_1.thy, not Idabelle built-in,
      so we need the following:\<close>

lemma add_04 [simp]: "add m n = m + n"
  apply(induction m)
   apply(auto)
  done
  \<comment> \<open>or we can directly use + instead of add in the definition of sum_upto\<close>
value "sum_upto 10" \<comment> \<open>"55" :: "nat"\<close>

theorem sum_formula: "sum_upto n = n * (n + 1) div 2"
  apply(induction n)
   apply(auto)
  done

text \<open>Exercise 2.6\<close>

fun sum_list :: "nat list \<Rightarrow> nat" where
  "sum_list Nil = 0"
| "sum_list (x # xs) = x + sum_list xs"
  \<comment> \<open>definition from the question\<close>

fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = Nil"
| "contents (Node ltree m rtree) = m # app (contents ltree) (contents rtree)"

value "contents (Node (Node Tip (1::nat) Tip) 2 (Node Tip 3 Tip))"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
  "sum_tree Tip = 0"
| "sum_tree (Node ltree m rtree) = m + (sum_tree ltree) + (sum_tree rtree)"

value "sum_tree (Node (Node Tip (1::nat) Tip) 2 (Node Tip 3 Tip))"

lemma sum_list_01 [simp]: "sum_list xs + sum_list ys = sum_list (app xs ys)"
  apply(induction xs)
   apply(auto)
  done
  \<comment> \<open>required by 2nd goal in the final proof:
      the relationship of add on sum_list\<close>

lemma sum_tree_01: "sum_tree tree = sum_list (contents tree)"
  apply(induction tree)
   apply(auto)
  done

text \<open>Exercise 2.7\<close>

fun pre_order :: "'a tree \<Rightarrow> 'a list" where
  "pre_order Tip = Nil"
| "pre_order (Node ltree m rtree) = m # (app (pre_order ltree) (pre_order rtree))"
  \<comment> \<open>pre-order: root, then left subtree, then right subtree\<close>

value "pre_order (Node (Node (Node Tip (4::nat) Tip) 2 Tip) 1 (Node Tip 3 Tip))"
  \<comment> \<open>"[1, 2, 4, 3]" :: "nat list"\<close>

fun post_order :: "'a tree \<Rightarrow> 'a list" where
  "post_order Tip = Nil"
| "post_order (Node ltree m rtree) = app (app (post_order ltree) (post_order rtree)) (m # Nil)"
  \<comment> \<open>pre-order: left subtree, then right subtree, then root\<close>

value "post_order (Node (Node (Node Tip (4::nat) Tip) 2 Tip) 1 (Node Tip 3 Tip))"
  \<comment> \<open>"[2, 4, 3, 1]" :: "nat list"\<close>

lemma pre_post: "pre_order (mirror tree) = rev (post_order tree)"
  apply(induction tree)
   apply(auto)
  done
  \<comment> \<open>Caution: user-defined app/rev (Chapter_1) are not the library's @ / List.rev.
      Lemmas proved for app (e.g. app_assoc, rev_app) do not apply to @, so this
      development must stick to app in pre_order/post_order; otherwise auto cannot
      reuse those simp rules in the induction step.\<close>

text \<open>Exercise 2.8\<close>

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse m Nil = Nil"
| "intersperse m (x # Nil) = x # Nil"
| "intersperse m (x # xs) = x # m # (intersperse m xs)"
  \<comment> \<open>more than one equation per Constructor\<close>

value "intersperse (0::nat) [3, 4, 5, 6]"
  \<comment> \<open>"[3, 0, 4, 0, 5, 0, 6]" :: "nat list"\<close>
value "intersperse (0::nat) [3]"
  \<comment> \<open>"[3]" :: "nat list"\<close>
value "intersperse (0::nat) []"
  \<comment> \<open>"[]" :: "nat list"\<close>

lemma map_intersperse: "my_map f (intersperse m xs) = intersperse (f m) (my_map f xs)"
  \<comment> \<open>Mapping f over a list after inserting m between its elements is the same as
      first mapping f over the elements and then inserting f m between them:
      f "commutes" with intersperse; the separator is transformed by f as well.\<close>
  apply(induction xs rule:intersperse.induct)
      \<comment> \<open>computational induction on definition of intersperse\<close>
    apply(auto)
  done

text \<open>Exercise 2.10\<close>

datatype tree0 = Tip | Node tree0 tree0
  \<comment> \<open>Reusing Tip/Node is allowed (Isabelle qualifies them as tree0.Tip /
      tree0.Node vs. tree.Tip / tree.Node), but bare Tip/Node after this
      point resolve to tree0 and thus shadow the constructors of 'a tree.\<close>

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip = 1"
  \<comment> \<open>Tip is a leaf and counts as one node; Exercise 2.10 asks for all
      nodes (inner nodes and leaves), so the base case is 1, not 0.\<close>
| "nodes (Node ltree rtree) = Suc (add (nodes ltree) (nodes rtree))"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 tree = tree"
| "explode (Suc n) tree = explode n (Node tree tree)"

text \<open>
  Failed attempt with @{method auto}: after induction, @{method auto} unfolds
  @{const explode}/@{const nodes} and uses the IH, but then gets stuck on a pure
  arithmetic equation involving @{text "+"}, @{text "*"} and @{text "2^n"}.

  Comparison:
  \begin{itemize}
  \item @{method auto} = light simplification + classical logic (quantifiers,
        connectives, case splits). It is not ``stronger simp''.
  \item @{method simp}/@{method simp_all} rewrite with the current simpset.
  \item @{thm algebra_simps} is a library list of algebraic equations
        (distributivity, @{text "x + x = 2 * x"}, etc.) that must be
        \emph{added} to the simpset; neither method loads it by default.
  \end{itemize}
  Here the leftover goal is term normalization, not a logic puzzle, so
  classical search does not help and plain @{method auto} fails.
\<close>
lemma siz_of_exploding_auto_fails:
  "nodes (explode n tree) = Suc (nodes tree) * (2 ^ n) - 1"
  apply(induction n arbitrary: tree)
  apply(auto)
  \<comment> \<open>Stuck, e.g. roughly:
        2^n + (2^n + (nodes t + nodes t) * 2^n) - 1
      = 2 * 2^n + nodes t * (2 * 2^n) - 1
      Needs algebra_simps; auto does not supply them.\<close>
  oops

lemma siz_of_exploding: "nodes (explode n tree) = Suc (nodes tree) * (2 ^ n) - 1"
  apply(induction n arbitrary: tree)
    \<comment> \<open>the 2nd argument for explode in the induction step changes,
        we must generalize the free variable - tree\<close>
   apply(simp_all add: algebra_simps)
    \<comment> \<open>simp_all rewrites with definitions + algebra_simps (tutorial hint);
        auto simp: algebra_simps would also work, but classical auto is unused.\<close>
  done

text \<open>Exercise 2.11\<close>

datatype exp = Var | Const int | Add exp exp | Mult exp exp
  \<comment> \<open>arithmetic expressions in one variable over integers (type int)\<close>

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var val = val"
| "eval (Const x) val = x"
| "eval (Add x y) val = (eval x val) + (eval y val)"
| "eval (Mult x y) val = (eval x val) * (eval y val)"
  \<comment> \<open>eval e x evaluates expression e at integer value x (the single variable)\<close>

value "eval Var 7"
  \<comment> \<open>"7" :: "int"\<close>

value "eval (Const 5) 99"
  \<comment> \<open>"5" :: "int" — constants ignore the valuation\<close>

value "eval (Add (Mult (Const 2) Var) (Const 3)) 4"
  \<comment> \<open>"11" :: "int" — 2 * 4 + 3 = 11 (tutorial-style example)\<close>

value "eval (Mult (Add Var (Const 1)) (Add Var (Const (-1)))) 5"
  \<comment> \<open>"24" :: "int" — (5 + 1) * (5 + (-1)) = 6 * 4 = 24\<close>

value "eval (Add (Const 0) (Mult Var Var)) (-3)"
  \<comment> \<open>"9" :: "int" — 0 + (-3) * (-3) = 9\<close>

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp Nil val = 0"
| "evalp (x # xs) val = x + (evalp xs val) * val"

value "evalp [] 5"
  \<comment> \<open>"0" :: "int"\<close>

value "evalp [4, 2, -1, 3] 5"
  \<comment> \<open>"364" :: "int"\<close>

(*
fun coeffs_add :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "coeffs_add Nil ys = ys"
| "coeffs_add (x # xs) ys =
    (case ys of
       Nil \<Rightarrow> x # xs
     | y # ys' \<Rightarrow> (x + y) # coeffs_add xs ys')"
        \<comment> \<open>the case-of version\<close>
*)
fun coeffs_add :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
(*"coeffs_add Nil Nil = Nil"*)  \<comment> \<open>covered by the following patterns\<close>
  "coeffs_add Nil ys = ys"
| "coeffs_add xs Nil = xs"
| "coeffs_add (x # xs) (y # ys) = (x + y) # (coeffs_add xs ys)"

fun nat_times_list :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "nat_times_list m Nil = Nil"
| "nat_times_list m (y # ys) = (m * y) # (nat_times_list m ys)"

fun coeffs_mult :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "coeffs_mult Nil ys = Nil"
| "coeffs_mult (x # xs) ys = coeffs_add (nat_times_list x ys) ([0] @ (coeffs_mult xs ys))"
  \<comment> \<open>(a_0 + x p) q = a_0 q + x (p q):
      1. p q - recursive call,
        x (p q) essentially adds an extra o to the head of p q
      2. nat \<times> nat list - a helper fun
      3. coeffs_add\<close>

value "coeffs_mult [1, 2, 3] [4, 5, 6]"
  \<comment> \<open>"[4, 13, 28, 27, 18]" :: "int list"\<close>

fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0, 1]"
| "coeffs (Const x) = [x]"
| "coeffs (Add x y) = coeffs_add (coeffs x) (coeffs y)"
    \<comment> \<open>need fun for adding two lists of coefficients\<close>
| "coeffs (Mult x y) = coeffs_mult (coeffs x) (coeffs y)"
    \<comment> \<open>need fun for multiplying two lists of coefficients\<close>

value "coeffs Var"
  \<comment> \<open>"[0, 1]" :: "int list" — the polynomial x\<close>

value "coeffs (Const 5)"
  \<comment> \<open>"[5]" :: "int list" — constant polynomial 5\<close>

value "coeffs (Add (Mult (Const 2) Var) (Const 3))"
  \<comment> \<open>"[3, 2]" :: "int list" — 3 + 2x\<close>

value "coeffs (Mult (Add Var (Const 1)) (Add Var (Const (-1))))"
  \<comment> \<open>"[- 1, 0, 1]" :: "int list" — (x + 1)(x - 1) = x^2 - 1\<close>

value "coeffs (Add (Const 0) (Mult Var Var))"
  \<comment> \<open>"[0, 0, 1]" :: "int list" — 0 + x \<sqdot> x = x^2\<close>

value "evalp (coeffs (Add (Mult (Const 2) Var) (Const 3))) 4"
  \<comment> \<open>"11" :: "int" — same as eval of that expression at 4\<close>

value "evalp (coeffs (Mult (Add Var (Const 1)) (Add Var (Const (-1))))) 5"
  \<comment> \<open>"24" :: "int" — same as eval of that expression at 5\<close>

value "evalp (coeffs (Add (Const 0) (Mult Var Var))) (-3)"
  \<comment> \<open>"9" :: "int" — same as eval of that expression at -3\<close>

end
