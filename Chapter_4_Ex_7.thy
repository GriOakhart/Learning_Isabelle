theory Chapter_4_Ex_7
  imports Main

begin

text \<open>Exercise 4.7\<close>

(*the followings are from Exercise 3.5:*)
datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
  empty: "S []"
| mid: "S xs \<Longrightarrow> S (a # xs @ (b # Nil))"
| doub: "S xs \<Longrightarrow> S ys \<Longrightarrow> S (xs @ ys)"

(*define by simulation, walking from left to right:*)
fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
  "balanced 0 [] = True"
(* | "balanced (Suc n) [] = False" *)
(* | "balanced 0 (b # ws) = False" *)
    \<comment> \<open>these two cases can be integrated and put at the end,
        note the order of pattern matching\<close>
| "balanced n (a # ws) = balanced (Suc n) ws"
    \<comment> \<open>meet an opening parenthesis, increase the counter by 1\<close>
| "balanced (Suc n) (b # ws) = balanced n ws"
    \<comment> \<open>a closing parenthesis was paired, decrease the counter by 1\<close>
| "balanced _ _ = False"
    \<comment> \<open>leftover opens @{text "balanced (Suc _) []"} and an extra
        close @{text "balanced 0 (b # _)"}\<close>

text \<open>
  The recognizer is meant to satisfy
  @{prop "balanced n w \<longleftrightarrow> S (replicate n a @ w)"}:
  @{text n} unmatched opening parentheses already consumed, @{text w}
  the remaining suffix.  Two failed starts, then the working
  development.

  Prepending @{term "[a, b]"} with @{text S.doub} only ever attaches
  the pair at the left.  Sliding it to an arbitrary split needs a
  separate fact, and @{text S} is not commutative in its arguments.

  Rule induction on @{prop "S (xs @ ys)"} is the wrong hook: @{text mid}
  wraps the whole word, so that particular split is not preserved.
  Induct on the @{text S}-word and quantify over every split
  (@{text arbitrary} on the two halves).
\<close>

lemma S_pair [iff]: "S [a, b]"
  using S.mid[OF S.empty] by simp

lemma S_insert_ab:
  "S u \<Longrightarrow> u = v @ w \<Longrightarrow> S (v @ a # b # w)"
proof (induction arbitrary: v w rule: S.induct)
  case empty
  then show ?case by simp
next
  case (mid u)
    \<comment> \<open>@{text mid} shadows @{text S.mid}; the introduction rule
        must be written @{text S.mid}.  Same for @{text doub}.\<close>
  show ?case
  proof (cases v)
    case Nil
    with mid.prems have "w = a # u @ [b]" by simp
    with mid.hyps have "S w" by (simp add: S.mid)
    then have "S ([a, b] @ w)" by (rule S.doub[OF S_pair])
    with Nil show ?thesis by simp
  next
    case (Cons x v')
    show ?thesis
    proof (cases w rule: rev_cases)
      case Nil
      from mid.hyps have "S (a # u @ [b])" by (rule S.mid)
      then have "S ((a # u @ [b]) @ [a, b])" by (rule S.doub[OF _ S_pair])
      with Nil Cons mid.prems show ?thesis by auto
    next
      case (snoc w' y)
      from Cons mid.prems snoc have "x = a" "y = b" "u = v' @ w'"
        by auto
      then have "S (v' @ a # b # w')" using mid.IH by simp
      then have "S (a # (v' @ a # b # w') @ [b])" by (rule S.mid)
      with Cons snoc \<open>x = a\<close> \<open>y = b\<close> show ?thesis by auto
    qed
  qed
next
  case (doub xs ys)
  from doub.prems consider
      (left) r where "xs = v @ r" "r @ ys = w"
    | (right) r where "xs @ r = v" "ys = r @ w"
    by (auto simp: append_eq_append_conv2)
      \<comment> \<open>the split of @{term "v @ w"} falls inside @{text xs} or
          inside @{text ys}; @{text append_eq_append_conv2} is that
          dichotomy.\<close>
  then show ?case
  proof cases
    case left
    then have "S (v @ a # b # r)" using doub.IH(1) by blast
    then have "S ((v @ a # b # r) @ ys)" using doub.hyps(2) by (rule S.doub)
    with left show ?thesis by simp
  next
    case right
    then have "S (r @ a # b # w)" using doub.IH(2) by blast
    with doub.hyps(1) have "S (xs @ (r @ a # b # w))" by (rule S.doub)
    moreover from right have "v @ a # b # w = xs @ (r @ a # b # w)"
      by simp
    ultimately show ?thesis by simp
  qed
qed

lemma S_ab: "S (xs @ ys) \<Longrightarrow> S (xs @ [a, b] @ ys)"
proof -
  assume "S (xs @ ys)"
  then have "S (xs @ a # b # ys)" by (rule S_insert_ab) simp
  then show ?thesis by simp
qed

lemma balanced_snoc_b [simp]:
  "balanced n w \<Longrightarrow> balanced (Suc n) (w @ [b])"
  by (induction n w rule: balanced.induct) simp_all

lemma balanced_append [simp]:
  "balanced n v \<Longrightarrow> balanced 0 w \<Longrightarrow> balanced n (v @ w)"
  by (induction n v rule: balanced.induct) simp_all

lemma S_imp_balanced0:
  "S w \<Longrightarrow> balanced 0 w"
  by (induction rule: S.induct) simp_all

text \<open>
  @{text balanced.induct} follows the @{text fun} equations, so the
  hook is the pair @{text "(n, w)"}, not @{text w} alone.  The
  @{text b}-equation is where @{text S_insert_ab} is used:
  @{term "replicate (Suc n) a @ b # w"} is @{term "replicate n a"}
  with an adjacent @{term "[a, b]"} inserted.  @{text replicate_app_Cons_same}
  slides one @{text a} across the @{text "@"}.
\<close>

lemma balanced_imp_S:
  "balanced n w \<Longrightarrow> S (replicate n a @ w)"
proof (induction n w rule: balanced.induct)
  case 1
  then show ?case by (simp add: S.empty)
next
  case (2 n w)
  then show ?case
    by (simp add: replicate_app_Cons_same)
next
  case (3 n w)
  then have "S (replicate n a @ w)" by simp
  then have "S (replicate n a @ a # b # w)"
    by (rule S_insert_ab) simp
  then show ?case
    by (simp add: replicate_app_Cons_same[symmetric])
next
  case "4_1"
  then show ?case by simp
next
  case "4_2"
  then show ?case by simp
qed

text \<open>
  The converse inducts on the @{text S}-derivation of
  @{term "replicate n a @ w"}, generalizing @{text n} and @{text w}
  (section 4.4.7).  In the @{text doub} case the left summand cannot
  be a nonempty prefix of the leading @{text a}s: every nonempty
  word of @{text S} ends with @{text b}.  The empty prefix is fine
  and falls through to the right induction hypothesis.
\<close>

lemma S_imp_balanced:
  "S (replicate n a @ w) \<Longrightarrow> balanced n w"
proof (induction "replicate n a @ w" arbitrary: n w rule: S.induct)
  case empty
  then show ?case by simp
next
  case (mid u)
  show ?case
  proof (cases n)
    case 0
    then have "w = a # u @ [b]" using mid by simp
    have "u = replicate 0 a @ u" by simp
    then have "balanced 0 u" using mid by simp
    then have "balanced (Suc 0) (u @ [b])" by simp
    with 0 \<open>w = a # u @ [b]\<close> show ?thesis by simp
  next
    case (Suc k)
    then have "a # u @ [b] = replicate (Suc k) a @ w" using mid by simp
    then have uw: "u @ [b] = replicate k a @ w" by simp
    show ?thesis
    proof (cases w rule: rev_cases)
      case Nil
      have "b \<in> set (u @ [b])" by simp
      moreover from Nil uw have "u @ [b] = replicate k a" by simp
      ultimately have "b \<in> set (replicate k a)" by simp
      then have False by simp
      then show ?thesis ..
    next
      case (snoc z y)
      with uw have "y = b" "u = replicate k a @ z" by auto
      then have "balanced k z" using mid by simp
      with Suc snoc \<open>y = b\<close> show ?thesis by simp
    qed
  qed
next
  case (doub x y)
  have eq: "x @ y = replicate n a @ w" using doub by simp
  then consider
      (left) r where "x = replicate n a @ r" "w = r @ y"
    | (right) r where "x @ r = replicate n a" "y = r @ w"
    by (auto simp: append_eq_append_conv2)
  then show ?case
  proof cases
    case left
    then have "balanced n r" using doub by simp
    moreover have "balanced 0 y" using doub by simp
    ultimately show ?thesis using left by simp
  next
    case right
    then have "n = length x + length r"
      by (metis length_append length_replicate)
    then have "replicate n a = replicate (length x) a @ replicate (length r) a"
      by (simp add: replicate_add)
    with right have "x = replicate (length x) a"
      by simp
    then have "balanced (length x) []" using doub by simp
    show ?thesis
    proof (cases "length x")
      case 0
      then have "x = []" by simp
      with right have "y = replicate n a @ w" by simp
      then show ?thesis using doub by simp
    next
      case (Suc k)
      with \<open>balanced (length x) []\<close> have False by simp
      then show ?thesis ..
    qed
  qed
qed

lemma balanced_S:
  "balanced n w \<longleftrightarrow> S (replicate n a @ w)"
  using balanced_imp_S S_imp_balanced by blast

lemma balanced_insert_ab:
  "balanced n (xs @ a # b # ys) = balanced n (xs @ ys)"
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases x; cases n) simp_all
qed

lemma S_ab_iff: "S (xs @ ys) = S (xs @ [a, b] @ ys)"
  using balanced_S[of 0 "xs @ ys"] balanced_S[of 0 "xs @ [a, b] @ ys"]
  by (simp add: balanced_insert_ab)


end
