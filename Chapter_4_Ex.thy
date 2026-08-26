theory Chapter_4_Ex
  imports Main

begin

text \<open>Exercise 4.1\<close>

lemma
  assumes T: "\<forall>x y. T x y \<or> T y x"
and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
and TA: "\<forall> x y. T x y \<longrightarrow> A x y"
and "A x y"
shows "T x y"
proof (rule ccontr)
  assume "\<not> T x y"
  from this have "T y x" using T by blast
  from this have "A y x" using TA by blast
  from this have "x = y" using A \<open>A x y\<close> by blast
  from this have "T x y" using \<open>T y x\<close> by blast
  from this show False using \<open>\<not> T x y\<close> by blast
qed

lemma
  assumes T: "\<forall>x y. T x y \<or> T y x"
and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
and TA: "\<forall> x y. T x y \<longrightarrow> A x y"
and "A x y"
shows "T x y"
proof (rule ccontr)
  assume "\<not> T x y"
  hence "T y x" using T by blast
  hence "A y x" using TA by blast
  hence "x = y" using A \<open>A x y\<close> by blast
  hence "T x y" using \<open>T y x\<close> by blast
  thus False using \<open>\<not> T x y\<close> by blast
qed

(*
  Same argument, streamlined with Chapter 4 connectives:
  with facts = from facts this (section 4.1.1);
  ?thesis (section 4.3.1);
  classical so the last step is show ?thesis
  rather than deriving T x y and then False.
*)
lemma
  assumes T: "\<forall>x y. T x y \<or> T y x"
and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
and TA: "\<forall> x y. T x y \<longrightarrow> A x y"
and "A x y"
shows "T x y"
proof (rule classical)
  assume "\<not> T x y"
  with T have "T y x" by blast
  with TA have "A y x" by blast
  with A \<open>A x y\<close> have "x = y" by blast
  with \<open>T y x\<close> show ?thesis by blast
qed

(* same contradiction, intermediates left to blast *)
lemma
  assumes T: "\<forall>x y. T x y \<or> T y x"
and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
and TA: "\<forall> x y. T x y \<longrightarrow> A x y"
and "A x y"
shows "T x y"
proof (rule classical)
  assume "\<not> T x y"
  with assms show ?thesis by blast
qed

lemma
  assumes T: "\<forall>x y. T x y \<or> T y x"
and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
and TA: "\<forall> x y. T x y \<longrightarrow> A x y"
and "A x y"
shows "T x y"
proof -
  from T have "T x y \<or> T y x" by blast
  then show ?thesis
  proof
    assume "T x y"
    thus ?thesis .
      \<comment> \<open>!!!IMPORTANT!!!
          "." finishes this case (by assumption). Without it, thus opens a
          nested proof and next is parsed there, not as the T y x case.\<close>
  next
    assume "T y x"
    with TA have "A y x" by blast
    with A \<open>A x y\<close> have "x = y" by blast
      \<comment> \<open>needs A x y as well as A; x = y alone is not the thesis.\<close>
    with \<open>T y x\<close> show ?thesis by blast
  qed
qed

text \<open>Exercise 4.2\<close>

(*the following built-in functions are needed*)
term take
thm take_def
thm take.simps

term drop
thm drop_def
thm drop.simps

(*this is an analog which came up in my mind:*)
lemma
  fixes m :: nat
  shows "\<exists>p q. m = p + q \<and> (p = q \<or> p = q + 1)"
proof -
  have "even m \<or> odd m" by simp
    \<comment> \<open>then show ?thesis proof case-splits this disjunction (disjE):
        (P \<or> Q) \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R
        with P = even m, Q = odd m, R = ?thesis.
        Bare P \<or> Q \<Longrightarrow> R is not the rule.\<close>
  then show ?thesis
  proof
    assume "even m"
    then obtain k where "m = 2 * k" by (rule evenE)
    then have "m = k + k \<and> (k = k \<or> k = k + 1)" by simp
    then show ?thesis by blast
  next
    assume "odd m"
    then obtain k where "m = 2 * k + 1" by (rule oddE)
    then have "m = (k + 1) + k \<and> (k + 1 = k \<or> k + 1 = k + 1)" by simp
    then show ?thesis by blast
  qed
qed

(*the exact lemma required in this exercise:*)
lemma
  fixes xs :: "'a list"
  shows "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof -
  have "even (length xs) \<or> odd (length xs)" by simp
  then show ?thesis
  proof
    assume "even (length xs)"
    then obtain k where "length xs = 2 * k" by (rule evenE)
    then have "xs = (take k xs) @ (drop k xs) \<and> (length (take k xs) = length (drop k xs) \<or> length (take k xs) = length (drop k xs) + 1)" by simp
    then show ?thesis by blast
  next
    assume "odd (length xs)"
    then obtain k where "length xs = 2 * k + 1" by (rule oddE)
    then have "xs = (take (k+1) xs) @ (drop (k+1) xs) \<and> (length (take (k+1) xs) = length (drop (k+1) xs) \<or> length (take (k+1) xs) = length (drop (k+1) xs) + 1)" by simp
    then show ?thesis by blast
  qed
qed

text \<open>
  Tutorial Exercise 4.2: same lemma, in the form the author asks for.
  Witnesses are take/drop (the hint). The two facts are combined with
  moreover/ultimately as in \<section>4.3.2; ?thesis is \<section>4.3.1.
  append_take_drop_id, length_take and length_drop are already simp rules,
  so they must not be added again.
\<close>
lemma "\<exists>ys zs. xs = ys @ zs \<and>
          (length ys = length zs \<or> length ys = length zs + 1)"
proof -
  let ?ys = "take ((length xs + 1) div 2) xs"
  let ?zs = "drop ((length xs + 1) div 2) xs"
    \<comment> \<open>actually we do not need to split cases to even and odd at all!\<close>
  have "xs = ?ys @ ?zs"
    by simp
  moreover have "length ?ys = length ?zs \<or> length ?ys = length ?zs + 1"
    by simp arith
  ultimately show ?thesis by blast
qed

text \<open>
  Same lemma, with the justification sledgehammer actually produced.
  On the bare existential it found nothing; the witnesses must be given.
  Here proof (without a method) applies the intro rule exI (\<section>4.2),
  so each show supplies one witness; sledgehammer (cvc5) then closed
  the remaining goal with "by force".
\<close>
lemma "\<exists>ys zs. xs = ys @ zs \<and>
          (length ys = length zs \<or> length ys = length zs + 1)"
proof
  let ?k = "(length xs + 1) div 2"
  show "\<exists>zs. xs = take ?k xs @ zs \<and>
          (length (take ?k xs) = length zs \<or>
           length (take ?k xs) = length zs + 1)"
  proof
    show "xs = take ?k xs @ drop ?k xs \<and>
          (length (take ?k xs) = length (drop ?k xs) \<or>
           length (take ?k xs) = length (drop ?k xs) + 1)"
      by force
  qed
qed

text \<open>Exercise 4.3\<close>

inductive ev :: "nat \<Rightarrow> bool" where
  ev0: "ev 0"
| evSS: "ev m \<Longrightarrow> ev (Suc (Suc m))"

lemma ev_inver_suc:
  assumes a: "ev (Suc (Suc n))"
  shows "ev n"
(* proof cases
     case ev0 *)
    \<comment> \<open>\<open>proof cases\<close> at the top would invert the goal @{prop "ev n"},
        not assumption @{text a}.  Rule inversion needs the inverted
        fact as input: @{text "from a"} feeds @{text a} into @{text cases}.\<close>
proof -
  from a show "ev n"
  proof cases
    case evSS
    thus ?thesis by simp
  qed
qed

text \<open>Exercise 4.4\<close>

lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))"
  hence "ev (Suc 0)" by (rule ev_inver_suc)
  thus "False" by cases
qed

(*former lemma is not needed:*)
lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))"
  thus False
  proof cases
    \<comment> \<open>first variant: apply @{text ev_inver_suc}, then invert
        @{prop "ev (Suc 0)"}.  Here @{text cases} inverts the
        assumption itself; @{text ev0} is impossible.\<close>
    case evSS
      \<comment> \<open>already @{prop "ev (Suc 0)"}, the conclusion of
          @{text ev_inver_suc}, so that lemma is not needed.\<close>
    thus False by cases
  qed
qed

text \<open>Exercise 4.5\<close>

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for f where
  refl: "star f x x"
| step: "f x y \<Longrightarrow> star f y z \<Longrightarrow> star f x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  init: "iter r 0 x x"
| step: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

thm iter.inducts

lemma
  fixes n :: nat
  assumes "iter r n x y"
  shows "star r x y"
(* proof (induction rule: iter.induct) *)
    \<comment> \<open>rule induction needs the iter hook in the goal or chained in;
        assumes leaves it in the context, so the method cannot apply.\<close>
proof -
  from assms show ?thesis
  proof (induction rule: iter.induct)
    case (init x)
    show ?case by (rule refl)  \<comment> \<open>not shadowed\<close>
  next
    case (step x y n z)
    (* thus ?case by (rule step) *)
        \<comment> \<open>case (step ...) rebinds step to the case facts, which do
            not conclude ?case; also shadows star.step.  iter.step
            concludes iter, not star.\<close>
    (* thus ?case by (rule star.step) *)
        \<comment> \<open>star.step wants r x y then star r y z; thus feeds all of
            this, with iter r n y z in between, so OF fails.\<close>
    from this(1, 3) show ?case by (rule star.step)
        \<comment> \<open>we should only pick the 1st and 3rd from this, strictly\<close>
    (* from step.hyps(1) step.IH show ?case by (rule star.step) - better*)
  qed
qed

text \<open>Exercise 4.6\<close>

fun elems :: "'a list \<Rightarrow> 'a set" where
  "elems Nil = {}"
| "elems (x # xs) = insert x (elems xs)"

(*
fun find_index :: "'a list \<Rightarrow> 'a \<Rightarrow> (nat \<times> bool)" where
  "find_index Nil x = (0, False)"
| "find_index (y # ys) x = (
    if y = x then
      (Suc 0, True)
    else
      (Suc (fst (find_index ys x))), False)"
    \<comment> \<open>the extra parenthesis closed the pair too early, so
        @{text False} was leftover syntax.  Even a well-formed
        pair with hardcoded @{text False} would be wrong: if
        @{text x} occurs later, the Boolean must come from the
        recursive call, via @{text snd}.\<close>
| "find_index (y # ys) x = (
    if y = x then
      (Suc 0, True)
    else
      (Suc (fst (find_index ys x)), snd (find_index ys x)))"
    \<comment> \<open>two independent recursive calls: the mathematical function
        is still linear, but @{text simp} / the code generator unfold
        each occurrence separately, so evaluation is exponential in
        the length of a miss-prefix.  Bind the result once.\<close>
| "find_index (y # ys) x = (
    if y = x then
      (Suc 0, True)
    else
      (case find_index ys x of (n, b) \<Rightarrow> (Suc n, b)))"

value "find_index [(3::nat), 4, 5] 3"
*)
  \<comment> \<open>not needed for the lemma.  Bare @{text "show ?Q proof"}
      would demand a closed-form witness such as
      @{text "take (fst (find_index xs x) - 1) xs"}, but induction
      on @{text xs} builds the prefix in each case: @{text "[]"}
      when @{text x} is the head, otherwise @{text "y # ys'"} from
      the IH.\<close>

lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys" (is "?P \<Longrightarrow> ?Q")
proof -
  (* assume ?P show ?Q  - assumption is lost *)
  assume ?P thus ?Q
  proof (induction xs)
    case Nil
    thus ?case by simp
      \<comment> \<open>from assumption infer False, then anything\<close>
  next
    case (Cons u us)
    from this have "x = u \<or> x \<noteq> u" by simp
      \<comment> \<open>"this" is a moving name\<close>
    thus ?case
    proof
      assume "x = u"
      hence "u # us = [] @ x # us \<and> x \<notin> elems []" by auto
      thus ?case by blast
    next
      assume noteq: "x \<noteq> u"
      from this Cons.prems have "x \<in> elems us" by simp
        \<comment> \<open>Note how we call the two Cons facts here and below\<close>
      then obtain ys zs where "us = ys @ x # zs" "x \<notin> elems ys"
        using Cons.IH by blast
        \<comment> \<open>IH splits @{text us}, not @{text "u # us"}.  Prepend @{text u}
            to the prefix; @{text noteq} is what keeps @{text x} out of
            @{text "elems (u # ys)"}.\<close>
      (* with noteq have "u # us = ys @ x # zs \<and> x \<notin> elems ys" by simp *)
      with noteq have "u # us = (u # ys) @ x # zs \<and> x \<notin> elems (u # ys)" by simp
        \<comment> \<open>Be careful about what is the new "ys"\<close>
      thus ?case by blast
    qed
  qed
qed

(*A cleaner proof for the Cons case:*)
lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys" (is "?P \<Longrightarrow> ?Q")
proof -
  assume ?P thus ?Q
  proof (induction xs)
    case Nil
    thus ?case by simp
      \<comment> \<open>from assumption infer False, then anything\<close>
  next
    case (Cons u us)
    show ?case
      \<comment> \<open>show, not thus: otherwise cases is fed Cons.IH / Cons.prems.\<close>
    proof (cases "x = u")
      \<comment> \<open>@{text True} / @{text False} on the term,
          not @{text disjE} on a manufactured @{text "x = u \<or> x \<noteq> u"}.\<close>
      case True
      then have "u # us = [] @ x # us \<and> x \<notin> elems []" by simp
      then show ?thesis by blast
    next
      case False
      from Cons.prems False have "x \<in> elems us" by simp
      then obtain ys zs where "us = ys @ x # zs" "x \<notin> elems ys"
        using Cons.IH by blast
      then have "u # us = (u # ys) @ x # zs \<and> x \<notin> elems (u # ys)"
        using False by simp
      then show ?thesis by blast
    qed
  qed
qed

(*Shortened: induct the lemma; name the empty prefix in True.*)
lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons u us)
  show ?case
  proof (cases "x = u")
    case True
    then show ?thesis
      by (intro exI[where x="[]"] exI[where x=us]) simp
        \<comment> \<open>name both witnesses; @{text auto} will search forever for them.\<close>
  next
    case False
    from Cons.prems False have "x \<in> elems us" by simp
    then obtain ys zs where "us = ys @ x # zs" "x \<notin> elems ys"
      using Cons.IH by blast
    then have "u # us = (u # ys) @ x # zs \<and> x \<notin> elems (u # ys)"
      using False by simp
    then show ?thesis by blast
  qed
qed

(*Further reading: elems is set; HOL already has the claim.*)
lemma elems_set: "elems xs = set xs"
  by (induction xs) auto

lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
  unfolding elems_set by (rule iffD1[OF in_set_conv_decomp_first])
    \<comment> \<open>@{text simp} with @{text in_set_conv_decomp_first} loops:
        it rewrites @{text "x \<notin> set ys"} in the conclusion as well.\<close>

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
