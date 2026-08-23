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

end
