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

end
