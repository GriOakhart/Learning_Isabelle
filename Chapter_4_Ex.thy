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



end
