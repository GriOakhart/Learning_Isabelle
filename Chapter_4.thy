theory Chapter_4
  imports Main

begin

text \<open>Section 4.1 Isar by Example\<close>

lemma Cantor_01: "\<not>surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists>a. A = f a" by(simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

(*this - refer to the proposition proved in the previous step*)
lemma Cantor_02: "\<not>surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  from this have "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  from this show "False" by blast
qed

text \<open>section 4.1.1 this, then, hence and thus\<close>

(*
  then  = from this
  hence = then have
  thus  = then show
*)
lemma Cantor_03: "\<not>surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  thus "False" by blast
qed

(*
  (have|show) prop using facts = from facts (have|show) prop
                    with facts = from facts this
*)

text \<open>section 4.1.2 Structured Lemma Statements: fixes, assumes, shows\<close>

lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -
  \<comment> \<open>the hyphen after the proof command is
      the null method that does nothing to the goal\<close>
  have "\<exists>a. {x. x \<notin> f x} = f a" using s \<comment> \<open>or assms(1)\<close>
    by(auto simp: surj_def)
  thus "False" by blast
qed

end
