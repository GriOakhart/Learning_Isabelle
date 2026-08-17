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

text \<open>section 4.2 Proof Patterns\<close>

(* reason forword from \<exists>x. P(x):
    have "\<exists>x. P(x)" \<open>proof\<close>
      then obtain x where p: "P(x)" by blast *)

lemma Cantor_04: "\<not>surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a. {x. x \<notin> f x} = f a" by(auto simp: surj_def)
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "a \<in> f a \<longleftrightarrow> a \<notin> f a" by blast
    \<comment> \<open>from {x. x \<notin> f x} = f a, membership is preserved:
        a \<in> {x. x \<notin> f x} \<longleftrightarrow> a \<in> f a;
        by the set comprehension, a \<in> {x. x \<notin> f x} \<longleftrightarrow> a \<notin> f a;
        transitivity then gives a \<in> f a \<longleftrightarrow> a \<notin> f a\<close>
  thus "False" by blast
qed

text \<open>section 4.2.2 Chains of (In)Equations\<close>

(*
  Textbook display:
      t1 = t2     justification
         = t3     justification
         = tn     justification

  Isar equivalent:
      have "t1 = t2" <proof>
      also have "... = t3" <proof>
      also have "... = tn" <proof>
      finally show "t1 = tn" .     <---- NOTE here

  "..." (literally three dots) is instantiated with the RHS of the
  previous (in)equation. 
  "." solves the goal from the result of finally!!!
  The same template works for mixtures of =, \<le> and < (not \<ge> or >).
  The relation in the finally step must be the most precise one possible.
*)

lemma eq_chain_square:
  fixes n :: nat
  shows "(n + 1)^2 = n^2 + 2 * n + 1"
proof -
  have "(n + 1)^2 = (n + 1) * (n + 1)"
    by (simp add: power2_eq_square)
  also have "... = n * n + n + n + 1"
    by (simp add: algebra_simps)
  also have "... = n^2 + 2 * n + 1"
    by (simp add: power2_eq_square)
  finally show "(n + 1)^2 = n^2 + 2 * n + 1" .
qed

lemma ineq_chain_double:
  fixes n :: nat
  assumes "n \<ge> 2"
  shows "1 < n + n"
proof -
  have "1 < (2::nat)" by simp
  also have "... \<le> n" using assms by simp
  also have "... \<le> n + n" by simp
  finally show "1 < n + n" .
    \<comment> \<open>calculation composes 1 < 2, 2 \<le> n and n \<le> n + n
        into 1 < n + n; writing 1 \<le> n + n here would be too weak\<close>
qed

thm trans  \<comment> \<open>equality only: @{thm trans}; mixed chains use other @{attribute trans} rules\<close>

text \<open>
this — the most recently established fact
calculation — an auxiliary fact register (like this) that accumulates the chain

  first also:
      calculation := this
      i.e. note calculation = this

  each later also:
      calculation := trans [OF calculation this]
      Here trans is some @{attribute trans} rule from the context,
      not only the equality theorem @{thm trans}.  The set includes
      transitivity of =, \<le>, < and mixed rules such as
      @{prop "x \<le> y \<Longrightarrow> y < z \<Longrightarrow> x < z"}.

  finally:
      also from calculation
      The hidden also composes the last step; then from calculation
      feeds the completed chain into the next claim.
      So  finally show "t1 R tn" .
      works because calculation is now "t1 R tn" and "." proves the
      goal from that fact.

Walk-through of ineq_chain_double:
  have "1 < 2"           this = (1 < 2)
  also                     first also: calculation := (1 < 2)
  have "... \<le> n"         this = (2 \<le> n)
  also                     calculation := (1 < n)
  have "... \<le> n + n"     this = (n \<le> n + n)
  finally                  hidden also: calculation := (1 < n + n)
                           then from calculation
  show "1 < n + n" .       "." matches the goal against calculation
\<close>

end


