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
  show "1 < n + n" .       "." matches the goal against calculation\<close>

text \<open>Section 4.3 Streamlining Proofs\<close>

text \<open>section 4.3.1 Pattern Matching and Quotations\<close>

(*
  show formula (is pattern)
    matches pattern against formula and binds the unknowns (?L, ?R, \<dots>)
    for later use.  Works with lemma / have / show.

  ?thesis
    is implicitly matched against the goal of lemma or show.

  let ?t = "some-big-term"
    binds an unknown to a term; later steps write ?t instead of the term.

  name: "P"     names a fact (a proved theorem)
  ?X            names a term or formula (not a fact)

  from \<open>P\<close>      quotes a fact by value, using \<open>\<dots>\<close>
                prefer this when the name would be longer than the fact
*)

lemma is_pattern_iff:
  "A \<inter> B = A \<longleftrightarrow> A \<subseteq> B" (is "?L \<longleftrightarrow> ?R")  \<comment> \<open>the pattern\<close>
proof
  assume "?L"
  thus "?R" by blast
next
  assume "?R"
  thus "?L" by blast
qed

lemma thesis_and_let:
  fixes xs ys :: "'a list"
  shows "length (rev xs @ ys) = length xs + length ys"
proof -
  let ?r = "rev xs"
  have "length (?r @ ys) = length ?r + length ys" by simp
  also have "... = length xs + length ys" by simp
  finally show ?thesis .
qed

lemma quote_vs_name:
  fixes n :: nat
  assumes "n > 0"
  shows "n * n > 0"
proof -
  have "n > 0" using assms .
    \<comment> \<open>a name like n_gr_0 would be longer than the fact itself\<close>
  from \<open>n > 0\<close> show ?thesis by simp
qed

text \<open>section 4.3.2 moreover\<close>

(*
  this         — the latest fact only
  calculation  — shared register for also and moreover

  also       calculation := trans [OF calculation this]   (compose)
  moreover   calculation := calculation this              (append)
  finally    \<equiv> also from calculation
  ultimately \<equiv> moreover from calculation

  also folds to one fact; moreover grows a list.
  Do not mix also and moreover in the same block.
*)

text \<open>section 4.3.3 Local Lemmas\<close>

(* This is simply an extension of the basic `have` construct:
    have B if name: A_1, ..., A_m for x_1, ..., x_n
    \<open>proof\<close> *)

lemma
  fixes a b :: int
  assumes "b dvd (a + b)"
  shows "b dvd a"
proof -
  have "\<exists>k'. a = b * k'" if asm: "a + b = b * k" for k
  proof
    show "a = b * (k - 1)" using asm by (simp add: algebra_simps)
  qed
  then show ?thesis using assms by (auto simp add: dvd_def)
qed

text \<open>Section 4.4 Case Analysis and Induction\<close>

text \<open>section 4.4.1 Datatype Case Analysis\<close>

thm tl_def

(*apply-style*)
lemma "length (tl xs) = length xs - 1"
  apply(induction xs)
   apply(simp_all)
  done

(*Isar-style*)
lemma "length (tl xs) = length xs - 1"
proof (cases xs)
  \<comment> \<open>case analysis on datatype of xs\<close>
  assume "xs = Nil"
  thus ?thesis by simp
next
  fix y ys
  assume "xs = y # ys"
  thus ?thesis by simp
qed

(*a simplified version using case idiom:*)
lemma "length (tl xs) = length xs - 1"
proof (cases xs)
  case Nil
  thus ?thesis by simp
next
  (* case "y # ys" - incorrect *)
    \<comment> \<open>Quotation marks delimit logical terms, not case specifications.\<close>
  (* case (y # ys) - incorrect *)
    \<comment> \<open>Parentheses group a case name and its parameter bindings; \<open>#\<close> is term syntax.\<close>
  case (Cons y ys)
    \<comment> \<open>\<open>Cons\<close> is the case name; \<open>y\<close> and \<open>ys\<close> name its parameters.\<close>
  thus ?thesis by simp
qed

section \<open>Section 4.4.2 Structural Induction\<close>

lemma "\<Sum>{0..n::nat} = n*(n+1) div 2"
proof (induction n)
  show "\<Sum>{0..0::nat} = 0*(0+1) div 2" by simp
next
  fix n
  assume "\<Sum>{0..n::nat} = n*(n+1) div 2"
  thus "\<Sum>{0..(Suc n)::nat} = (Suc n)*((Suc n)+1) div 2" by simp
qed

(*simplified version using pattern matching:*)
lemma "\<Sum>{0..n::nat} = n*(n+1) div 2" (is "?P n")  \<comment> \<open>the pattern\<close>
proof (induction n)
  show "?P 0" by simp
next
  fix n
  assume "?P n"
  thus "?P (Suc n)" by simp
qed

(*simplified version using case idiom*)
lemma "\<Sum>{0..n::nat} = n*(n+1) div 2"
(* proof (cases n) *)
  \<comment> \<open>Case analysis splits n into 0 and Suc n,
      but supplies no induction hypothesis for the Suc case.\<close>
proof (induction n)
  case 0
  show ?case by simp
    \<comment> \<open>?case is set in each case to the required claim\<close>
next
  case (Suc n)
  thus ?case by simp
qed

text \<open>
  When the induction goal is an implication, each case assumes its premise
  automatically, and \<open>?case\<close> denotes only the conclusion.
\<close>

lemma add_right_less_if_less:
  fixes n m k :: nat
  shows "n < m \<Longrightarrow> n + k < m + k"
proof (induction k)
  case 0
  \<comment> \<open>\<open>0.prems\<close> is \<open>n < m\<close>; \<open>?case\<close> is only \<open>n + 0 < m + 0\<close>.\<close>
  from "0.prems" show ?case by simp
next
  case (Suc k)
  \<comment> \<open>\<open>Suc.IH\<close> is an implication, and \<open>Suc.prems\<close> supplies its premise.\<close>
  from Suc.IH[OF Suc.prems] show ?case by simp
qed

text \<open>section 4.4.3 Computation Induction\<close>

fun pair_count :: "'a list \<Rightarrow> nat" where
  "pair_count [] = 0"
| "pair_count [x] = 0"
| "pair_count (x # y # xs) = Suc (pair_count xs)"

lemma pair_count_le_length:
  "2 * pair_count xs \<le> length xs"
proof (induction rule: pair_count.induct)
  case 1
    \<comment> \<open>the number of equations starts from 1\<close>
  show ?case by simp
next
  case (2 x)
  show ?case by simp
next
  case (3 x y xs)
  (* thus ?case by simp, or: *)
  from "3.IH"(1) show ?case by simp
    \<comment> \<open>\<open>"3.IH"(1)\<close> selects the first induction hypothesis of case 3;
        \<open>(1)\<close> may be omitted because this case has exactly one induction hypothesis.\<close>
qed

text \<open>section 4.4.4 Rule Induction\<close>

inductive ev :: "nat \<Rightarrow> bool" where
  ev0: "ev 0"
| evSS: "ev m \<Longrightarrow> ev (Suc (Suc m))"

fun evn :: "nat \<Rightarrow> bool" where
  "evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc (Suc m)) = evn m"

(*the Isar-style based on rules*)
lemma "ev m \<Longrightarrow> evn m"
proof (induction rule: ev.induct)
  case ev0
    \<comment> \<open>let ?case = "evn 0"\<close>
  show ?case by simp
next
  case evSS  \<comment> \<open>m is not needed explicitly here\<close>
    \<comment> \<open>fix m
        assume evSS: "ev m" - the premise of the rule \<open>ev.evSS\<close> (\<open>evSS.hyps\<close>)
                     "evn m" - the induction hypothesis for that premise (\<open>evSS.IH\<close>)
        let ?case = "evn (Suc (Suc m))"\<close>
  thus ?case by simp
qed
(* next
  case (evSS m)  <-- in this case m is needed explicitly
  have "evn(Suc(Suc m)) = evn m" by simp
  thus ?case using \<open>evn m\<close> by blast
qed *)


end




