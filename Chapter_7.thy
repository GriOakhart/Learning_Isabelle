theory Chapter_7
  imports Main Chapter_5

begin

section \<open>7.1 IMP Commands\<close>

text \<open>
  The abstract syntax of commands:\<close>
datatype
  com = SKIP
    \<comment> \<open>no mixfix: the constructor name is already the concrete token\<close>
  | Assign vname aexp       (\<open>_ ::= _\<close> [1000, 61] 61)
    \<comment> \<open>form: (\<open>template\<close> [p1, p2, ...] p).
        `_` = argument hole; other text is the token (`::=`).
        last p = priority of the whole phrase (higher binds tighter).
        [p1, p2, ...] = minimum tightness each argument needs to appear
        without parentheses --- not a maximum, and not the argument's own prio.
        1000 = atomic (only a name left of ::=); 61 = same as Assign itself.\<close>
  | Seq    com  com         (\<open>_;;/ _\<close>  [60, 61] 60)
    \<comment> \<open>`/` = optional pretty-print break after `;;`.
        infixl n is [n, n+1] n, so [60, 61] 60:
        c1;; c2;; c3 = (c1;; c2);; c3.
        the right hole demands 61, so another Seq (60) cannot sit there bare.\<close>
  | If     bexp com com     (\<open>(IF _/ THEN _/ ELSE _)\<close>  [0, 0, 61] 61)
    \<comment> \<open>`(...)` is a pretty-print block.
        0 on an argument is the lowest threshold: no tightness required,
        so any phrase is allowed. Use 0 when keywords already delimit the
        hole (IF _ THEN, THEN _ ELSE) --- the opposite of "parens if compound".
        thus IF b THEN c1;; c2 ELSE c3 = IF b THEN (c1;; c2) ELSE c3.
        ELSE is open on the right, so it demands 61 (Seq at 60 is too loose):
        IF b THEN c1 ELSE c2;; c3 = (IF b THEN c1 ELSE c2);; c3.\<close>
  | While  bexp com         (\<open>(WHILE _/ DO _)\<close>  [0, 61] 61)
    \<comment> \<open>condition sits between WHILE and DO, so threshold 0.
        body is open on the right and demands 61:
        WHILE b DO c1;; c2 = (WHILE b DO c1);; c2;
        write WHILE b DO (c1;; c2) to sequence in the body.\<close>

  \<comment> \<open>Example: WHILE b DO c1;; c2 means (WHILE b DO c1);; c2,
      not WHILE b DO (c1;; c2). Compare own priority with the hole's
      minimum: allowed iff own_prio \<ge> hole_threshold.
      1. WHILE b DO (c1;; c2): Seq's own prio is 60; the DO-hole
         demands 61; 60 < 61, so Seq is not tight enough --- rejected
         without parentheses.
      2. (WHILE b DO c1);; c2: While's own prio is 61; Seq's left hole
         demands 60; 61 \<ge> 60, so While is tight enough --- this is the parse.\<close>

term "Seq (Assign (''x'') (Plus (V ''y'') (N 1))) (Assign (''y'') (N 2))"
  \<comment> \<open>abstract syntax: constructors applied to arguments\<close>
term "''x'' ::= Plus (V ''y'') (N 1);; ''y'' ::= N 2"
  \<comment> \<open>the same term, written with the mixfix sugars above\<close>

section \<open>7.2 Big-Step Semantics\<close>
section \<open>7.2.1 Definition\<close>

text \<open>
  @{text big_step} is a relation, not a function:
  @{text "(c, s) \<Rightarrow> t"} means @{text c} started in @{text s}
  \emph{terminates} in @{text t}.
  A @{command fun} @{text "com \<times> state \<Rightarrow> state"} would have to be total (Ch.\ 2.3),
  but @{term "WHILE Bc True DO SKIP"} never yields a final state.
  @{command fun} also requires recursive calls on strictly smaller arguments;
  @{text WhileTrue} recurses on the same loop.
  @{command inductive} has no termination obligation (Ch.\ 4.5):
  a derivation exists iff execution finishes.
  Contrast @{const aval} / @{const bval}, which always terminate on smaller syntax.
  Determinism (at most one final state) is then a theorem, not built in.\<close>

inductive big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55) where
    \<comment> \<open>`(infix "\<Rightarrow>" 55)` is mixfix for the constant, not a rename:
        `(c, s) \<Rightarrow> t` is `big_step (c, s) t` everywhere (rules, lemmas, \<dots>).
        First argument is a pair so the configuration sits left of \<Rightarrow>
        (`com \<times> state \<Rightarrow> state \<Rightarrow> bool`, not `com \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool`).
        `infix` expands to `("_ \<Rightarrow>/ _" [56, 56] 55)`: both holes demand 56,
        so another \<Rightarrow> (priority 55) cannot sit there --- non-associative.
        The type arrow `\<Rightarrow>` is a different token.\<close>
  Skip: "(SKIP, s) \<Rightarrow> s"
| Assign: "(Assign x exp, s) \<Rightarrow> s (x := aval exp s)"
| Seq: "\<lbrakk>(com1, stk1) \<Rightarrow> stk2; (com2, stk2) \<Rightarrow> stk3\<rbrakk> \<Longrightarrow> (com1;; com2, stk1) \<Rightarrow> stk3"
  \<comment> \<open>s0 is already used in Chapter_5.thy\<close>
| IfTrue: "\<lbrakk>bval b s; (com1, s) \<Rightarrow> t\<rbrakk> \<Longrightarrow> (IF b THEN com1 ELSE com2, s) \<Rightarrow> t"
| IfFalse: "\<lbrakk>\<not> bval b s; (com2, s) \<Rightarrow> t\<rbrakk> \<Longrightarrow> (IF b THEN com1 ELSE com2, s) \<Rightarrow> t"
| WhileFalse: "(\<not> bval b s) \<Longrightarrow> (WHILE b DO com, s) \<Rightarrow> s"
  \<comment> \<open>the loop body is just skipped\<close>
| WhileTrue: "\<lbrakk>bval b stk1; (com, stk1) \<Rightarrow> stk2; (WHILE b DO com, stk2) \<Rightarrow> stk3\<rbrakk> \<Longrightarrow> (WHILE b DO com, stk1) \<Rightarrow> stk3"
  \<comment> \<open>one more iteration: if b holds at stk1, prepend a body run
      stk1 \<Rightarrow> stk2 to a remaining loop from stk2. b is not retested here;
      the recursive WHILE premise does that (False or True again).\<close>

section \<open>7.2.2 Deriving IMP Executions\<close>

schematic_goal ex: "(''x'' ::= N 5;; ''y'' ::= V ''x'', s) \<Rightarrow> ?t"
  apply (rule Seq)
   apply (rule Assign)
  apply (simp)
  apply (rule Assign)
  done
    \<comment> \<open>`done` instantiates ?t with the last Assign's RHS, which still
        has @{term "aval (V ''x'')"} --- there is no remaining subgoal
        to @{method simp}. Reduce the finished fact instead:\<close>
thm ex[simplified]
    \<comment> \<open>(''x'' ::= N 5;; ''y'' ::= V ''x'', ?s) \<Rightarrow> ?s(''x'' := 5, ''y'' := 5)\<close>

text \<open>
  generate code for the predicate big_step (i.e. \<Rightarrow>):\<close>
code_pred big_step .

text \<open>
  similar to value, but works on inductive definitions and computes a set of possible results:\<close>
(* values "(SKIP, (\<lambda>_. 0))" *)
values "{t. (SKIP, (\<lambda>_. 0)) \<Rightarrow> t}"
  \<comment> \<open>"{_}" :: "(char list \<Rightarrow> int) set",
      - a singleton set
      (SKIP, (\<lambda>_. 0)) \<Rightarrow> t - this is a predicate\<close>

(* see section 4.2: *)
values "{t ''x'' | t. (SKIP, (\<lambda>_. 0)) \<Rightarrow> t}"
  \<comment> \<open>"{0}" :: "int set"\<close>

values "{map t [''x'', ''y''] | t. (''x'' ::= (Plus (V ''x'') (N 1));; ''y'' ::= V ''x'', (\<lambda>_. 1)) \<Rightarrow> t}"
  \<comment> \<open>"{[2, 2]}" :: "int list set"\<close>

values "{map t [''x'', ''y''] | t.
  (WHILE Less (V ''x'') (V ''y'') DO (''x'' ::= Plus (V ''x'') (N 5)),
   (\<lambda>_. 0)(''x'' := 0, ''y'' := 13)) \<Rightarrow> t}"
  \<comment> \<open>"{[15, 13]}" :: "int list set"
      x := 0,5,10,15 then 15 < 13 fails. A WHILE that actually ends.\<close>

(* values "{t. (WHILE Bc True DO SKIP, (\<lambda>_. 0)) \<Rightarrow> t}" *)
  \<comment> \<open>Do not run:
      @{command values} searches for a derivation. @{text WhileTrue} matches
      forever (condition stays true, SKIP leaves the state, same loop again),
      so the search never returns and the derivation tree grows without bound.\<close>

section \<open>7.2.3 Rule Inversion\<close>

(* the following is the inverted rules for big_step semantics: *)
thm big_step.cases

text \<open>
  Bare @{method cases} does not consume the @{text "\<Longrightarrow>"}-premise, so
  @{text "by cases"} fails here --- same pitfall as Exercise 4.3.
  Feed the inductive fact in.  Even then, @{text "by cases"} only
  finishes when every branch is impossible (e.g.\ @{text "ev (Suc 0)"}).
  SKIP leaves @{text "t = s"}, which @{method cases} does not @{method simp}
  into @{text "s = t"}.\<close>

(* apply-style, same shape as @{text ev.cases} in Chapter_4: *)
lemma "(SKIP, s) \<Rightarrow> t \<Longrightarrow> s = t"
  apply (rule big_step.cases)
  apply auto
  done

lemma
  assumes skip: "(SKIP, s) \<Rightarrow> t"
  shows "s = t"
proof -
  from skip show "s = t"
  proof cases
    case Skip
    thus ?thesis by simp
  qed
qed

(* book's automation: specialize @{text big_step.cases} and register as elim *)
inductive_cases SkipE[elim!]: "(SKIP, s) \<Rightarrow> t"
thm SkipE

lemma "(SKIP, s) \<Rightarrow> t \<Longrightarrow> s = t"
  by blast

lemma seq_inver: "(c1;; c2, stk1) \<Rightarrow> stk3 \<longleftrightarrow> (\<exists>stk2. ((c1, stk1) \<Rightarrow> stk2 \<and> (c2, stk2) \<Rightarrow> stk3))"
  apply (rule iffI)
   apply (rule big_step.cases)
          apply (auto)
  apply (simp add: big_step.Seq)
  done

lemma "((c1;; c2);; c3, s) \<Rightarrow> t \<longleftrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> t"
  apply (rule iffI)
   apply (simp_all add: seq_inver)
   apply (auto)
  done

section \<open>7.2.4 Equivalence of Commands\<close>

text \<open>
  Equivalence w.r.t. the big-step semantics:\<close>
abbreviation equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  \<comment> \<open>"\<sim>" is \<sim>\<close>
  "c \<sim> c' \<equiv> (\<forall>s t. (c, s) \<Rightarrow> t = (c', s) \<Rightarrow> t)"
  \<comment> \<open>"Both change s to t" overstates: @{text "="} is iff of bools,
      so the predicates must match, not both be True.
      From any s, c reaches t exactly when c' does
      (both may diverge (non-terminated), or leave s unchanged).\<close>

text \<open>
  Unfolding WHILE-DO:\<close>
(* Variant 1A *)
lemma "WHILE b DO c \<sim> IF b THEN (c;;  WHILE b DO c) ELSE SKIP"
  apply (auto)
   apply (rule big_step.cases)  \<comment> \<open>rules inversion for the first subgoal\<close>
          apply (auto)
    \<comment> \<open>Auto discharges the major premise from the assumption and rules out
        the five non-While cases by constructor distinctness, leaving WhileFalse and WhileTrue.\<close>
    \<comment> \<open> 1. \<And>sa. (WHILE b DO c, sa) \<Rightarrow> sa \<Longrightarrow>
            \<not> bval b sa \<Longrightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP, sa) \<Rightarrow> sa\<close>
    apply (simp add: big_step.IfFalse big_step.Skip)
    \<comment> \<open> 2. \<And>stk1 stk2 stk3.
         (WHILE b DO c, stk1) \<Rightarrow> stk3 \<Longrightarrow>
         bval b stk1 \<Longrightarrow>
         (c, stk1) \<Rightarrow> stk2 \<Longrightarrow>
         (WHILE b DO c, stk2) \<Rightarrow> stk3 \<Longrightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP, stk1) \<Rightarrow> stk3\<close>
   apply (simp add: big_step.IfTrue big_step.Seq)
  apply (rule big_step.cases)
         apply (auto)
   apply (simp_all add: big_step.intros)
    \<comment> \<open>apply inverted rules for Seq again:\<close>
  apply (rule big_step.cases)
         apply (auto)
  apply (simp add: big_step.Seq big_step.WhileTrue)
(*
  or alternatively, we can do the following, instead of applying rules of inversion again:
    \<comment> \<open>WhileTrue needs (c, sa) \<Rightarrow> ?s2 and (WHILE b DO c, ?s2) \<Rightarrow> ta
        separately; invert the Seq fact first:\<close>
  apply (simp add: seq_inver)
  apply (auto intro: WhileTrue) *)
  done

text \<open>
  Variant 1B:
  Or we can firstly generate the inverted rules for specific schemes:\<close>
inductive_cases SeqE: "(c1;; c2, s) \<Rightarrow> t"
inductive_cases IfE: "(IF b THEN c1 ELSE c2, s) \<Rightarrow> t"
inductive_cases WhileE: "(WHILE b DO c, s) \<Rightarrow> t"
lemma "WHILE b DO c \<sim> IF b THEN (c;;  WHILE b DO c) ELSE SKIP"
  apply (auto)
   apply (erule WhileE)
    apply (simp_all add: big_step.intros)
  apply (erule IfE)
   apply (erule SeqE)
   apply (simp add: big_step.WhileTrue)
  apply (erule SkipE)
  apply (simp add: big_step.WhileFalse)
  done

(* Variant 2 - Simplified version for variant 1*)
lemma "WHILE b DO c \<sim> IF b THEN (c;;  WHILE b DO c) ELSE SKIP"
    \<comment> \<open>same argument, shorter script: @{method erule} inverts the
        assumption (unlike @{method rule}); @{text "+"} repeats for
        both directions of @{text "\<sim>"}.\<close>
  apply auto
  apply (erule big_step.cases, auto intro: big_step.intros)+
  done

lemma "c \<sim> IF b THEN c ELSE c"
  apply auto
   apply (erule big_step.cases, auto intro: big_step.intros)+
  done

thm big_step.inducts

text \<open>
  This lemma is more complex. Rule inversion alone only exposes the outermost
  loop step. In the WhileTrue case, the recursive premise
  @{text "(WHILE b DO c, s2) \<Rightarrow> t"} remains, but inversion provides no
  hypothesis for replacing @{text c} by @{text c'} in that execution.
  Induction on the big-step derivation is therefore needed to obtain the
  required induction hypothesis for every remaining loop iteration.\<close>
text \<open>
  Recall section 4.4.7\<close>
lemma "\<lbrakk>(WHILE b DO c, s) \<Rightarrow> t; c \<sim> c'\<rbrakk> \<Longrightarrow> (WHILE b DO c', s) \<Rightarrow> t"
  (* apply (induction "WHILE b DO c" s t arbitrary: b c rule: big_step.inducts) *)
  \<comment> \<open>Ill-typed instantiation:
        x__ :: com
      @{text big_step.inducts} is @{text "P (c, s) t"}: first slot is
      @{typ "com \<times> state"}, not @{typ com}. Three terms do not match.\<close>
  apply (induction "(WHILE b DO c, s)" t arbitrary: b c s rule: big_step.inducts)
    \<comment> \<open>`s` lives in the hook pair, so generalize it too. Otherwise the
        remaining-loop IH is only @{text "stk2 = s \<Longrightarrow> \<dots>"} and WhileTrue sticks.\<close>
   apply (auto intro: big_step.intros)
  done

(* the proof from the official theory file: *)
declare big_step.intros [intro]
lemmas big_step_induct = big_step.induct[split_format(complete)]
  \<comment> \<open>`big_step` is @{typ "com \<times> state \<Rightarrow> state \<Rightarrow> bool"}, so
      @{text big_step.induct} has two slots: @{text "P (c, s) t"}.
      @{text "split_format(complete)"} unpacks the pair, giving
      @{text big_step_induct} the three slots @{text "P c s t"}.
      The induction below instantiates those three:
      @{text "WHILE b DO c"}, @{text s}, @{text t}.
      Without the split that is the ill-typed instantiation
      above (`x__ :: com`): the first slot of
      @{text big_step.inducts} wants @{typ "com \<times> state"}.
      The 4.4.7 hook also needs the command as its own argument
      so @{text "arbitrary: b c"} can generalize the pieces of
      @{text "WHILE b DO c"}.\<close>
lemma sim_while_cong_aux:
  "(WHILE b DO c,s) \<Rightarrow> t  \<Longrightarrow> c \<sim> c' \<Longrightarrow>  (WHILE b DO c',s) \<Rightarrow> t"
  apply(induction "WHILE b DO c" s t arbitrary: b c rule: big_step_induct)
   apply (blast)
    \<comment> \<open>Failed to apply proof method,
        lacks of declare big_step.intros [intro]\<close>
  apply (blast)
  done

lemma "c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b DO c'"
  by (metis sim_while_cong_aux)

(* INCORRECT:
definition equivalence :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "equivalence x x"
& "equivalence x y \<Longrightarrow> equivalence y x"
& "equivalence x y \<Longrightarrow> equivalence y z \<Longrightarrow> equivalence x z" *)
definition equiv :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "equiv R \<longleftrightarrow> (\<forall> x y z. (R x x) \<and> (R x y \<longrightarrow> R y x) \<and> (R x y \<longrightarrow> R y z \<longrightarrow> R x z))"

lemma "equiv (\<sim>)"
  apply (simp add: equiv_def)
    \<comment> \<open>@{text "\<sim>"} is pointwise HOL equality of big-step predicates,
        so the three conjuncts are refl / sym / trans of @{text "="}.
        @{method simp} already finishes --- no remaining subgoal for @{method auto}.\<close>
  done

section \<open>7.2.5 Execution in IMP is Deterministic\<close>

inductive_cases AssignE: "(x ::= a, s) \<Rightarrow> t"
text \<open>
  IMP is deterministic:
  a language is deterministic if any two executions of the same command
  from the same initial state will always arrive in the same final state\<close>
lemma "\<lbrakk>(c, s) \<Rightarrow> t; (c, s) \<Rightarrow> t'\<rbrakk> \<Longrightarrow> t = t'"
  \<comment> \<open>Induct on the first derivation. @{text "arbitrary: t'"} keeps the
      other final state open, so each IH applies to any second result
      of the same sub-command.
      The case fixes the command shape. @{method blast} inverts
      @{text "(c, s) \<Rightarrow> t'"} with the matching @{text E} rule and the
      IH identifies the intermediate states, hence @{text "t = t'"}.
      @{text SkipE} is already @{text "[elim!]"}. The other four are
      not in the claset, so this call names them.
      @{text WhileE} stays off @{text "[elim!]"}: a @{text WhileTrue}
      premise is another @{text WHILE}, and an eager elim loops.\<close>
  by (induction arbitrary: t' rule: big_step.inducts)
     (blast elim: AssignE SeqE IfE WhileE)+

lemma "\<lbrakk>(c, s) \<Rightarrow> t; (c, s) \<Rightarrow> t'\<rbrakk> \<Longrightarrow> t = t'"
  apply (induction arbitrary: t' rule: big_step.inducts)
        apply (erule SkipE, simp)
       apply (erule AssignE, simp)
      apply (erule SeqE, simp)
     apply (erule IfE, simp, blast)
      \<comment> \<open>@{text IfTrue} only. @{method simp} finishes the second run's
          true arm: the IH rewrites @{text "t = t'"}.
          The false arm ran @{text com2}, so that IH gives no equation;
          @{method blast} uses @{text "bval b s"} against @{text "\<not> bval b s"}.
          @{text IfFalse} is the next subgoal.\<close>
    apply (erule IfE, blast, simp)
   apply (erule WhileE, simp, blast)
  apply (erule WhileE, blast, simp)
  done

lemma "\<lbrakk>(c, s) \<Rightarrow> t; (c, s) \<Rightarrow> t'\<rbrakk> \<Longrightarrow> t = t'"
  apply (induction arbitrary: t' rule: big_step.inducts)
        apply (metis SkipE AssignE SeqE IfE WhileE)+
          \<comment> \<open>@{method metis} ignores the claset, so @{text SkipE}
              is named even though it is @{text "[elim!]"}.
              @{command "done"} closes the proof.\<close>
  done

lemma "\<lbrakk>(c, s) \<Rightarrow> t; (c, s) \<Rightarrow> t'\<rbrakk> \<Longrightarrow> t = t'"
  apply (induction arbitrary: t' rule: big_step.inducts)
  by (blast elim: AssignE SeqE IfE WhileE)+
    \<comment> \<open>@{method blast} uses the claset, so @{text SkipE} is already
        found. @{command "by"} runs the method and closes the proof.\<close>

text \<open>
  @{text WhileTrue} written out: premises, two IHs, then @{text "t = t'"}.
  @{method blast} closes the other six cases.
\<close>
theorem "(c, s) \<Rightarrow> t \<Longrightarrow> (c, s) \<Rightarrow> t' \<Longrightarrow> t = t'"
proof (induction arbitrary: t' rule: big_step.induct)
\<comment> \<open>7. \<And>b stk1 com stk2 stk3 t'.
           bval b stk1 \<Longrightarrow>
           (com, stk1) \<Rightarrow> stk2 \<Longrightarrow>
           (\<And>t'. (com, stk1) \<Rightarrow> t' \<Longrightarrow> stk2 = t') \<Longrightarrow>
           (WHILE b DO com, stk2) \<Rightarrow> stk3 \<Longrightarrow>
           (\<And>t'. (WHILE b DO com, stk2) \<Rightarrow> t' \<Longrightarrow> stk3 = t') \<Longrightarrow>
           (WHILE b DO com, stk1) \<Rightarrow> t' \<Longrightarrow>
            stk3 = t' \<close>
  fix b c s s_1 t t'
  assume "bval b s" and "(c, s) \<Rightarrow> s_1" and "(WHILE b DO c, s_1) \<Rightarrow> t"
  assume IHc: "\<And>t'. (c,s) \<Rightarrow> t' \<Longrightarrow> s_1 = t'"
  assume IHw: "\<And>t'. (WHILE b DO c, s_1) \<Rightarrow> t' \<Longrightarrow> t = t'"
  assume "(WHILE b DO c, s) \<Rightarrow> t'"
  with \<open>bval b s\<close> obtain s_1' where
    c: "(c, s) \<Rightarrow> s_1'" and
    w: "(WHILE b DO c, s_1') \<Rightarrow>t'"
    by (auto elim: WhileE)
  from c IHc have "s_1' = s_1" by blast
  with w IHw show "t = t'" by blast
qed (blast elim: AssignE SeqE IfE WhileE)+

text \<open>
  @{command "case"} names those same facts. @{command obtain} unfolds the
  second @{text WHILE}; @{text WhileTrue.IH} lines the states up.
\<close>
theorem "(c, s) \<Rightarrow> t \<Longrightarrow> (c, s) \<Rightarrow> t' \<Longrightarrow> t = t'"
proof (induction arbitrary: t' rule: big_step.inducts)
  case (WhileTrue b stk1 com stk2 stk3)
    \<comment> \<open>this:
     -->  bval b stk1
          (com, stk1) \<Rightarrow> stk2
          (WHILE b DO com, stk2) \<Rightarrow> stk3
          (com, stk1) \<Rightarrow> ?t' \<Longrightarrow> stk2 = ?t'
          (WHILE b DO com, stk2) \<Rightarrow> ?t' \<Longrightarrow> stk3 = ?t'
     -->  (WHILE b DO com, stk1) \<Rightarrow> t'\<close>
  from \<open>(WHILE b DO com, stk1) \<Rightarrow> t'\<close> \<open>bval b stk1\<close> obtain stk where
    \<comment> \<open>unfold WHILE-DO one time\<close>
    "(com, stk1) \<Rightarrow> stk" and "(WHILE b DO com, stk) \<Rightarrow> t'"
    by (auto elim: WhileE)
  with WhileTrue.IH show ?case by auto
qed (blast elim: AssignE SeqE IfE WhileE)+

end