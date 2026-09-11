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
  @{const big_step} is a relation, not a function:
  @{term "(c, s) \<Rightarrow> t"} means @{term c} started in @{term s} \emph{terminates} in @{term t}.
  A @{command fun} @{text "com \<times> state \<Rightarrow> state"} would have to be total (Ch.\ 2.3),
  but @{term "WHILE Bc True DO SKIP"} never yields a @{term t}.
  @{command fun} also requires recursive calls on strictly smaller arguments;
  @{text WhileTrue} recurses on the same loop.
  @{command inductive} has no termination obligation (Ch.\ 4.5):
  a derivation exists iff execution finishes.
  Contrast @{const aval} / @{const bval}, which always terminate on smaller syntax.
  Determinism (at most one @{term t}) is then a theorem, not built in.\<close>
inductive big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55) where
  Skip: "(SKIP, s) \<Rightarrow> s"
| Assign: "(Assign x exp, s) \<Rightarrow> s (x := aval exp s)"
| Seq: "\<lbrakk>(com1, s1) \<Rightarrow> s2; (com2, s2) \<Rightarrow> s3\<rbrakk> \<Longrightarrow> (com1;; com2, s1) \<Rightarrow> s3"
| IfTrue: "\<lbrakk>bval b s; (com1, s) \<Rightarrow> t\<rbrakk> \<Longrightarrow> (IF b THEN com1 ELSE com2, s) \<Rightarrow> t"
| IfFalse: "\<lbrakk>\<not> bval b s; (com2, s) \<Rightarrow> t\<rbrakk> \<Longrightarrow> (IF b THEN com1 ELSE com2, s) \<Rightarrow> t"
| WhileFalse: "(\<not> bval b s) \<Longrightarrow> (WHILE b DO com, s) \<Rightarrow> s"
  \<comment> \<open>the loop body is just skipped\<close>
| WhileTrue: "\<lbrakk>bval b s1; (com, s1) \<Rightarrow> s2; (WHILE b DO com, s2) \<Rightarrow> s3\<rbrakk> \<Longrightarrow> (WHILE b DO com, s1) \<Rightarrow> s3"
  \<comment> \<open>one more iteration: if b holds at s1, prepend a body run
      s1 \<Rightarrow> s2 to a remaining loop from s2. b is not retested here;
      the recursive WHILE premise does that (False or True again).\<close>

end