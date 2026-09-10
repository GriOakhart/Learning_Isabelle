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

term "Seq (Assign (''x'') (Plus (V ''y'') (N 1))) (Assign (''y'') (N 2))"
  \<comment> \<open>abstract syntax: constructors applied to arguments\<close>
term "''x'' ::= Plus (V ''y'') (N 1);; ''y'' ::= N 2"
  \<comment> \<open>the same term, written with the mixfix sugars above\<close>

end