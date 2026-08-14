theory Star_Simp_Notes
  imports Chapter_3_Ex
begin

text \<open>
  Why does @{prop "star' r x y \<Longrightarrow> star r x y"} prove with a simp one-liner while its
  mirror image @{prop "star r x y \<Longrightarrow> star' r x y"} needs metis?

  The math is symmetric. In the first lemma, the step case of the induction hands
  you a path \<open>star r x y\<close> plus one step \<open>r y z\<close> at the right end, where @{const star}
  only grows on the left — so it needs @{thm [source] star_trans} plus a one-step
  path built from step and refl. The second lemma is the mirror image: one step
  \<open>r x y\<close> at the left end of \<open>star' r y z\<close>, needing @{thm [source] star'_trans} plus
  a one-step path from @{thm [source] star'.step} and @{thm [source] star'.refl}.
  Same shape, same depth, rule for rule.

  Why simp handles one and not the other: when simp uses a conditional rule, it
  solves the premises left to right, and it can only fill in an unknown (like the
  intermediate point of a path) by unifying a premise with an assumption of the
  goal. Compare the two step rules:

    \<^item> @{thm [source] star.step}: \<open>r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z\<close> — the atomic
      r-premise comes first. Solving it against an assumption pins down the
      midpoint, and the recursive premise is then fully concrete. Every rewriting
      step is deterministic, so simp marches straight through.

    \<^item> @{thm [source] star'.step}: \<open>star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z\<close> — the
      recursive premise comes first. simp hits \<open>star' r x ?y\<close> with \<open>?y\<close> still
      unknown, no assumption matches it, and it starts recursively expanding that
      condition with star'_trans and star'.step again, each level introducing fresh
      unknowns. That is not a clean failure but a combinatorial explosion.

  metis (and blast) do genuine proof search with backtracking, so they are
  indifferent to premise order — which is why the metis line in Chapter_3_Ex closes
  the lemma effortlessly.

  This is the same phenomenon as the premise-order remark at
  @{thm [source] star'_trans}: premise order relative to the induction changes what
  the automation can chain together, even when the statements are logically
  interchangeable.\<close>

text \<open>
  Experiment 1: the literal mirror of the star' \<Longrightarrow> star one-liner. This is NOT a
  clean failure; the simplifier goes into a runaway search (killed after 6+
  minutes), because transitivity-style rules make terrible simp rules unless every
  unknown gets pinned down immediately. Kept as a comment so the theory builds:

    lemma "star r x y \<Longrightarrow> star' r x y"
      apply(induction rule: star.induct)
       apply(simp_all add: star'.intros star'_trans)   (* diverges *)\<close>

text \<open>
  Experiment 2: a copy of star'.step with the premises swapped, so the atomic
  r-premise comes first — the same order star.step has.\<close>

lemma star'_step_swp: "r y z \<Longrightarrow> star' r x y \<Longrightarrow> star' r x z"
  by (metis star'.step)

text \<open>
  With it, the literal mirror one-liner works (and builds in seconds), confirming
  that the asymmetry is purely simp's sensitivity to premise order:\<close>

lemma "star r x y \<Longrightarrow> star' r x y"
  apply(induction rule: star.induct)
   apply(simp_all add: star'.refl star'_step_swp star'_trans)
  done

end
