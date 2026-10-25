import chebyshev2.SineContinuum.MercerClosed

/-!
Article: chebyshev2, Lemma 5.
Uniform absolute convergence of the literal Mercer series on the entire closed square, expressed as
a uniform bound on every infinite absolute tail.
Result: `chebyshev2.SineContinuum.green_mercer_uniform` supplies the stated article conclusion.
Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion. The needed form is
proved here.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Set Real Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency true

/--
Defines `mercerDiagonalTail` of type `ℝ` by `green t t-mercerDiagonalPartial N t`.

Use: `chebyshev2.SineContinuum.green_mercer_uniform_absolute` uses this definition to
establish constructs witnesses with the exact properties `∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (0:ℝ) 1,
∀ s ∈ Icc (0:ℝ) 1, (∑' j, |upsilon (j+n) t*upsilon (j+n) s/mu (j+n)|) < ε`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.
-/
def mercerDiagonalTail (N : ℕ) (t : ℝ) : ℝ := green t t-mercerDiagonalPartial N t

/--
Exact identity `(∑' j, upsilon (j+N) t^2/mu (j+N))=mercerDiagonalTail N t`.

Use: `chebyshev2.SineContinuum.mercer_absolute_tail_bound` rewrites with this identity to
establish the stated quantitative bound `(∑' j, |upsilon (j+N) t*upsilon (j+N) s/mu (j+N)|) ≤
(mercerDiagonalTail N t+mercerDiagonalTail N s)/2`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.green_mercer_diagonal_closed`
with the arguments shown in the proof.
-/
theorem mercerDiagonalTail_eq (N : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (∑' j, upsilon (j+N) t^2/mu (j+N))=mercerDiagonalTail N t := by
  have h := (green_mercer_diagonal_closed ht).summable.sum_add_tsum_nat_add N
  rw [(green_mercer_diagonal_closed ht).tsum_eq] at h
  change mercerDiagonalPartial N t+_=green t t at h
  unfold mercerDiagonalTail
  linarith

/--
The stated quantitative bound `(∑' j, |upsilon (j+N) t*upsilon (j+N) s/mu (j+N)|) ≤
(mercerDiagonalTail N t+mercerDiagonalTail N s)/2`.

Use: `chebyshev2.SineContinuum.green_mercer_uniform_absolute` uses this bound to establish
constructs witnesses with the exact properties `∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc
(0:ℝ) 1, (∑' j, |upsilon (j+n) t*upsilon (j+n) s/mu (j+n)|) < ε`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Use the identities/estimates
`chebyshev2.SineContinuum.green_mercer_diagonal_closed`,
`chebyshev2.SineContinuum.green_mercer_absolute`,
`chebyshev2.SineContinuum.mercer_term_abs_le` with the arguments shown in the proof.
-/
theorem mercer_absolute_tail_bound (N : ℕ) {t s : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) :
    (∑' j, |upsilon (j+N) t*upsilon (j+N) s/mu (j+N)|) ≤
      (mercerDiagonalTail N t+mercerDiagonalTail N s)/2 := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.green_mercer_diagonal_closed`,
  -- `chebyshev2.SineContinuum.green_mercer_absolute`,
  -- `chebyshev2.SineContinuum.mercer_term_abs_le` with the arguments shown in the proof.
  have h₁ := (summable_nat_add_iff N).mpr (green_mercer_diagonal_closed ht).summable
  have h₂ := (summable_nat_add_iff N).mpr (green_mercer_diagonal_closed hs).summable
  have h₃ := (summable_nat_add_iff N).mpr (green_mercer_absolute ht hs)
  calc
    _ ≤ ∑' j, (upsilon (j+N) t^2/mu (j+N)+upsilon (j+N) s^2/mu (j+N))/2 :=
      h₃.tsum_le_tsum (fun j => mercer_term_abs_le (j+N) t s) ((h₁.add h₂).div_const 2)
    _ = _ := by rw [tsum_div_const,(h₁.tsum_add h₂),mercerDiagonalTail_eq N ht,mercerDiagonalTail_eq N hs]

/--
Uniform absolute convergence of the literal Mercer series on the entire closed square,
expressed as a uniform bound on every infinite absolute tail.

Constructs witnesses with the exact properties `∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc
(0:ℝ) 1, (∑' j, |upsilon (j+n) t*upsilon (j+n) s/mu (j+n)|) < ε`.

Use: `chebyshev2.SineContinuum.green_mercer_uniform` uses this bound to establish the
stated quantitative bound `TendstoUniformlyOn mercerPartial (fun z => green z.1 z.2) atTop (Icc
(0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Use the identities/estimates
`chebyshev2.SineContinuum.green_mercer_diagonal_uniform`,
`chebyshev2.SineContinuum.mercer_absolute_tail_bound` with the arguments shown in the
proof.
-/
theorem green_mercer_uniform_absolute (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1,
      (∑' j, |upsilon (j+n) t*upsilon (j+n) s/mu (j+n)|) < ε := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.green_mercer_diagonal_uniform`,
  -- `chebyshev2.SineContinuum.mercer_absolute_tail_bound` with the arguments shown in the
  -- proof.
  have h := (Metric.tendstoUniformlyOn_iff.mp green_mercer_diagonal_uniform) ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  refine ⟨N,?_⟩
  intro n hn t ht s hs
  have h₁ := hN n hn t ht
  have h₂ := hN n hn s hs
  simp only [Real.dist_eq] at h₁ h₂
  have h₃ := mercer_absolute_tail_bound n ht hs
  unfold mercerDiagonalTail at h₃
  have ha := le_abs_self (green t t-mercerDiagonalPartial n t)
  have hb := le_abs_self (green s s-mercerDiagonalPartial n s)
  linarith

/--
Defines `mercerPartial` of type `ℝ` by `∑ j ∈ Finset.range N, upsilon j z.1*upsilon j z.2/mu
j`.

Use: `chebyshev2.SineContinuum.mercer_error_le_tail` uses this definition to establish the
stated quantitative bound `|green t s-mercerPartial N (t,s)| ≤ ∑' j, |upsilon (j+N) t*upsilon
(j+N) s/mu (j+N)|`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.
-/
def mercerPartial (N : ℕ) (z : ℝ × ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, upsilon j z.1*upsilon j z.2/mu j

/--
The stated quantitative bound `|green t s-mercerPartial N (t,s)| ≤ ∑' j, |upsilon (j+N)
t*upsilon (j+N) s/mu (j+N)|`.

Use: `chebyshev2.SineContinuum.green_mercer_uniform` uses this bound to establish the
stated quantitative bound `TendstoUniformlyOn mercerPartial (fun z => green z.1 z.2) atTop (Icc
(0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.green_mercer_closed`,
`chebyshev2.SineContinuum.green_mercer_absolute` with the arguments shown in the proof.
-/
theorem mercer_error_le_tail (N : ℕ) {t s : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) :
    |green t s-mercerPartial N (t,s)| ≤
      ∑' j, |upsilon (j+N) t*upsilon (j+N) s/mu (j+N)| := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.green_mercer_closed`,
  -- `chebyshev2.SineContinuum.green_mercer_absolute` with the arguments shown in the
  -- proof.
  have h := (green_mercer_closed ht hs).summable.sum_add_tsum_nat_add N
  rw [(green_mercer_closed ht hs).tsum_eq] at h
  have he : green t s-mercerPartial N (t,s)=
      ∑' j, upsilon (j+N) t*upsilon (j+N) s/mu (j+N) := by
    change mercerPartial N (t,s)+_=green t s at h
    linarith
  rw [he]
  -- Prove the summability hn needed for the later infinite-sum manipulations.
  have hn : Summable (fun j => ‖upsilon (j+N) t*upsilon (j+N) s/mu (j+N)‖) := by
    simpa only [Real.norm_eq_abs] using (summable_nat_add_iff N).mpr (green_mercer_absolute ht hs)
  simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hn

/--
The stated quantitative bound `TendstoUniformlyOn mercerPartial (fun z => green z.1 z.2) atTop
(Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 5.

Source: Riesz and Sz.-Nagy, Functional Analysis, §98 — Mercer diagonal expansion.

Proof: Use the identities/estimates
`chebyshev2.SineContinuum.green_mercer_uniform_absolute`,
`chebyshev2.SineContinuum.mercer_error_le_tail` with the arguments shown in the proof.
-/
theorem green_mercer_uniform : TendstoUniformlyOn mercerPartial
    (fun z => green z.1 z.2) atTop (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.green_mercer_uniform_absolute`,
  -- `chebyshev2.SineContinuum.mercer_error_le_tail` with the arguments shown in the proof.
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := green_mercer_uniform_absolute ε hε
  apply eventually_atTop.mpr
  refine ⟨N,?_⟩
  intro n hn z hz
  rw [Real.dist_eq]
  exact (mercer_error_le_tail n hz.1 hz.2).trans_lt (hN n hn z.1 hz.1 z.2 hz.2)

end
end chebyshev2.SineContinuum
