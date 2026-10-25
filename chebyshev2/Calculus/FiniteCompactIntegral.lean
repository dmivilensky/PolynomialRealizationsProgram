import chebyshev2.Calculus.CompactIntegral

/-!
Article: chebyshev2, Lemma 22.
Finite-order parameter integration.
Use: `chebyshev2.Calculus.finite_compact_integral_smooth` feeds
`chebyshev2.Calculus.finite_cubicIntegral_smooth` (finite cubic Integral smooth).
Proof chain: `chebyshev2.Calculus.removing_cubic_zero` — chebyshev2, Lemma 22; Removal of a
cubic zero at the available finite differentiability order.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace chebyshev2.Calculus
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Establishes the uniform, quantified assertion `∀ k j : ℕ, j+k≤n → ContDiffOn ℝ k (fun t => ∫ v
in Icc c d,F j t v) (Icc a b)`.

Use: `chebyshev2.Calculus.finite_cubicIntegral_smooth` uses this identity to establish
smoothness to the stated order: `ContDiffOn ℝ n (cubicIntegral D 0) (Icc 0 β)`.

Article: chebyshev2, Lemma 22 via `chebyshev2.Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Induct on `k`; the recursive step uses the previous-stage assertion.
-/
theorem finite_compact_integral_smooth {a b c d : ℝ} (hab : a<b) (n : ℕ)
    (F : ℕ → ℝ → ℝ → ℝ)
    (hc : ∀ j≤n, ContinuousOn (fun p : ℝ × ℝ => F j p.1 p.2) (Icc a b ×ˢ Icc c d))
    (hd : ∀ j<n, ∀ t∈Ioo a b, ∀ v∈Icc c d,
      HasDerivAt (fun t => F j t v) (F (j+1) t v) t) :
    ∀ k j : ℕ, j+k≤n → ContDiffOn ℝ k (fun t => ∫ v in Icc c d,F j t v) (Icc a b) := by
  -- Induct on `k`; the recursive step uses the previous-stage assertion.
  intro k
  induction k with
  | zero =>
    intro j hj
    exact contDiffOn_zero.mpr (continuousOn_compact_integral (hc j (by omega)))
  | succ k ih =>
    intro j hj
    have hdiff := hasDerivWithinAt_compact_integral hab (hc j (by omega))
      (hc (j+1) (by omega)) (hd j (by omega))
    rw [show ((k+1:ℕ):ℕ∞ω)=(k:ℕ∞ω)+1 by simp,
      contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)]
    refine ⟨fun t ht => (hdiff t ht).differentiableWithinAt,by simp,?_⟩
    exact (ih (j+1) (by omega)).congr
      (fun t ht => (hdiff t ht).derivWithin (uniqueDiffOn_Icc hab t ht))

end
end chebyshev2.Calculus
