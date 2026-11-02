import jacobi.Variational.GreenParameter

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
The actual parameter derivative is a nonnegative Green-product integral.
Therefore each kernel entry increases with a nonnegative subcritical
coupling. This comparison supplies a single upper endpoint kernel for
dominating all spatial determinant derivatives on a compact parameter interval.
Source: the proved actual inverse derivative and the mean value theorem.
Use: a fixed upper endpoint inverse dominates the whole family when differentiating the spatial determinant integral.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every actual Green kernel entry increases along a nonnegative subcritical parameter interval.
Use: a fixed upper endpoint inverse dominates the whole family when differentiating the spatial determinant integral.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the actual kernel parameter derivative is twice an integral of
three nonnegative factors. Apply the mean value theorem on the compact
coupling interval and identify both endpoint parameter kernels with the actual inverses. -/
theorem L1Source.greenParameter_monotone (m : L1Source) {b : ℝ}
    (hp : b*observe m .top<1) (x y : ℝ) :
    MonotoneOn (fun t => m.greenParameter t x y) (Icc (0:ℝ) b) := by
  -- Actual spectral ordering keeps every parameter in the same subcritical domain.
  have htop : 0≤observe m .top := (chebyshev2.Continuum.kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg 0
  have hmargin (t : ℝ) (ht : t∈Icc (0:ℝ) b) : t*observe m .top<1 :=
    (mul_le_mul_of_nonneg_right ht.2 htop).trans_lt hp
  have hc : ContinuousOn (fun t => m.greenParameter t x y) (Icc (0:ℝ) b) :=
    fun t ht => (m.greenParameter_hasDerivAt ht.1 (hmargin t ht) x y).continuousAt.continuousWithinAt
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 b) hc
  · intro t ht
    exact (m.greenParameter_hasDerivAt (interior_subset ht).1
      (hmargin t (interior_subset ht)) x y).differentiableAt.differentiableWithinAt
  intro t ht
  have ht' : t∈Icc (0:ℝ) b := interior_subset ht
  rw [(m.greenParameter_hasDerivAt ht'.1 (hmargin t ht') x y).deriv]
  apply mul_nonneg (by norm_num)
  exact integral_nonneg fun z => mul_nonneg
    (mul_nonneg (m.nonneg z) (m.fredholmGreen_pos ht'.1 (hmargin t ht') x z).le)
    (m.fredholmGreen_pos ht'.1 (hmargin t ht') y z).le

/-- Two actual subcritical Green kernels obey pointwise comparison at ordered nonnegative couplings.
Use: bounds every variable-parameter Green ratio by one fixed actual upper endpoint kernel.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: use the proved parameter monotonicity and the exact inverse identification at the two endpoints. -/
theorem L1Source.fredholmGreen_mono_parameter (m : L1Source) {s b : ℝ} (hs : 0≤s) (hsb : s≤b)
    (hp : b*observe m .top<1) (x y : ℝ) :
    m.fredholmGreen s hs (by
      have hn := (chebyshev2.Continuum.kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg 0
      exact (mul_le_mul_of_nonneg_right hsb hn).trans_lt hp) x y≤
      m.fredholmGreen b (hs.trans hsb) hp x y := by
  have h := m.greenParameter_monotone hp x y ⟨hs,hsb⟩ ⟨hs.trans hsb,le_rfl⟩ hsb
  dsimp only at h
  rwa [m.greenParameter_eq hs _,m.greenParameter_eq (hs.trans hsb) hp] at h

end
end jacobi.Variational
