import jacobi.Continuum.Moments

/-!
Article: jacobi, Appendix D.1 (strict concentration gain).
The cyclic multiple integrals are expressed as nested one-dimensional integrals.
Each extra link contributes exactly m(z) exp(-|x-z|); closing the last link yields
the article's product with x_(p+1) = x_1. The operator identification proves these
are actual spectral moments, with integrability justified before exchanging sums.
Use: expresses the cycle integral without choosing coordinates on a product space.
-/

namespace jacobi.Continuum
noncomputable section
open chebyshev2.Continuum MeasureTheory Real
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Repeated exponential links, with one density integration per additional link.
Use: expresses the cycle integral without choosing coordinates on a product space.
Article: jacobi, Appendix D.1 (strict concentration gain).
-/
def chainKernel (m : ℝ → ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, x, y => exp (-|x-y|)
  | n+1, x, y => ∫ z, m z * (exp (-|x-z|) * chainKernel m n z y)

/-- The nested link integral is a matrix coefficient of an actual operator power.
Use: connects the cyclic density integral to the trace-class spectral theory.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: the feature inner product supplies the first link; each operator application
introduces precisely one density integral by the existing Bochner identity. -/
theorem chainKernel_eq {m : ℝ → ℝ} (hm : Integrable m) (n : ℕ) (x y : ℝ) :
    chainKernel m n x y =
      inner ℝ (feature x) ((densityOperator m ^ n) (feature y)) := by
  induction n generalizing x y with
  | zero => simp [chainKernel, feature_inner]
  | succ n ih =>
    rw [chainKernel, pow_succ', mul_apply_eq_comp, densityOperator_inner hm]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      dsimp only
      rw [ih, feature_inner, abs_sub_comm z x]

/-- The trace of T^(p+1) is the density integral of the diagonal coefficient of T^p.
Use: closing the link integral gives every cyclic moment of Section 6.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: integrate the nonnegative eigenbasis expansion, using the operator-norm
majorant for domination; the density pairing changes each λ^p into λ^(p+1). -/
theorem moment_diagonal_integral {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    {p : ℕ} (hp : 0 < p) :
    (∑' j, kernelEigenvalue hm hn j^(p+1)) =
      ∫ x, m x * inner ℝ (feature x) ((densityOperator m ^ p) (feature x)) := by
  let T := densityOperator m
  let D := densitySpectralData hm hn
  let : Countable D.Index := orthonormal_countable D.basis.orthonormal
  let DP := powerData D hp
  have hquad (x : ℝ) : HasSum (fun i => D.eig i^p * inner ℝ (feature x) (D.basis i)^2)
      (inner ℝ (feature x) ((T^p) (feature x))) := by
    simpa only [DP, powerData, real_inner_comm (D.basis _) (feature x)] using
      eigenbasis_quadratic_hasSum DP.basis (T^p) DP.equation (feature x)
  have hsum (x : ℝ) := (hquad x).mul_left (m x)
  have hb (x : ℝ) : |inner ℝ (feature x) ((T^p) (feature x))| ≤ ‖T^p‖ := by
    calc
      _ ≤ ‖feature x‖ * ‖(T^p) (feature x)‖ := abs_real_inner_le_norm _ _
      _ = ‖(T^p) (feature x)‖ := by rw [feature_norm, one_mul]
      _ ≤ ‖T^p‖ := by simpa only [feature_norm, mul_one] using (T^p).le_opNorm (feature x)
  have hint : Integrable (fun x => m x * inner ℝ (feature x) ((T^p) (feature x))) := by
    apply (hm.norm.mul_const ‖T^p‖).mono'
    · exact hm.aestronglyMeasurable.mul
        (feature_continuous.inner ((T^p).continuous.comp feature_continuous)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)
  -- Absolute integrability of the limiting quadratic coefficient licenses the exchange.
  have hi := hasSum_integral_of_dominated_convergence
    (F := fun i x => m x * (D.eig i^p * inner ℝ (feature x) (D.basis i)^2))
    (f := fun x => m x * inner ℝ (feature x) ((T^p) (feature x))) (μ := volume)
    (fun i x => m x * (D.eig i^p * inner ℝ (feature x) (D.basis i)^2))
    (fun i => hm.aestronglyMeasurable.mul
      (aestronglyMeasurable_const.mul ((feature_continuous.inner continuous_const).pow 2).aestronglyMeasurable))
    (fun i => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (hn x) (mul_nonneg (pow_nonneg (D.nonneg i) p) (sq_nonneg _)))])
    (Filter.Eventually.of_forall fun x => (hsum x).summable)
    (by
      have he : (fun x => ∑' i, m x * (D.eig i^p * inner ℝ (feature x) (D.basis i)^2)) =
          (fun x => m x * inner ℝ (feature x) ((T^p) (feature x))) :=
        funext (fun x => (hsum x).tsum_eq)
      rw [he]
      exact hint)
    (Filter.Eventually.of_forall hsum)
  have he (i : D.Index) :
      (∫ x, m x * (D.eig i^p * inner ℝ (feature x) (D.basis i)^2)) = D.eig i^(p+1) := by
    have hd := D.diagonal_eq i
    rw [densityOperator_inner hm] at hd
    have hf : (fun x => m x * (D.eig i^p * inner ℝ (feature x) (D.basis i)^2)) =
        (fun x => D.eig i^p * (m x *
          (inner ℝ (feature x) (D.basis i) * inner ℝ (feature x) (D.basis i)))) := by
      funext x
      ring
    rw [hf, integral_const_mul, hd, pow_succ]
  simp only [he] at hi
  have hsort := (spectralSorted_moment D.summable D.nonneg (fun a => a^(p+1))
    (by simp) (fun a ha => pow_nonneg ha _) hi.summable).2
  rw [← density_kernel_eigenvalue_eq hm hn D]
  change (∑' j, spectralSorted D.summable j^(p+1)) = _
  rw [hsort]
  exact hi.tsum_eq

/-- All positive integer spectral moments equal the corresponding cyclic density integrals.
Use: defines the actual spectral constraints for arbitrary edge spectra.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: the first moment is the mass; higher moments close the operator link expansion. -/
theorem moment_cycle {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    {p : ℕ} (hp : 0 < p) :
    (∑' j, kernelEigenvalue hm hn j^p) = ∫ x, m x * chainKernel m (p-1) x x := by
  -- Separate the trace case from higher powers before closing the operator path.
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  cases n with
  | zero => simpa [chainKernel] using kernelEigenvalue_mass hm hn
  | succ n =>
    rw [moment_diagonal_integral hm hn (by omega : 0 < n+1)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [Nat.succ_sub_one, chainKernel_eq hm]

end
end jacobi.Continuum
