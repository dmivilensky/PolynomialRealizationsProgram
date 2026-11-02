import bezout.Synthesis.Exactness
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Article: bezout, Theorems 3.1 and 4.1, admissible quadratic Hessians.
Use: scalar polynomial bounds control the actual action on every finite
dimensional real Hilbert space, with no dimension in the constants.
Proof: the finite real spectral theorem and an orthonormal eigenbasis.
-/

namespace bezout.Analysis
noncomputable section
open Polynomial
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An admissible real quadratic Hessian: symmetric, with every eigenvalue
in the prescribed closed interval. This includes repeated eigenvalues. -/
def Admissible (I : chebyshev1.SpectralInterval) (H : E →ₗ[ℝ] E) : Prop :=
  H.IsSymmetric ∧ ∀ x : ℝ, Module.End.HasEigenvalue H x → x ∈ Set.Icc I.mu I.L

/-- Polynomial action in orthonormal spectral coordinates is scalar evaluation. -/
theorem polynomial_spectral_coordinates (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (p : ℝ[X]) (v : E) (i : Fin (Module.finrank ℝ E)) :
    ((hH.eigenvectorBasis rfl).repr ((aeval H p) v)) i =
      p.eval (hH.eigenvalues rfl i) * ((hH.eigenvectorBasis rfl).repr v) i := by
  let B := (hH.eigenvectorBasis rfl).repr
  have hpow (n : ℕ) (w : E) :
      B ((H ^ n) w) i = (hH.eigenvalues rfl i) ^ n * B w i := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply,
        hH.eigenvectorBasis_apply_self_apply rfl]
      rw [ih]
      simp only [RCLike.ofReal_real_eq_id, id_eq]
      ring
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, eval_add, hp, hq, add_mul, PiLp.add_apply]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      LinearIsometryEquiv.map_smul, PiLp.smul_apply, smul_eq_mul, eval_monomial]
    change a * B ((H ^ n) v) i = _
    rw [hpow]
    ring

/-- A scalar uniform polynomial bound is a dimension-uniform bound on its
actual action on every admissible quadratic. -/
theorem polynomial_action_bound (I : chebyshev1.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H) (p : ℝ[X]) (C : ℝ) (hC : 0 ≤ C)
    (hp : ∀ x ∈ Set.Icc I.mu I.L, |p.eval x| ≤ C) (v : E) :
    ‖(aeval H p) v‖ ≤ C * ‖v‖ := by
  let B := (hH.1.eigenvectorBasis rfl).repr
  have hb (i : Fin (Module.finrank ℝ E)) : |p.eval (hH.1.eigenvalues rfl i)| ≤ C :=
    hp _ (hH.2 _ (hH.1.hasEigenvalue_eigenvalues rfl i))
  have hs : ‖(aeval H p) v‖ ^ 2 ≤ (C * ‖v‖) ^ 2 := by
    rw [← B.norm_map ((aeval H p) v), ← B.norm_map v,
      EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [polynomial_spectral_coordinates H hH.1 p v i]
    simp only [Real.norm_eq_abs, sq_abs, mul_pow]
    have hi := (sq_le_sq₀ (abs_nonneg _) hC).mpr (hb i)
    rw [sq_abs] at hi
    exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg v))).mp hs

/-- The continuous operator norm satisfies the same scalar polynomial bound. -/
theorem polynomial_operator_bound (I : chebyshev1.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H) (p : ℝ[X]) (C : ℝ) (hC : 0 ≤ C)
    (hp : ∀ x ∈ Set.Icc I.mu I.L, |p.eval x| ≤ C) :
    ‖(aeval H p).toContinuousLinearMap‖ ≤ C := by
  exact ContinuousLinearMap.opNorm_le_bound _ hC
    (polynomial_action_bound I H hH p C hC hp)

/-- Every admissible Hessian has norm at most the upper spectral endpoint. -/
theorem hessian_action_bound (I : chebyshev1.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H) (v : E) : ‖H v‖ ≤ I.L * ‖v‖ := by
  have hL : 0 ≤ I.L := le_of_lt (I.mu_pos.trans I.mu_lt_L)
  simpa only [aeval_X] using polynomial_action_bound I H hH X I.L hL
    (fun x hx => by simpa only [eval_X, abs_of_nonneg (I.mu_pos.le.trans hx.1)] using hx.2) v

/-- The prescribed noiseless terminal contracts by exactly the Chebyshev factor. -/
theorem residual_action_bound (I : chebyshev1.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H) (N : ℕ) (v : E) :
    ‖(aeval H (I.residual N)) v‖ ≤ I.epsilon N * ‖v‖ :=
  polynomial_action_bound I H hH _ _ (le_of_lt (one_div_pos.mpr (I.den_pos N)))
    (fun _ hx => I.residual_abs_le N hx) v

/-- Scalar Hessians at any admissible spectral point belong to the full class. -/
theorem scalar_admissible (I : chebyshev1.SpectralInterval) (x : ℝ)
    (hx : x ∈ Set.Icc I.mu I.L) : Admissible I (bezout.History.scalarOperator x) := by
  constructor
  · change (x • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).IsSymmetric
    exact LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.id
  · intro y hy
    obtain ⟨v, hv, hne⟩ := hy.exists_hasEigenvector
    have he := Module.End.mem_eigenspace_iff.mp hv
    simp only [bezout.History.scalarOperator_apply, smul_eq_mul] at he
    have hxy : x = y := mul_right_cancel₀ hne he
    simpa only [← hxy] using hx

/-- Every fixed polynomial has a finite nonnegative bound on the spectral interval.
Use: the actual worst-case risks of a fixed finite history are finite. -/
theorem exists_polynomial_bound (I : chebyshev1.SpectralInterval) (p : ℝ[X]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc I.mu I.L, |p.eval x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.image p.continuous.abs).bddAbove
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  exact (hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)

end
end bezout.Analysis
