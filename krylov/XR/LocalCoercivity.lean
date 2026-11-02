import krylov.XR.LocalWindowBounds

/-!
Article: main_krylov, apG:local(a), genuine rectangular-model inverse domains.
Use: quantitative physical step independence and true Hessian positivity
imply coercivity and inverse bounds for the observed nonsymmetric solve.
Source: finite-dimensional coercivity, Cauchy--Schwarz, and actual model-error
estimates. These inverses are derived from the primitive observed data.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Quadratic forms of any real matrix are bounded by the true Euclidean
operator norm, also when the matrix is nonsymmetric. -/
theorem coefficient_quadratic_norm_bound (M : Matrix (Fin p) (Fin p) ℝ)
    (c : Fin p → ℝ) :
    |c ⬝ᵥ (M *ᵥ c)| ≤ ‖M‖ * ‖WithLp.toLp 2 c‖ ^ 2 := by
  have hi := norm_inner_le_norm (𝕜 := ℝ) (WithLp.toLp 2 c)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) M (WithLp.toLp 2 c))
  rw [Real.norm_eq_abs, Matrix.inner_toEuclideanCLM] at hi
  have ho := (Matrix.toEuclideanCLM (𝕜 := ℝ) M).le_opNorm (WithLp.toLp 2 c)
  rw [Matrix.l2_opNorm_toEuclideanCLM] at ho
  calc
    _ ≤ ‖WithLp.toLp 2 c‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M (WithLp.toLp 2 c)‖ := by
      simpa only [star_trivial] using hi
    _ ≤ ‖M‖ * ‖WithLp.toLp 2 c‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left ho (norm_nonneg (WithLp.toLp 2 c))]

/-- Genuine coefficient coercivity implies the actual least-gain bound. -/
theorem coefficient_gain_of_coercivity (M : Matrix (Fin p) (Fin p) ℝ)
    (c : ℝ) (_hc : 0 < c)
    (hM : ∀ w : Fin p → ℝ, c * ‖WithLp.toLp 2 w‖ ^ 2 ≤ w ⬝ᵥ (M *ᵥ w))
    (w : Fin p → ℝ) :
    c * ‖WithLp.toLp 2 w‖ ≤ ‖WithLp.toLp 2 (M *ᵥ w)‖ := by
  have hi := real_inner_le_norm (WithLp.toLp 2 w)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) M (WithLp.toLp 2 w))
  rw [Matrix.inner_toEuclideanCLM] at hi
  by_cases hw : w = 0
  · simp [hw]
  · have hn : 0 < ‖WithLp.toLp 2 w‖ := norm_pos_iff.mpr
      (fun hz => hw ((WithLp.toLp_injective 2) hz))
    have hb := (hM w).trans hi
    change c * ‖WithLp.toLp 2 w‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M (WithLp.toLp 2 w)‖
    nlinarith

/-- Coercivity proves both nonsingularity and the quantitative inverse
bound for the actual nonsymmetric coefficient matrix. -/
theorem coefficient_inverse_of_coercivity (M : Matrix (Fin p) (Fin p) ℝ)
    (c : ℝ) (hc : 0 < c)
    (hM : ∀ w : Fin p → ℝ, c * ‖WithLp.toLp 2 w‖ ^ 2 ≤ w ⬝ᵥ (M *ᵥ w)) :
    IsUnit M.det ∧ ‖M⁻¹‖ ≤ c⁻¹ := by
  have hinj : Function.Injective M.mulVec := by
    intro u v huv
    have he : M *ᵥ (u - v) = 0 := by rw [mulVec_sub, huv, sub_self]
    have hb := coefficient_gain_of_coercivity M c hc hM (u - v)
    rw [he, WithLp.toLp_zero, norm_zero] at hb
    have hz : ‖WithLp.toLp 2 (u - v)‖ = 0 := by
      nlinarith [norm_nonneg (WithLp.toLp 2 (u - v))]
    exact sub_eq_zero.mp ((WithLp.toLp_injective 2) (norm_eq_zero.mp hz))
  have hunit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  refine ⟨hunit, ?_⟩
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le)
  intro v
  let z : EuclideanSpace ℝ (Fin p) := WithLp.toLp 2 (M⁻¹ *ᵥ WithLp.ofLp v)
  have he : M *ᵥ WithLp.ofLp z = WithLp.ofLp v := by
    change M *ᵥ (M⁻¹ *ᵥ WithLp.ofLp v) = _
    rw [mulVec_mulVec, mul_nonsing_inv _ hunit, one_mulVec]
  have hb := coefficient_gain_of_coercivity M c hc hM (WithLp.ofLp z)
  rw [he] at hb
  change ‖z‖ ≤ c⁻¹ * ‖v‖
  change c * ‖z‖ ≤ ‖v‖ at hb
  have hdiv : ‖z‖ ≤ ‖v‖ / c := (le_div_iff₀ hc).2 (by nlinarith [hb])
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

/-- Primitive true-Hessian positivity and physical normalized-column
independence supply coercivity of the exact reference coefficient Gram. -/
theorem localReferenceGram_coercive (H : E →L[ℝ] E) (s : Fin p → E)
    (mu sigma : ℝ) (hmu : 0 ≤ mu)
    (hH : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v))
    (hs : ∀ w : Fin p → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖combine s w‖ ^ 2)
    (w : Fin p → ℝ) :
    mu * sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤ w ⬝ᵥ (localReferenceGram H s *ᵥ w) := by
  rw [localReferenceGram, operatorGram_form, real_inner_comm]
  calc
    _ ≤ mu * ‖combine s w‖ ^ 2 := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hs w) hmu
    _ ≤ _ := hH _

/-- A genuine norm perturbation of a coercive reference form preserves
the corresponding quantitative coefficient lower bound. -/
theorem coefficient_coercivity_of_error (M A : Matrix (Fin p) (Fin p) ℝ)
    (a b : ℝ) (hA : ∀ w : Fin p → ℝ, a * ‖WithLp.toLp 2 w‖ ^ 2 ≤ w ⬝ᵥ (A *ᵥ w))
    (he : ‖M - A‖ ≤ b) (w : Fin p → ℝ) :
    (a - b) * ‖WithLp.toLp 2 w‖ ^ 2 ≤ w ⬝ᵥ (M *ᵥ w) := by
  have hb := (coefficient_quadratic_norm_bound (M - A) w).trans
    (mul_le_mul_of_nonneg_right he (sq_nonneg _))
  rw [sub_mulVec, dotProduct_sub] at hb
  have hl := (abs_le.mp hb).1
  nlinarith [hA w]

/-- The uniform positive coefficient lower bound printed in apG:local. -/
def localCoercivity (mu sigma : ℝ) : ℝ := (3 / 4 : ℝ) * sigma ^ 2 * mu

/-- Both actual observed coefficient matrices have the same quantitative
coercivity, derived solely from true Hessian positivity, real normalized
column independence, and the actual secant error allowance. -/
theorem local_observed_coercivity (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1)
    (mu sigma epsilon : ℝ) (hmu : 0 < mu) (he : 0 ≤ epsilon)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v))
    (hindependent : ∀ w : Fin p → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖combine s w‖ ^ 2)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon)
    (hsmall : (p : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4) :
    (∀ w : Fin p → ℝ, localCoercivity mu sigma * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      w ⬝ᵥ (latest (crossGram s y) *ᵥ w)) ∧
    (∀ w : Fin p → ℝ, localCoercivity mu sigma * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      w ⬝ᵥ (crossGram y s *ᵥ w)) := by
  have hbase := localReferenceGram_coercive H s mu sigma hmu.le hpositive hindependent
  have hcoef : localCoercivity mu sigma ≤ mu * sigma ^ 2 - (p : ℝ) * epsilon := by
    dsimp only [localCoercivity]
    nlinarith
  constructor
  · intro w
    exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)).trans
      (coefficient_coercivity_of_error _ _ _ _ hbase
        (local_latest_error_norm H hH s y hs he hy) w)
  · intro w
    exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)).trans
      (coefficient_coercivity_of_error _ _ _ _ hbase
        (local_conjugacy_error_norm H s y hs he hy) w)

/-- Actual latest-model positivity and both actual inverse domains, with
their uniform printed coercivity constant. These are not model premises. -/
theorem local_observed_domains (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (s y : Fin p → E) (hs : ∀ i, ‖s i‖ = 1)
    (mu sigma epsilon : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma) (he : 0 ≤ epsilon)
    (hpositive : ∀ v : E, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v))
    (hindependent : ∀ w : Fin p → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖combine s w‖ ^ 2)
    (hy : ∀ i, ‖y i - H (s i)‖ ≤ epsilon)
    (hsmall : (p : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4) :
    (latest (crossGram s y)).PosDef ∧
      IsUnit (crossGram y s).det ∧
      ‖(latest (crossGram s y))⁻¹‖ ≤ (localCoercivity mu sigma)⁻¹ ∧
      ‖(crossGram y s)⁻¹‖ ≤ (localCoercivity mu sigma)⁻¹ := by
  have hc : 0 < localCoercivity mu sigma := by unfold localCoercivity; positivity
  have hco := local_observed_coercivity H hH s y hs mu sigma epsilon hmu he
    hpositive hindependent hy hsmall
  have hT := coefficient_inverse_of_coercivity (latest (crossGram s y)) _ hc hco.1
  have hA := coefficient_inverse_of_coercivity (crossGram y s) _ hc hco.2
  refine ⟨?_, hA.1, hT.2, hA.2⟩
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_iff_isSymm.mpr (latest_isSymm _))
  intro w hw
  have hn : 0 < ‖WithLp.toLp 2 w‖ ^ 2 := sq_pos_of_pos
    (norm_pos_iff.mpr (fun hz => hw ((WithLp.toLp_injective 2) hz)))
  simpa only [star_trivial] using (mul_pos hc hn).trans_le (hco.1 w)

end
end krylov.XR
