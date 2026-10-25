import polyak.Interpolation.Data
import polyak.Waves.Complex

/-!
Article: Appendix A, Lemma energy, the separation into quadratic and value terms.
Use: exact local identities for the original interpolation inequalities, including
the uniform bound on the sampled values. No recurrence or spectral ansatz is assumed.
Proof: homogeneity of the real inner product and the minimizer interpolation inequality.
-/

noncomputable section

namespace polyak.Energy

open Interpolation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: the quadratic part of `R ± T`. Use: both signs are retained explicitly. -/
def pairQuadratic (δ : ℝ) (x y σ τ : E) : ℝ :=
  (1 / 4 : ℝ) * (‖y - x‖ ^ 2 - ‖τ - σ‖ ^ 2) -
    δ / 2 * inner ℝ (σ + τ) (y - x)

/-- Article: the quadratic part of the minimizer inequality. -/
def starQuadratic (δ : ℝ) (x σ : E) : ℝ :=
  (1 / 4 : ℝ) * (‖x‖ ^ 2 - ‖σ‖ ^ 2) - δ / 2 * inner ℝ σ x

/-- Article: the signed pair slack. Proof: separate the prescribed values from `T`. -/
theorem pair_slack_eq {I : Type*} (x σ : I → E) (v : I → ℝ) (i j : I) (δ : ℝ) :
    datumR x σ i j + δ * datumT x σ v i j =
      pairQuadratic δ (x i) (x j) (σ i) (σ j) + δ * (v j - v i) := by
  simp only [datumR, datumT, pairQuadratic]
  ring

/-- Article: the signed minimizer slack. Proof: use the actual zero datum. -/
theorem star_slack_eq {I : Type*} (x σ : I → E) (v : I → ℝ) (star i : I)
    (hx : x star = 0) (hσ : σ star = 0) (hv : v star = 0) (δ : ℝ) :
    datumR x σ star i + δ * datumT x σ v star i =
      starQuadratic δ (x i) (σ i) + δ * v i := by
  simp only [datumR, datumT, hx, hσ, hv, sub_zero, zero_add, starQuadratic]
  ring

/-- Article: the minimizer inequality controls every value by half the squared norm.
Use: bounds the uncancelled values in the boundary windows of the energy estimate.
Proof: the signed interpolation inequality and Young's inequality for the inner product. -/
theorem abs_value_le_half_sq {x σ : E} {v : ℝ}
    (h : |v - (1 / 2 : ℝ) * inner ℝ σ x| ≤
      (1 / 4 : ℝ) * (‖x‖ ^ 2 - ‖σ‖ ^ 2)) : |v| ≤ (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
  have hin := abs_real_inner_le_norm σ x
  have hyoung : (1 / 2 : ℝ) * |inner ℝ σ x| ≤
      (1 / 4 : ℝ) * (‖x‖ ^ 2 + ‖σ‖ ^ 2) := by
    have := sq_nonneg (‖x‖ - ‖σ‖)
    nlinarith
  calc
    |v| = |(v - (1 / 2 : ℝ) * inner ℝ σ x) +
        (1 / 2 : ℝ) * inner ℝ σ x| := by congr 1; ring
    _ ≤ |v - (1 / 2 : ℝ) * inner ℝ σ x| +
        |(1 / 2 : ℝ) * inner ℝ σ x| := abs_add_le _ _
    _ ≤ (1 / 4 : ℝ) * (‖x‖ ^ 2 - ‖σ‖ ^ 2) +
        (1 / 4 : ℝ) * (‖x‖ ^ 2 + ‖σ‖ ^ 2) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact add_le_add h hyoung
    _ = _ := by ring

/-- Article: the same value bound for an arbitrary feasible table.
Proof: specialize feasibility to the minimizer pair. -/
theorem table_abs_value_le_half_sq {I : Type*} {x σ : I → E} {v : I → ℝ}
    (h : TableFeasible x σ v) (star : I) (hx : x star = 0)
    (hσ : σ star = 0) (hv : v star = 0) (i : I) :
    |v i| ≤ (1 / 2 : ℝ) * ‖x i‖ ^ 2 := by
  apply abs_value_le_half_sq
  simpa only [datumT, datumR, hx, hσ, hv, sub_zero, zero_add] using h star i

/-- Article: discounting preserves the quadratic part exactly.
Use: there are no error terms in passing from positions to discounted positions.
Proof: squared homogeneity and bilinearity; the discount can be any real scalar. -/
theorem pairQuadratic_smul (r δ : ℝ) (x y σ τ : E) :
    pairQuadratic δ (r • x) (r • y) (r • σ) (r • τ) =
      r ^ 2 * pairQuadratic δ x y σ τ := by
  simp only [pairQuadratic, ← smul_sub, ← smul_add, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Article: discounting the minimizer quadratic has the same degree two homogeneity. -/
theorem starQuadratic_smul (r δ : ℝ) (x σ : E) :
    starQuadratic δ (r • x) (r • σ) = r ^ 2 * starQuadratic δ x σ := by
  simp only [starQuadratic, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- Article: Young's boundary estimate for a real Hilbert inner product.
Use: every omitted quadratic term is controlled by squared norms in its window. -/
theorem abs_inner_le_half_sq (x y : E) :
    |inner ℝ x y| ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  have := abs_real_inner_le_norm x y
  have := sq_nonneg (‖x‖ - ‖y‖)
  nlinarith

end polyak.Energy
