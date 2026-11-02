import bezout.Synthesis.Coefficients
import chebyshev1.Chebyshev.Normalization

/-!
Article: bezout, Theorem 2.1, the normalized coordinates `q_s(eta)=1`.
Use: transports a graded basis in the Chebyshev coordinate to physical query
polynomials at the zero Hessian, where causal coefficient synthesis applies.
Proof: affine substitution has degree one and evaluates to `eta` at zero.
-/

namespace bezout
noncomputable section
open Polynomial

namespace GradedFamily
variable {N : ℕ} (Q : GradedFamily N)

/-- Reexpress the graded Chebyshev-coordinate basis in physical spectral coordinates.
Use: the coordinate change in the converse direction of Theorem 2.1. -/
def physical (I : chebyshev1.SpectralInterval) : GradedFamily N where
  poly s := (Q.poly s).comp (C I.eta - C (2 / I.delta) * X)
  degree_eq s := by
    have hc : (2 / I.delta : ℝ) ≠ 0 := div_ne_zero (by norm_num) (ne_of_gt I.delta_pos)
    have hd : (C I.eta - C (2 / I.delta) * X : ℝ[X]).degree = 1 := by
      rw [← neg_sub, degree_neg, degree_sub_C (by simp [degree_C_mul_X hc]),
        degree_C_mul_X hc]
    rw [degree_comp (by rw [hd]; norm_num), hd, mul_one, Q.degree_eq s]

/-- A basis normalized at `eta` gives a physically normalized causal query family.
Use: reconstructs a history directly from the exact input data in Theorem 2.1. -/
def normalizedPhysical (I : chebyshev1.SpectralInterval)
    (hQ : ∀ s, (Q.poly s).eval I.eta = 1) : NormalizedFamily N where
  toGradedFamily := Q.physical I
  eval_zero s := by
    simp only [physical, eval_comp, eval_sub, eval_C, eval_mul, eval_X, mul_zero, sub_zero]
    exact hQ s

/-- The affine coordinate transport agrees with the article's spectral coordinate.
Use: transfers physical responses and the synthesized basis back to `[-1,1]`. -/
theorem physical_eval (I : chebyshev1.SpectralInterval) (s : Fin N) (lam : ℝ) :
    ((Q.physical I).poly s).eval lam = (Q.poly s).eval (I.z lam) := by
  simp only [physical, eval_comp, eval_sub, eval_C, eval_mul, eval_X]
  rw [I.z_eq]

/-- The inverse affine spectral coordinate, from `[-1,1]` to `[mu,L]`.
Use: returns synthesized physical queries to the input Chebyshev-coordinate basis. -/
def chart (I : chebyshev1.SpectralInterval) : ℝ[X] :=
  C ((I.L + I.mu) / 2) - C (I.delta / 2) * X

/-- The physical coordinate and its inverse compose to the identity polynomial.
Use: proves recovery of the input normalized factorization after synthesis. -/
theorem coordinate_comp_chart (I : chebyshev1.SpectralInterval) :
    (C I.eta - C (2 / I.delta) * X : ℝ[X]).comp (chart I) = X := by
  have hd : I.delta ≠ 0 := ne_of_gt I.delta_pos
  have hzero : I.eta - (2 / I.delta) * ((I.L + I.mu) / 2) = 0 := by
    unfold chebyshev1.SpectralInterval.eta
    field_simp
    ring
  have hone : (2 / I.delta) * (I.delta / 2) = 1 := by field_simp
  have hc0 : C I.eta - C (2 / I.delta) * C ((I.L + I.mu) / 2) = (0 : ℝ[X]) := by
    rw [← C_mul, ← C_sub, hzero, C_0]
  have hc1 : C (2 / I.delta) * C (I.delta / 2) = (1 : ℝ[X]) := by
    rw [← C_mul, hone, C_1]
  simp only [sub_comp, mul_comp, C_comp, X_comp, chart]
  calc
    _ = (C I.eta - C (2 / I.delta) * C ((I.L + I.mu) / 2)) +
        (C (2 / I.delta) * C (I.delta / 2)) * X := by ring
    _ = X := by rw [hc0, hc1]; simp

/-- The inverse coordinate also composes in the opposite order.
Use: transfers physical polynomial equalities back to the original spectral variable. -/
theorem chart_comp_coordinate (I : chebyshev1.SpectralInterval) :
    (chart I).comp (C I.eta - C (2 / I.delta) * X) = X := by
  have hd : I.delta ≠ 0 := ne_of_gt I.delta_pos
  have hzero : (I.L + I.mu) / 2 - (I.delta / 2) * I.eta = 0 := by
    unfold chebyshev1.SpectralInterval.eta
    field_simp
    ring
  have hone : (I.delta / 2) * (2 / I.delta) = 1 := by field_simp
  have hc0 : C ((I.L + I.mu) / 2) - C (I.delta / 2) * C I.eta = (0 : ℝ[X]) := by
    rw [← C_mul, ← C_sub, hzero, C_0]
  have hc1 : C (I.delta / 2) * C (2 / I.delta) = (1 : ℝ[X]) := by
    rw [← C_mul, hone, C_1]
  simp only [chart, sub_comp, mul_comp, C_comp, X_comp]
  calc
    _ = (C ((I.L + I.mu) / 2) - C (I.delta / 2) * C I.eta) +
        (C (I.delta / 2) * C (2 / I.delta)) * X := by ring
    _ = X := by rw [hc0, hc1]; simp

/-- Synthesis in physical coordinates loses none of the prescribed basis data.
Use: the original `q_s` are recovered, rather than only an equivalent nominal terminal. -/
theorem physical_comp_chart (I : chebyshev1.SpectralInterval) (s : Fin N) :
    ((Q.physical I).poly s).comp (chart I) = Q.poly s := by
  change ((Q.poly s).comp _).comp _ = _
  rw [comp_assoc, coordinate_comp_chart, comp_X]

end GradedFamily
end
end bezout
