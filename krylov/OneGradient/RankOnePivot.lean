import krylov.LinearAlgebra.PositiveCauchy
import krylov.LinearAlgebra.NormalizedRankOne
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(a,c).
Use: characterize genuine positive rank-one fibre completions and their exact
relative-ball interval, using the original inverse quadratic form.
Source: the already proved positive-metric Cauchy--Schwarz inequality and
exact physical rank-one spectral norm; all strict positivity cases are proved here.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Secant krylov.LinearAlgebra
variable {n : ℕ}

/-- A physical rank-one update is positive exactly while its single inverse
quadratic pivot stays positive.
Use: determine the whole admissible half-line of the actual information fibre.
Article: main_krylov, s5:fibre(a).
Proof: testing at A⁻¹z proves necessity. For sufficiency, positive-metric
Cauchy--Schwarz bounds a negative rank-one update; a nonnegative update is immediate. -/
theorem rank_one_positive_iff (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (z : Fin n → ℝ) (hz : z≠0) (t : ℝ) :
    (A+t • vecMulVec z z).PosDef ↔ 0<1+t*(z ⬝ᵥ (A⁻¹*ᵥ z)) := by
  let u := A⁻¹*ᵥ z
  let h := z ⬝ᵥ u
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hu : A*ᵥ u=z := by dsimp only [u];rw [mulVec_mulVec,mul_nonsing_inv A hd,one_mulVec]
  have hun : u≠0 := by intro h0;exact hz (hu.symm.trans (by rw [h0,mulVec_zero]))
  have hh : 0<h := by simpa only [h,u,star_trivial] using hA.inv.dotProduct_mulVec_pos hz
  have hpair (v : Fin n → ℝ) : u ⬝ᵥ (A*ᵥ v)=z ⬝ᵥ v := by
    have hs := hA.1.star_dotProduct_mulVec_comm u v
    simpa only [star_trivial,hu,dotProduct_comm] using hs
  have hform (v : Fin n → ℝ) :
      v ⬝ᵥ ((A+t • vecMulVec z z)*ᵥ v)=v ⬝ᵥ (A*ᵥ v)+t*(z ⬝ᵥ v)^2 := by
    simp only [add_mulVec,smul_mulVec,krylov.Secant.outer_mulVec,dotProduct_add,
      dotProduct_smul,smul_smul,smul_eq_mul]
    rw [dotProduct_comm v z]
    ring
  constructor
  · intro hpos
    have hp := hpos.dotProduct_mulVec_pos hun
    simp only [star_trivial,hform,hu,dotProduct_comm u z] at hp
    change 0<1+t*h
    change 0<h+t*h^2 at hp
    nlinarith
  · intro hcrit
    have hsym : (A+t • vecMulVec z z).IsHermitian :=
      hA.1.add ((Matrix.posSemidef_vecMulVec_self_star z).1.smul (show IsSelfAdjoint t from rfl))
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa only [star_trivial] using hsym)
    intro v hv
    simp only [star_trivial,hform]
    have hq : 0<v ⬝ᵥ (A*ᵥ v) := by simpa only [star_trivial] using hA.dotProduct_mulVec_pos hv
    by_cases ht : 0≤t
    · exact add_pos_of_pos_of_nonneg hq (mul_nonneg ht (sq_nonneg _))
    · have hc := positive_cauchy A hA u v
      rw [hpair,hu,dotProduct_comm u z] at hc
      have hm := mul_le_mul_of_nonpos_left hc (le_of_not_ge ht)
      have hp := mul_pos hcrit hq
      change 0<(1+t*h)*(v ⬝ᵥ (A*ᵥ v)) at hp
      nlinarith

/-- The genuine relative norm of a physical rank-one completion is its absolute
scalar coefficient times the actual inverse quadratic form.
Use: compute the exact centre-fibre interval of a known relative base ball.
Article: main_krylov, s5:fibre(c).
Proof: the real inverse root transports the generating vector; reuse its exact
rank-one spectral norm and the proved inverse-root energy identity. -/
theorem rank_one_relative_budget (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (z : Fin n → ℝ) (t : ℝ) :
    relativeBudget A (t • vecMulVec z z)=|t| *(z ⬝ᵥ (A⁻¹*ᵥ z)) := by
  have hs : ((metricRoot A)⁻¹).IsSymm := (metricRoot_isSymm A).inv
  rw [relativeBudget,relativeOperator_smul,relativeOperator,rankOne_inverse_congruence _ hs,
    chebyshev1.opNorm_smul,spectral_norm_rankOne,← pow_two,inverseRoot_energy A hA]

/-- The relative ball intersects the entire rank-one line in the exact closed
interval, including zero radius.
Use: both endpoint completions are admitted, rather than merely bounded above.
Article: main_krylov, s5:fibre(c).
Proof: use the exact physical relative norm and clear its positive actual inverse energy. -/
theorem rank_one_ball_interval (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (z : Fin n → ℝ) (hz : z≠0) (rho t : ℝ) :
    relativeBudget A (t • vecMulVec z z)≤rho ↔
      -(rho/(z ⬝ᵥ (A⁻¹*ᵥ z)))≤t ∧ t≤rho/(z ⬝ᵥ (A⁻¹*ᵥ z)) := by
  have hh : 0<z ⬝ᵥ (A⁻¹*ᵥ z) := by simpa only [star_trivial] using hA.inv.dotProduct_mulVec_pos hz
  rw [rank_one_relative_budget A hA,← le_div_iff₀ hh,abs_le]

/-- Every point of a relative ball of radius below one is a genuine positive
rank-one completion, including both closed interval endpoints.
Use: discharge actual positive-definiteness of the central-fibre scenarios.
Article: main_krylov, s5:fibre(c).
Proof: the exact norm bound controls the only strict inverse pivot away from zero. -/
theorem rank_one_ball_positive (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (z : Fin n → ℝ) (hz : z≠0) {rho t : ℝ} (hrho : rho<1)
    (hbudget : relativeBudget A (t • vecMulVec z z)≤rho) :
    (A+t • vecMulVec z z).PosDef := by
  rw [rank_one_positive_iff A hA z hz]
  rw [rank_one_relative_budget A hA] at hbudget
  have hh : 0≤z ⬝ᵥ (A⁻¹*ᵥ z) := by simpa only [star_trivial] using hA.inv.posSemidef.dotProduct_mulVec_nonneg z
  have hn := mul_le_mul_of_nonneg_right (neg_abs_le t) hh
  nlinarith

end
end krylov.OneGradient
