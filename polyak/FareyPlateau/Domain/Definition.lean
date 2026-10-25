import polyak.FareyPlateau.Domain.Recovery

/-! The edge tuning exists exactly under the two source endpoint signs,
before any gap restriction, and D is literally Ξ′(c₀)−1. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels

theorem edge_tuning_defined_iff {c h a D : ℝ} (ha : 0<a) :
    (∃! q : Tuning,Chart.coefficients q=edgeCoefficients c h a D) ↔
      (edgeCoefficients c h a D).eval 1<0 ∧ (edgeCoefficients c h a D).eval (-1)<0 := by
  constructor
  · rintro ⟨q,he,_⟩
    rw [←he,Chart.eval_coefficients,Chart.eval_coefficients]
    exact ⟨q.Xi_one_neg,q.Xi_neg_one_neg⟩
  · intro hh
    have hC : edgeCoefficients c h a D∈Chart.CoeffDomain :=
      ⟨neg_neg_of_pos ha,hh⟩
    let C : Chart.CoefficientPoint := ⟨edgeCoefficients c h a D,hC⟩
    refine ⟨Chart.inverseTuning C,Chart.coefficients_inverseTuning C,?_⟩
    intro q hq
    have hb : 0<q.beta := (Chart.coefficient_quadratic_neg_iff q).mp (by
      rw [hq];exact neg_neg_of_pos ha)
    apply Chart.coefficients_injective hb (Chart.inverseBeta_pos C)
    exact hq.trans (Chart.coefficients_inverseTuning C).symm

theorem edge_coordinate_derivative (q : Tuning) {c h a D : ℝ}
    (he : Chart.coefficients q=edgeCoefficients c h a D) : deriv q.Xi c=1+D := by
  have hf : q.Xi=(fun x=>h+(1+D)*(x-c)-a*(x-c)^2) := by
    funext x
    rw [←Chart.eval_coefficients,he,edgeCoefficients_eval]
  rw [hf]
  have hd := (((hasDerivAt_const c h).add
    (((hasDerivAt_id c).sub_const c).const_mul (1+D))).sub
      ((((hasDerivAt_id c).sub_const c).pow 2).const_mul a)).deriv
  convert hd using 1
  · congr 1
  · simp

end polyak.FareyPlateau
