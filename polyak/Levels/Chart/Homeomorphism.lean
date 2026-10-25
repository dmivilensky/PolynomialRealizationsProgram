import polyak.Levels.Chart.Recovery
import polyak.Levels.Chart.Continuity
import polyak.Levels.Chart.Factor

/-! Proposition chart(a): a proved homeomorphism, with an actual inverse
constructed by the unique stable secular root. -/
noncomputable section
namespace polyak.Levels.Chart
open General

abbrev PositiveTuning := {q : Tuning // 0<q.beta}

def coefficientHomeomorph : PositiveTuning ≃ₜ CoefficientPoint where
  toFun q := coefficientPoint q.val q.property
  invFun C := ⟨inverseTuning C,inverseBeta_pos C⟩
  left_inv q := Subtype.ext (inverseTuning_coefficientPoint q.val q.property)
  right_inv C := Subtype.ext (coefficients_inverseTuning C)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_coefficients.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_inverseTuning

theorem coefficients_injective {q p : Tuning} (hq : 0<q.beta) (hp : 0<p.beta)
    (he : coefficients q=coefficients p) : q=p := by
  have hh : coefficientHomeomorph ⟨q,hq⟩=coefficientHomeomorph ⟨p,hp⟩ := Subtype.ext he
  exact congrArg Subtype.val (coefficientHomeomorph.injective hh)

theorem coefficients_surjective (C : Coefficients) (hC : C∈CoeffDomain) :
    ∃ q : Tuning,0<q.beta ∧ coefficients q=C :=
  ⟨inverseTuning ⟨C,hC⟩,inverseBeta_pos ⟨C,hC⟩,coefficients_inverseTuning ⟨C,hC⟩⟩

/-- The source stable factor has actual roots in the open disk. -/
theorem inverse_a_roots_stable (C : CoefficientPoint) {z : ℂ}
    (hz : (inverseTuning C).a z=0) : ‖z‖<1 := (inverseTuning C).a_root_stable hz

/-- The reversed second factor has its roots outside the closed disk. -/
theorem inverse_reversed_b_roots_outside (C : CoefficientPoint) {z : ℂ}
    (hz : z≠0) (hroot : (inverseTuning C).b z⁻¹=0) : 1<‖z‖ := by
  have hh := (inverseTuning C).b_root_stable hroot
  rw [norm_inv] at hh
  exact (inv_lt_one₀ (norm_pos_iff.mpr hz)).mp hh

/-- Every admissible source quartic has the constructed stable factorization. -/
theorem constructed_quartic_factor (C : CoefficientPoint) {z : ℂ} (hz : z≠0) :
    (2*(inverseTuning C).B*(1-(inverseTuning C).beta):ℝ)*(quartic C.val).eval z=
      -(inverseTuning C).a z*((inverseTuning C).beta*z^2-
        (1+(inverseTuning C).beta-(inverseTuning C).y:ℝ)*z+1) := by
  rw [← coefficients_inverseTuning C]
  exact quartic_factor (inverseTuning C) hz

end polyak.Levels.Chart
