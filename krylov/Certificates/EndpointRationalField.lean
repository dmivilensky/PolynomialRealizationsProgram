import krylov.Certificates.EndpointRationalWitness

/-!
Article: main_krylov, apC:prop:digits, actual-field interpretation of the endpoint
rational certificate. The compactification x=1/U is differentiated exactly and
its signed residual is identified with the original endpoint graph equation.
Source: quotient and chain rules, and exact rational algebra.
-/
namespace krylov.Certificates
noncomputable section
open Set
open krylov.LotkaVolterra

/-- Rational witness pulled back to the original state variable U. -/
def endpointRationalBarrier (c U : ℝ) : ℝ :=
  endpointNumerator (1/U) / endpointDenominator (1/U) + c

/-- Its literal derivative with respect to the original state variable. -/
def endpointRationalBarrierDerivative (U : ℝ) : ℝ :=
  -(endpointNumeratorDerivative (1/U) * endpointDenominator (1/U) -
    endpointNumerator (1/U) * endpointDenominatorDerivative (1/U)) /
    endpointDenominator (1/U)^2 / U^2

/-- Quotient and compactification chain rules for the actual rational witness. -/
theorem endpointRationalBarrier_hasDerivAt (c : ℝ) {U : ℝ} (hU : 0 < U) :
    HasDerivAt (endpointRationalBarrier c) (endpointRationalBarrierDerivative U) U := by
  have hq := endpointDenominator_pos (show 0 ≤ 1/U by positivity)
  have hi := (hasDerivAt_const U (1 : ℝ)).div (hasDerivAt_id U) (ne_of_gt hU)
  have hp := (endpointNumerator_hasDerivAt (1/U)).comp U hi
  have hd := (endpointDenominator_hasDerivAt (1/U)).comp U hi
  convert (hp.div hd (ne_of_gt hq)).add_const c using 1
  · rfl
  · dsimp [endpointRationalBarrierDerivative]
    ring

/-- The original field residual is exactly the certified polynomial residual
up to an explicitly positive factor. -/
theorem endpointRational_residual_identity {U c : ℝ} (hU : 0 < U)
    (hb : endpointRationalBarrier c U + 1 ≠ 0) :
    (endpointGraphRate U (endpointRationalBarrier c U) -
      endpointRationalBarrierDerivative U) * (endpointRationalBarrier c U+1) *
        endpointDenominator (1/U)^3 = endpointRationalResidual (1/U) c := by
  have hq := endpointDenominator_pos (show 0 ≤ 1/U by positivity)
  have hF : endpointGraphRate U (endpointRationalBarrier c U) *
      (endpointRationalBarrier c U+1) =
      (endpointRationalBarrier c U-3) +
        2*(1/U)*endpointRationalBarrier c U*(endpointRationalBarrier c U-1) := by
    rw [endpointGraphRate_eq (ne_of_gt hU) hb]
    field_simp [ne_of_gt hU, hb]
  calc
    _ = (endpointGraphRate U (endpointRationalBarrier c U) *
        (endpointRationalBarrier c U+1))*endpointDenominator (1/U)^3 -
        endpointRationalBarrierDerivative U*(endpointRationalBarrier c U+1)*
          endpointDenominator (1/U)^3 := by ring
    _ = _ := by
      rw [hF]
      unfold endpointRationalBarrier endpointRationalBarrierDerivative endpointRationalResidual
      field_simp [ne_of_gt hq, ne_of_gt hU]
      ring

/-- The lower rational witness lies in the comparison strip and is an actual
supersolution of the endpoint gap equation in the original U coordinate. -/
theorem endpointRational_lower_field (U : ℝ) (hU : 1 ≤ U) :
    endpointRationalBarrier (-(1/500000)) U ∈ Icc (1 : ℝ) 4 ∧
      HasDerivAt (endpointRationalBarrier (-(1/500000)))
        (endpointRationalBarrierDerivative U) U ∧
      endpointGraphRate U (endpointRationalBarrier (-(1/500000)) U) ≤
        endpointRationalBarrierDerivative U := by
  have hU₀ : 0 < U := by linarith
  have hx : (1/U : ℝ) ∈ Icc 0 1 :=
    ⟨by positivity, (div_le_one hU₀).mpr hU⟩
  have hs := endpointRational_strip hx.1
  have hb : endpointRationalBarrier (-(1/500000)) U ∈ Icc (1 : ℝ) 4 := by
    unfold endpointRationalBarrier
    constructor <;> linarith [hs.1,hs.2]
  refine ⟨hb, endpointRationalBarrier_hasDerivAt _ hU₀, ?_⟩
  have hi := endpointRational_residual_identity (c := -(1/500000)) hU₀
    (by linarith [hb.1])
  have hr := endpointRationalResidual_lower hx
  have hpos : 0 < (endpointRationalBarrier (-(1/500000)) U+1)*
      endpointDenominator (1/U)^3 := by
    exact mul_pos (by linarith [hb.1]) (pow_pos (endpointDenominator_pos hx.1) _)
  have hprod : (endpointGraphRate U (endpointRationalBarrier (-(1/500000)) U) -
      endpointRationalBarrierDerivative U)*((endpointRationalBarrier (-(1/500000)) U+1)*
        endpointDenominator (1/U)^3) ≤ 0 := by
    rw [← mul_assoc, hi]
    exact hr
  exact sub_nonpos.mp (le_of_mul_le_mul_right (by simpa only [zero_mul] using hprod) hpos)

/-- The upper rational witness is an actual subsolution of the endpoint gap
field, with the same bounded strip and explicit derivative. -/
theorem endpointRational_upper_field (U : ℝ) (hU : 1 ≤ U) :
    endpointRationalBarrier (1/500000) U ∈ Icc (1 : ℝ) 4 ∧
      HasDerivAt (endpointRationalBarrier (1/500000))
        (endpointRationalBarrierDerivative U) U ∧
      endpointRationalBarrierDerivative U ≤
        endpointGraphRate U (endpointRationalBarrier (1/500000) U) := by
  have hU₀ : 0 < U := by linarith
  have hx : (1/U : ℝ) ∈ Icc 0 1 :=
    ⟨by positivity, (div_le_one hU₀).mpr hU⟩
  have hs := endpointRational_strip hx.1
  have hb : endpointRationalBarrier (1/500000) U ∈ Icc (1 : ℝ) 4 := by
    unfold endpointRationalBarrier
    constructor <;> linarith [hs.1,hs.2]
  refine ⟨hb, endpointRationalBarrier_hasDerivAt _ hU₀, ?_⟩
  have hi := endpointRational_residual_identity (c := 1/500000) hU₀
    (by linarith [hb.1])
  have hr := endpointRationalResidual_upper hx
  have hpos : 0 < (endpointRationalBarrier (1/500000) U+1)*
      endpointDenominator (1/U)^3 := by
    exact mul_pos (by linarith [hb.1]) (pow_pos (endpointDenominator_pos hx.1) _)
  have hprod : 0 ≤ (endpointGraphRate U (endpointRationalBarrier (1/500000) U) -
      endpointRationalBarrierDerivative U)*((endpointRationalBarrier (1/500000) U+1)*
        endpointDenominator (1/U)^3) := by
    rw [← mul_assoc, hi]
    exact hr
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hpos).mp hprod)

end
end krylov.Certificates
