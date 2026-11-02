import jacobi.Reference.WeightDerivatives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Article: jacobi, Lemma C.1.
The monotone cosine coordinate transports the actual reference squared
prefactor to the literal Jacobi weight. The change of variables uses
the community theorem for a nonnegative derivative, so integrable
singular endpoint weights do not require artificial continuity assumptions.
Use: transports the full source reference system to the already proved genuine Jacobi orthogonality and polynomial basis.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- The actual shifted Jacobi coordinate of the reference cosine angle.
Use: transports the full source reference system to the already proved genuine Jacobi orthogonality and polynomial basis.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
-/
def coordinate (t : ℝ) : ℝ := (1-cos (Real.pi*t))/2

/-- The actual ordinary derivative of the reference-to-Jacobi coordinate.
Use: fixes the exact Jacobian in the reference norm and orthogonality integrals.
Article: jacobi, Lemma C.1.
-/
def coordinateSlope (t : ℝ) : ℝ := Real.pi*sin (Real.pi*t)/2

/-- The exact positive scalar relating the original Jacobi weight and the actual squared reference prefactor.
Use: fixes all normalization powers in the actual reference squared norm formula.
Article: jacobi, Appendix C.1 (selected endpoint branch).
-/
def coordinateScale (a : ℝ) : ℝ := Real.pi*(Real.pi/2)^(2*gamma a)

/-- The actual reference cosine coordinate is continuous and differentiates with the literal positive interior Jacobian.
Use: discharges the analytic coordinate premises of the reference norm substitution.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: differentiate the original cosine affine expression by the ordinary chain rule. -/
theorem coordinate_hasDerivAt (t : ℝ) : HasDerivAt coordinate (coordinateSlope t) t := by
  convert ((hasDerivAt_const t (1:ℝ)).sub ((Real.hasDerivAt_cos (Real.pi*t)).comp t
    ((hasDerivAt_id t).const_mul Real.pi))).div_const 2 using 1
  · rfl
  · dsimp [coordinateSlope]
    ring

/-- The actual reference cosine coordinate maps the closed unit interval into itself and has its two exact endpoint values.
Use: transports the literal Jacobi integrals over their entire source interval.
Article: jacobi, Lemma C.1.
Proof: the global cosine bounds give the interval inclusion; cos(0)=1 and cos(pi)=-1 give the endpoints. -/
theorem coordinate_properties : coordinate 0=0 ∧ coordinate 1=1 ∧ ∀ t,coordinate t∈Icc 0 1 := by
  refine ⟨by simp [coordinate],by simp [coordinate],?_⟩
  intro t
  dsimp [coordinate]
  constructor <;> linarith [Real.cos_le_one (Real.pi*t),Real.neg_one_le_cos (Real.pi*t)]

/-- The exact reference norm coordinate scalar is strictly positive for every original real order.
Use: division by the genuine coordinate normalization in the reference norms preserves positivity and equality.
Article: jacobi, Lemma C.1.
Proof: pi and the positive-base real power are both strictly positive. -/
theorem coordinateScale_pos (a : ℝ) : 0<coordinateScale a := by
  unfold coordinateScale
  exact mul_pos Real.pi_pos (Real.rpow_pos_of_pos (by positivity) _)

/-- The actual reference squared sine-power weight transports to the literal singular Jacobi weight with the exact source normalization.
Use: the complete reference norm and orthogonality theorems reuse the existing genuine Jacobi integrals.
Article: jacobi, Lemma C.1.
Proof: x*(1-x)=sin(pi*t)^2/4. Combine the two positive Jacobi real
powers, include the true Jacobian, and use 2*(gamma-1/2)+1=2*gamma.
The real-power multiplication law then supplies the exact pi normalization. -/
theorem coordinate_weight (a : ℝ) {t : ℝ} (ht : t∈Ioo 0 1) :
    jacobi.Jacobi.weight (jacobiIndex a) (jacobiIndex a) (coordinate t)*coordinateSlope t=
      coordinateScale a*(weight a t)^2 := by
  -- All bases in the real-power identities are genuinely positive physical coordinates.
  have hs := sine_pos ht
  have hy := (coordinate_properties.2.2 t).1
  have hy' := sub_nonneg.mpr (coordinate_properties.2.2 t).2
  have hquad : coordinate t*(1-coordinate t)=(sin (Real.pi*t)/2)^2 := by
    dsimp [coordinate]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi*t)]
  have hs2 : 0<sin (Real.pi*t)/2 := by positivity
  have hw : (weight a t)^2=(sin (Real.pi*t)/Real.pi)^(2*gamma a) := by
    unfold weight
    rw [show 2*gamma a=gamma a*2 by ring,Real.rpow_mul (div_nonneg hs.le Real.pi_pos.le),Real.rpow_two]
  rw [jacobi.Jacobi.weight,← Real.mul_rpow hy hy',hquad,← Real.rpow_two (sin (Real.pi*t)/2),
    ← Real.rpow_mul hs2.le]
  calc
    _ = Real.pi*(sin (Real.pi*t)/2)^(2*jacobiIndex a+1) := by
      rw [Real.rpow_add hs2,Real.rpow_one]
      dsimp [coordinateSlope]
      ring
    _ = Real.pi*(sin (Real.pi*t)/2)^(2*gamma a) := by congr 2; dsimp [jacobiIndex]; ring
    _ = Real.pi*((Real.pi/2)*(sin (Real.pi*t)/Real.pi))^(2*gamma a) := by
      congr 2
      field_simp
    _ = _ := by
      rw [Real.mul_rpow (by positivity : (0:ℝ)≤Real.pi/2) (div_nonneg hs.le Real.pi_pos.le),hw]
      dsimp [coordinateScale]
      ring

/-- The actual monotone reference cosine substitution gives an exact integral identity even for singular endpoint Jacobi weights.
Use: transfers genuine weighted Jacobi orthogonality and exact norms to the actual source reference functions.
Article: jacobi, Lemma C.1.
Source: mathlib, intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg.
Proof: the source coordinate has the true nonnegative derivative on the whole physical interior and exact endpoint values zero and one. -/
theorem coordinate_substitution (g : ℝ → ℝ) :
    (∫ t in (0:ℝ)..1,g (coordinate t)*coordinateSlope t)=∫ x in (0:ℝ)..1,g x := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := 0) (b := 1) (f := coordinate) (f' := coordinateSlope) (g := g)
    ((show Continuous coordinate from continuous_iff_continuousAt.mpr fun t => (coordinate_hasDerivAt t).continuousAt).continuousOn)
    (fun t _ => coordinate_hasDerivAt t)
    (fun t ht => by
      have ht : t∈Ioo (0:ℝ) 1 := by simpa only [min_eq_left (by norm_num : (0:ℝ)≤1),max_eq_right (by norm_num : (0:ℝ)≤1)] using ht
      exact (div_pos (mul_pos Real.pi_pos (sine_pos ht)) (by norm_num)).le)
  simpa only [coordinate_properties.1,coordinate_properties.2.1,Function.comp_apply] using h

end
end jacobi.Reference
