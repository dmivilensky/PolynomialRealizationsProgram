import polyak.FareyPlateau.Ray.Interior
import polyak.Levels.Geometry.LagEnds

/-! The endpoint inequalities in the source ray criterion. At π strict
negativity is automatic; at zero the second-jet test is exactly R(1)<a. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels Set
open scoped BigOperators

theorem SourceCertificate.strict_pi {j k : ℕ} {b : ℤ} {D : ℝ}
    (C : SourceCertificate j k b D) (q : Tuning) :
    LargeCurvature.indexedSymbol q 0 C.lag C.weight Real.pi<0 := by
  rw [indexedSymbol_expansion q C.lag C.weight ⟨Real.pi_pos.le,le_rfl⟩,
    q.angle_pi,Real.cos_pi,Real.sin_pi,zero_mul,sub_zero,neg_one_mul]
  exact neg_neg_of_pos (C.admissible.denominator_pos ⟨Real.pi_pos,le_rfl⟩)

theorem SourceCertificate.R_neg_one_lt {j k : ℕ} {b : ℤ} {D a : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1)
    (q : Tuning) (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) : C.R (-1)<a := by
  have hω := Regions.rationalAngle_mem hj hjk
  have hc : -1<Chart.rationalCosine j k := by
    have hx := Real.cos_lt_cos_of_nonneg_of_le_pi hω.1.le le_rfl hω.2
    simpa only [Chart.rationalCosine,Real.cos_pi] using hx
  have hd := C.parabola_difference (a:=a) hj hjk hb (-1)
  rw [←he,Chart.eval_coefficients,Symbols.psi_neg_one,sub_zero] at hd
  have hh : ((-1)-Chart.rationalCosine j k)^2*(C.R (-1)-a)<0 := by
    rw [←hd]; exact q.Xi_neg_one_neg
  have hp := sq_pos_of_ne_zero (sub_ne_zero.mpr hc.ne)
  have hneg := neg_of_mul_neg_right hh hp.le
  linarith

theorem SourceCertificate.endpoint_iff {j k : ℕ} {b : ℤ} {D a : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1)
    (q : Tuning) (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    (0<∑i,C.weight i*(C.lag i:ℝ)*((C.lag i:ℝ)+2*Geometry.tau q)) ↔ C.R 1<a := by
  have hω := Regions.rationalAngle_mem hj hjk
  have hc : Chart.rationalCosine j k<1 := by
    have hx := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0:ℝ)≤0 by rfl) hω.2.le hω.1
    simpa only [Chart.rationalCosine,Real.cos_zero] using hx
  have hS := Symbols.normalizedDenominator_pos C.lag C.weight C.admissible.nonzero
    (fun i=>(C.admissible.positive i).le) C.admissible.normalization C.admissible.bezout
    (show (1:ℝ)∈Icc (-1:ℝ) 1 by norm_num)
  rw [Symbols.normalizedDenominator_one] at hS
  have hmoment : (∑i,C.weight i*(C.lag i:ℝ)*((C.lag i:ℝ)+2*Geometry.tau q))=
      ((∑i,C.weight i*(C.lag i:ℝ)^2)/(-q.Xi 1))*
        (Symbols.psi C.lag C.weight 1-q.Xi 1) := by
    have hexpand : (∑i,C.weight i*(C.lag i:ℝ)*((C.lag i:ℝ)+2*Geometry.tau q))=
        (∑i,C.weight i*(C.lag i:ℝ)^2)+2*Geometry.tau q*(∑i,C.weight i*(C.lag i:ℝ)) := by
      rw [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hexpand,Symbols.psi_one]
    unfold Geometry.tau
    field_simp [q.Xi_one_neg.ne,hS.ne']
    ring
  have hsign : (0<∑i,C.weight i*(C.lag i:ℝ)*((C.lag i:ℝ)+2*Geometry.tau q)) ↔
      q.Xi 1<Symbols.psi C.lag C.weight 1 := by
    rw [hmoment]
    have hp := div_pos hS (neg_pos.mpr q.Xi_one_neg)
    constructor
    · intro h
      have ht := pos_of_mul_pos_right h hp.le
      linarith
    · intro h
      exact mul_pos hp (sub_pos.mpr h)
  rw [hsign]
  have hd := C.parabola_difference (a:=a) hj hjk hb 1
  rw [←he,Chart.eval_coefficients] at hd
  rw [←sub_neg,hd]
  rw [lt_iff_not_ge,mul_nonneg_iff_of_pos_left
    (sq_pos_of_ne_zero (sub_ne_zero.mpr hc.ne')),not_le,sub_neg]

end polyak.FareyPlateau.Ray
