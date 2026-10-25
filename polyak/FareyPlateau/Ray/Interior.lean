import polyak.FareyPlateau.Ray.ThresholdDefinition
import polyak.FareyPlateau.LargeCurvature.IndexedCertificate
import polyak.ModeLocking.TwoLag.SecondJet

/-! The original finite symbol, rather than a replacement polynomial,
has exactly the phase-floor sign on the open frequency interval. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels ModeLocking Set
open scoped BigOperators
variable {I : Type*} [Fintype I]

theorem indexedSymbol_expansion (q : Tuning) (n : I→ℤ) (w : I→ℝ)
    {x : ℝ} (hx : x∈Icc (0:ℝ) Real.pi) :
    LargeCurvature.indexedSymbol q 0 n w x=
      Real.cos (q.angle x)*Symbols.denominator n w x-Real.sin (q.angle x)*sineMoment n w x := by
  unfold LargeCurvature.indexedSymbol Symbols.denominator sineMoment
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [lagExtension_actual q 0 (n i) ⟨x,hx⟩,Geometry.shiftedCurve_zero,Curve.lag_expand]
  change w i*(Real.cos (q.angle x)*(1-Real.cos ((n i:ℝ)*x))-
    Real.sin (q.angle x)*Real.sin ((n i:ℝ)*x))=_
  ring

theorem indexedSymbol_phaseFloor (q : Tuning) (n : I→ℤ) (w : I→ℝ)
    (hn : ∀i,n i≠0) (hw : ∀i,0≤w i) (hsum : ∑i,w i=1)
    (hbez : Symbols.SupportBezout n w) {x : ℝ} (hx : x∈Ioo (0:ℝ) Real.pi) :
    LargeCurvature.indexedSymbol q 0 n w x=
      (Real.sin (q.angle x)*Symbols.denominator n w x/Real.sin x)*
        (q.Xi (Real.cos x)-Symbols.psi n w (Real.cos x)) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hθ := Real.sin_pos_of_pos_of_lt_pi (q.angle_mem hx).1 (q.angle_mem hx).2
  have hP := Symbols.denominator_pos n w hw hbez ⟨hx.1,hx.2.le⟩
  rw [indexedSymbol_expansion q n w ⟨hx.1.le,hx.2.le⟩,
    Symbols.psi_cos n w hn hw hsum hbez hx]
  unfold sineMoment
  have hc := (div_eq_div_iff hθ.ne' hs.ne').mp (q.cot_angle hx)
  field_simp [hs.ne',hP.ne']
  simp only [mul_comm x] at *
  linear_combination Symbols.denominator n w x*hc

theorem indexedSymbol_negative_iff (q : Tuning) (n : I→ℤ) (w : I→ℝ)
    (hn : ∀i,n i≠0) (hw : ∀i,0≤w i) (hsum : ∑i,w i=1)
    (hbez : Symbols.SupportBezout n w) {x : ℝ} (hx : x∈Ioo (0:ℝ) Real.pi) :
    LargeCurvature.indexedSymbol q 0 n w x<0 ↔
      q.Xi (Real.cos x)<Symbols.psi n w (Real.cos x) := by
  rw [indexedSymbol_phaseFloor q n w hn hw hsum hbez hx]
  have hp : 0<Real.sin (q.angle x)*Symbols.denominator n w x/Real.sin x := by
    exact div_pos (mul_pos
      (Real.sin_pos_of_pos_of_lt_pi (q.angle_mem hx).1 (q.angle_mem hx).2)
      (Symbols.denominator_pos n w hw hbez ⟨hx.1,hx.2.le⟩))
      (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2)
  rw [lt_iff_not_ge,mul_nonneg_iff_of_pos_left hp,not_le,sub_neg]

theorem SourceCertificate.parabola_difference {j k : ℕ} {b : ℤ} {D a : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1)
    (c : ℝ) :
    (edgeCoefficients (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D).eval c-
      Symbols.psi C.lag C.weight c=(c-Chart.rationalCosine j k)^2*(C.R c-a) := by
  obtain ⟨hv,hd⟩ := phaseFloor_edge_contact hj hjk hb C.admissible
  have hjets := Symbols.contactDifference_jets C.lag C.weight
    (C.admissible.phaseFloor_analytic _ ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩) hv hd
  have hf := Symbols.quadraticQuotient_factor hjets.1 hjets.2 c
  change (c-Chart.rationalCosine j k)^2*C.R c=
    Chart.rationalHeight j k+(1+D)*(c-Chart.rationalCosine j k)-Symbols.psi C.lag C.weight c at hf
  rw [edgeCoefficients_eval]
  linear_combination -hf

theorem SourceCertificate.interior_ray_iff {j k : ℕ} {b : ℤ} {D a x : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1)
    (q : Tuning) (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D)
    (hx : x∈Ioo (0:ℝ) Real.pi) (hc : Real.cos x≠Chart.rationalCosine j k) :
    LargeCurvature.indexedSymbol q 0 C.lag C.weight x<0 ↔ C.R (Real.cos x)<a := by
  rw [indexedSymbol_negative_iff q C.lag C.weight C.admissible.nonzero
    (fun i=>(C.admissible.positive i).le) C.admissible.normalization C.admissible.bezout hx]
  rw [←sub_neg,←Chart.eval_coefficients,he,C.parabola_difference hj hjk hb]
  rw [lt_iff_not_ge,mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero (sub_ne_zero.mpr hc)),
    not_le,sub_neg]

end polyak.FareyPlateau.Ray
