import polyak.FareyPlateau.Domain.Source

/-! Every actual tuning on the Farey edge has the displayed `(a,D)`
coordinates. They are recovered from the coefficients and are unique. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels Set

theorem recover_edgeCoefficients (C : Chart.Coefficients) (c h : ℝ)
    (he : C.eval c=h) :
    C=edgeCoefficients c h (-C.c2) (C.c1-1+2*C.c2*c) := by
  apply Chart.Coefficients.ext
  · dsimp [edgeCoefficients]
    dsimp [Chart.Coefficients.eval] at he
    nlinarith
  · dsimp [edgeCoefficients]; ring
  · dsimp [edgeCoefficients]; ring

theorem edgeCoefficients_injective (c h : ℝ) {a D a' D' : ℝ}
    (he : edgeCoefficients c h a D=edgeCoefficients c h a' D') : a=a' ∧ D=D' := by
  have h2 := congrArg Chart.Coefficients.c2 he
  have h1 := congrArg Chart.Coefficients.c1 he
  dsimp [edgeCoefficients] at h1 h2
  have haa : a=a' := by linarith
  refine ⟨haa,?_⟩
  rw [haa] at h1
  linarith

theorem source_edge_recovery (q : Tuning) {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k)
    (hphase : q.angle (Regions.rationalAngle j k)=Real.pi/k) :
    ∃a D : ℝ,0<a ∧ Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D ∧
      (Geometry.Gap K q ↔ aE K j k D<a) := by
  obtain ⟨hj,hjk⟩ := Chart.fraction_window_arithmetic hK hf
  have hω := Regions.rationalAngle_mem (show 1≤j by omega) hjk
  have hs := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hvalue : (Chart.coefficients q).eval (Chart.rationalCosine j k)=
      Chart.rationalHeight j k := by
    rw [Chart.eval_coefficients]
    have hc := q.cot_angle hω
    rw [hphase] at hc
    unfold Chart.rationalCosine Chart.rationalHeight
    exact ((div_eq_iff hs.ne').mp hc.symm)
  have hpoly := recover_edgeCoefficients (Chart.coefficients q)
    (Chart.rationalCosine j k) (Chart.rationalHeight j k) hvalue
  have hhalf : Real.pi/(k:ℝ)<Regions.rationalAngle j k/2 := by
    have hk : (0:ℝ)<k := by exact_mod_cast hf.1
    have hjr : (1:ℝ)<j := by exact_mod_cast (show 1<j by omega)
    unfold Regions.rationalAngle
    apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_lt_div_iff_of_pos_right hk).mpr
    nlinarith [Real.pi_pos]
  let ω : Frequency := ⟨Regions.rationalAngle j k,hω.1.le,hω.2.le⟩
  have hdip : ω∈Geometry.dip (tuningCurve q) := by
    change q.angle (Regions.rationalAngle j k)<Regions.rationalAngle j k/2
    rw [hphase]
    exact hhalf
  have hβ := (Chart.roots_of_nonempty_dip q ⟨ω,hdip⟩).1
  have hneg := (Chart.coefficient_quadratic_neg_iff q).mpr hβ
  refine ⟨-(Chart.coefficients q).c2,
    (Chart.coefficients q).c1-1+2*(Chart.coefficients q).c2*Chart.rationalCosine j k,
    neg_pos.mpr hneg,hpoly,?_⟩
  exact source_edgedomain q hK hf hpoly

end polyak.FareyPlateau
