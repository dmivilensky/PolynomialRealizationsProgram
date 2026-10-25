import polyak.Levels.Chart.DoubleRootConverse

/-! Exact classification of the open diagonal face, in both source
coordinates and the actual relative boundary of lag-one convergence. -/
noncomputable section
namespace polyak.Levels.Chart
open General Set

theorem diagonal_face_iff {K : ℕ} (hK : 2≤K) (q : Tuning) :
    (∃a r : ℝ,boundaryCosine K<r ∧ r<boundaryCosine (K+1) ∧
      amplitudeFloor r r<a ∧ coefficients q=gapPolynomial a r r) ↔
    (q∈frontier {p : Tuning | Regions.OmegaOne p} ∧
      ¬Geometry.PhaseLockedContact q ∧
      ∃ω : Frequency,Geometry.InWindow K ω ∧ q.angle ω=(ω:ℝ)/2) := by
  constructor
  · rintro ⟨a,r,hl,hu,ha,he⟩
    have hr : r∈Ioo (-1:ℝ) 1 :=
      ⟨(boundaryCosine_ge_neg_one K).trans_lt hl,hu.trans (boundaryCosine_succ_lt_one hK)⟩
    have hap := (amplitudeFloor_pos hr.2 hr.2).trans ha
    have hh := double_root_between_boundaries_strict q hap hK hl hu he
    let ω : Frequency := ⟨Real.arccos r,Real.arccos_nonneg _,Real.arccos_le_pi _⟩
    refine ⟨hh.1,hh.2.1,ω,?_,(double_root_boundary q hap hr he).2.1⟩
    have hc : boundaryCosine K<Real.cos (ω:ℝ) ∧ Real.cos (ω:ℝ)<boundaryCosine (K+1) := by
      simpa only [ω,Real.cos_arccos hr.1.le hr.2.le] using And.intro hl hu
    simpa only [Geometry.InWindow,boundaryAngle,Nat.cast_add,Nat.cast_one] using
      (cos_window_iff hK ω.property).mp hc
  · rintro ⟨hf,_,ω,hw,hθ⟩
    obtain ⟨_,a,r,ha,hr,hfloor,he⟩ := frontier_double_root q hf
    have hω : (ω:ℝ)∈Ioo (0:ℝ) Real.pi := by
      have hw' : boundaryAngle (K+1)<(ω:ℝ) ∧ (ω:ℝ)<boundaryAngle K := by
        simpa only [Geometry.InWindow,boundaryAngle,Nat.cast_add,Nat.cast_one] using hw
      exact ⟨(boundaryAngle_succ_mem hK).1.trans hw'.1,
        hw'.2.trans_le (boundaryAngle_mem hK).2⟩
    have hc := (angle_eq_half_iff_Xi q hω).mp hθ
    rw [←eval_coefficients,he,gapPolynomial_eval] at hc
    have hz : a*(Real.cos (ω:ℝ)-r)^2=0 := by nlinarith [hc]
    have heq : Real.cos (ω:ℝ)=r := by
      have hs : (Real.cos (ω:ℝ)-r)^2=0 := (mul_eq_zero.mp hz).resolve_left ha.ne'
      nlinarith [sq_nonneg (Real.cos (ω:ℝ)-r)]
    have hwin : boundaryAngle (K+1)<(ω:ℝ) ∧ (ω:ℝ)<boundaryAngle K := by
      simpa only [Geometry.InWindow,boundaryAngle,Nat.cast_add,Nat.cast_one] using hw
    have hb := (cos_window_iff hK ω.property).mpr hwin
    rw [heq] at hb
    exact ⟨a,r,hb.1,hb.2,hfloor,he⟩

end polyak.Levels.Chart
