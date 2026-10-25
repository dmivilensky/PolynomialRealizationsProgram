import polyak.Levels.Chart.Window
import polyak.Levels.Chart.RealRoots
import polyak.General.Regions.GradientDescent

/-! The source geometric definition of I_K is equivalent to the genuine
ordered-root polynomial coordinates. -/
noncomputable section
namespace polyak.Levels.Chart
open General Set

theorem roots_of_nonempty_dip (q : Tuning) (h : (Geometry.dip (tuningCurve q)).Nonempty) :
    0<q.beta ∧ ∃ r₁ r₂ : ℝ,-1<r₁ ∧ r₁<r₂ ∧ r₂<1 ∧
      coefficients q=gapPolynomial (-(coefficients q).c2) r₁ r₂ ∧
      amplitudeFloor r₁ r₂< -(coefficients q).c2 := by
  obtain ⟨ω,hω⟩ := h
  change q.angle (ω:ℝ)<(ω:ℝ)/2 at hω
  have hclosed : ω∈Geometry.closedDip (tuningCurve q) := by
    change q.angle (ω:ℝ)≤(ω:ℝ)/2
    exact hω.le
  have hi := Geometry.closedDip_interior_frequency (tuningCurve q) hclosed
  have hneg := (angle_lt_half_iff_Xi q hi).mp hω
  have hβ : 0<q.beta := by
    by_contra hh
    have hz : q.beta=0 := le_antisymm (le_of_not_gt hh) q.beta_nonneg
    have ho := General.Regions.gradientDescent_mem_omegaOne q hz
    have hp := (q.angle_gt_half_iff ⟨hi.1,hi.2.le⟩).mpr
      (ho (Real.cos (ω:ℝ)) ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)
    linarith
  refine ⟨hβ,?_⟩
  apply exists_gap_roots (coefficients q) (coefficients_mem q hβ)
  · constructor
    · have hh := Real.cos_lt_cos_of_nonneg_of_le_pi hi.1.le le_rfl hi.2
      simpa only [Real.cos_pi] using hh
    · have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0:ℝ)≤0 by rfl) hi.2.le hi.1
      simpa only [Real.cos_zero] using hh
  · rwa [eval_coefficients]

theorem gap_of_root_coordinates (q : Tuning) {K : ℕ} (hK : 2≤K)
    {a r₁ r₂ : ℝ} (h₁ : boundaryCosine K<r₁) (hr : r₁<r₂)
    (h₂ : r₂<boundaryCosine (K+1)) (ha : amplitudeFloor r₁ r₂<a)
    (he : coefficients q=gapPolynomial a r₁ r₂) : Geometry.Gap K q := by
  have hl : -1<r₁ := (boundaryCosine_ge_neg_one K).trans_lt h₁
  have hu : r₂<1 := h₂.trans (boundaryCosine_succ_lt_one hK)
  have hap : 0<a := (amplitudeFloor_pos (hr.trans hu) hu).trans ha
  have hm : (r₁+r₂)/2∈Ioo (-1:ℝ) 1 := ⟨by linarith,by linarith⟩
  let ω₀ : Frequency := ⟨Real.arccos ((r₁+r₂)/2),Real.arccos_nonneg _,Real.arccos_le_pi _⟩
  have hc : Real.cos (ω₀:ℝ)=(r₁+r₂)/2 := Real.cos_arccos hm.1.le hm.2.le
  have hdip : ω₀∈Geometry.dip (tuningCurve q) := by
    rw [dip_gapPolynomial_iff q hap hl hr hu he,hc]
    constructor <;> linarith
  refine ⟨hK,⟨ω₀,hdip⟩,?_,?_,?_⟩
  · intro ω hω
    have hc' := (dip_gapPolynomial_iff q hap hl hr hu he ω).mp hω
    have hh := (cos_window_iff hK ω.property).mp ⟨h₁.trans hc'.1,hc'.2.trans h₂⟩
    simpa only [boundaryAngle,Nat.cast_add,Nat.cast_one] using hh
  · have hx : q.Xi (Real.cos (boundaryAngle K))<1+Real.cos (boundaryAngle K) := by
      rw [← eval_coefficients,he,gapPolynomial_eval]
      change 1+boundaryCosine K-a*(boundaryCosine K-r₁)*(boundaryCosine K-r₂)<1+boundaryCosine K
      have hp := mul_pos_of_neg_of_neg (show boundaryCosine K-r₁<0 by linarith)
        (show boundaryCosine K-r₂<0 by linarith)
      nlinarith [mul_pos hap hp]
    have hh := (angle_gt_half_iff_Xi q (boundaryAngle_mem hK)).mpr hx
    have hf : boundaryAngle K/2=Real.pi/K := by unfold boundaryAngle; ring
    rw [hf] at hh
    exact hh
  · have hx : q.Xi (Real.cos (boundaryAngle (K+1)))<1+Real.cos (boundaryAngle (K+1)) := by
      rw [← eval_coefficients,he,gapPolynomial_eval]
      change 1+boundaryCosine (K+1)-a*(boundaryCosine (K+1)-r₁)*(boundaryCosine (K+1)-r₂)<1+boundaryCosine (K+1)
      have hp := mul_pos (show 0<boundaryCosine (K+1)-r₁ by linarith)
        (show 0<boundaryCosine (K+1)-r₂ by linarith)
      nlinarith [mul_pos hap hp]
    have hh := (angle_gt_half_iff_Xi q
      ⟨(boundaryAngle_succ_mem hK).1,(boundaryAngle_succ_mem hK).2.le⟩).mpr hx
    have hf : boundaryAngle (K+1)/2=Real.pi/(K+1) := by unfold boundaryAngle; push_cast; ring
    rw [hf] at hh
    simpa only [boundaryAngle,Nat.cast_add,Nat.cast_one] using hh

theorem root_coordinates_of_gap (q : Tuning) {K : ℕ} (hgap : Geometry.Gap K q) :
    ∃ a r₁ r₂ : ℝ,boundaryCosine K<r₁ ∧ r₁<r₂ ∧ r₂<boundaryCosine (K+1) ∧
      amplitudeFloor r₁ r₂<a ∧ coefficients q=gapPolynomial a r₁ r₂ := by
  rcases hgap with ⟨hK,hdip,hwindow,hlo,hhi⟩
  obtain ⟨hβ,r₁,r₂,hl,hr,hu,he,ha⟩ := roots_of_nonempty_dip q hdip
  let a := -(coefficients q).c2
  have hap : 0<a := neg_pos.mpr ((coefficient_quadratic_neg_iff q).mpr hβ)
  have hbetween {c : ℝ} (hc : r₁<c ∧ c<r₂) :
      boundaryCosine K<c ∧ c<boundaryCosine (K+1) := by
    have hc' : c∈Ioo (-1:ℝ) 1 := ⟨hl.trans hc.1,hc.2.trans hu⟩
    let ω : Frequency := ⟨Real.arccos c,Real.arccos_nonneg c,Real.arccos_le_pi c⟩
    have hcos : Real.cos (ω:ℝ)=c := Real.cos_arccos hc'.1.le hc'.2.le
    have hω : ω∈Geometry.dip (tuningCurve q) := by
      rw [dip_gapPolynomial_iff q hap hl hr hu he,hcos]
      exact hc
    have hw := hwindow ω hω
    have hw' : boundaryAngle (K+1)<(ω:ℝ) ∧ (ω:ℝ)<boundaryAngle K := by
      simpa only [boundaryAngle,Nat.cast_add,Nat.cast_one] using hw
    simpa only [hcos] using (cos_window_iff hK ω.property).mpr hw'
  have hleft : boundaryCosine K≤r₁ := by
    by_contra hh
    have hh : r₁<boundaryCosine K := lt_of_not_ge hh
    let c := (r₁+min r₂ (boundaryCosine K))/2
    have hmin : r₁<min r₂ (boundaryCosine K) := lt_min hr hh
    have hc₁ : r₁<c := by dsimp [c]; linarith
    have hc₂ : c<r₂ := by have := min_le_left r₂ (boundaryCosine K); dsimp [c]; linarith
    have hc₃ : c<boundaryCosine K := by have := min_le_right r₂ (boundaryCosine K); dsimp [c]; linarith
    exact (not_lt_of_ge (hbetween ⟨hc₁,hc₂⟩).1.le) hc₃
  have hright : r₂≤boundaryCosine (K+1) := by
    by_contra hh
    have hh : boundaryCosine (K+1)<r₂ := lt_of_not_ge hh
    let c := (max r₁ (boundaryCosine (K+1))+r₂)/2
    have hmax : max r₁ (boundaryCosine (K+1))<r₂ := max_lt hr hh
    have hc₁ : r₁<c := by have := le_max_left r₁ (boundaryCosine (K+1)); dsimp [c]; linarith
    have hc₂ : c<r₂ := by dsimp [c]; linarith
    have hc₃ : boundaryCosine (K+1)<c := by have := le_max_right r₁ (boundaryCosine (K+1)); dsimp [c]; linarith
    exact (not_lt_of_ge (hbetween ⟨hc₁,hc₂⟩).2.le) hc₃
  have hxlo : q.Xi (boundaryCosine K)<1+boundaryCosine K := by
    apply (angle_gt_half_iff_Xi q (boundaryAngle_mem hK)).mp
    convert hlo using 1 <;> unfold boundaryAngle <;> ring
  have hxhi : q.Xi (boundaryCosine (K+1))<1+boundaryCosine (K+1) := by
    apply (angle_gt_half_iff_Xi q ⟨(boundaryAngle_succ_mem hK).1,(boundaryAngle_succ_mem hK).2.le⟩).mp
    convert hhi using 1 <;> unfold boundaryAngle <;> push_cast <;> ring
  have hleft' : boundaryCosine K<r₁ := by
    apply lt_of_le_of_ne hleft
    intro hh
    rw [← eval_coefficients,he,gapPolynomial_eval,hh] at hxlo
    simp only [sub_self,mul_zero,zero_mul,sub_zero] at hxlo
    exact lt_irrefl _ hxlo
  have hright' : r₂<boundaryCosine (K+1) := by
    apply lt_of_le_of_ne hright
    intro hh
    rw [← eval_coefficients,he,gapPolynomial_eval,← hh] at hxhi
    simp only [sub_self,mul_zero,sub_zero] at hxhi
    exact lt_irrefl _ hxhi
  exact ⟨a,r₁,r₂,hleft',hr,hright',ha,he⟩

theorem gap_iff_root_coordinates (q : Tuning) {K : ℕ} : Geometry.Gap K q ↔
    2≤K ∧ ∃ a r₁ r₂ : ℝ,boundaryCosine K<r₁ ∧ r₁<r₂ ∧ r₂<boundaryCosine (K+1) ∧
      amplitudeFloor r₁ r₂<a ∧ coefficients q=gapPolynomial a r₁ r₂ := by
  constructor
  · intro h
    exact ⟨h.1,root_coordinates_of_gap q h⟩
  · rintro ⟨hK,a,r₁,r₂,h₁,hr,h₂,ha,he⟩
    exact gap_of_root_coordinates q hK h₁ hr h₂ ha he

end polyak.Levels.Chart
