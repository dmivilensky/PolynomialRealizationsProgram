import polyak.Levels.Chart.GapHomeomorphism
import polyak.Levels.Chart.RootReconstruction

/-! Strict root inequalities give an open set of the original tunings. -/
noncomputable section
namespace polyak.Levels.Chart
open General Set Filter

 theorem gap_iff_discriminant {K : ℕ} (hK : 2≤K) (q : Tuning) :
    Geometry.Gap K q ↔ (coefficients q).c2<0 ∧
      0<gapDiscriminant (coefficients q) ∧
      boundaryCosine K<leftRoot (coefficients q) ∧
      rightRoot (coefficients q)<boundaryCosine (K+1) := by
  constructor
  · intro hq
    obtain ⟨a,r₁,r₂,h₁,hr,h₂,ha,he⟩ := root_coordinates_of_gap q hq
    have hu := h₂.trans (boundaryCosine_succ_lt_one hK)
    have hap := (amplitudeFloor_pos (hr.trans hu) hu).trans ha
    rw [he,leftRoot_gapPolynomial hap hr.le,rightRoot_gapPolynomial hap hr.le,
      gapDiscriminant_gapPolynomial]
    exact ⟨neg_neg_of_pos hap,sq_pos_of_pos (mul_pos hap (sub_pos.mpr hr)),h₁,h₂⟩
  · rintro ⟨hc,hΔ,hl,hr⟩
    have ho := leftRoot_lt_rightRoot (coefficients q) hc hΔ
    have hu := hr.trans (boundaryCosine_succ_lt_one hK)
    have he := reconstruct_gapPolynomial (coefficients q) (ne_of_lt hc) hΔ.le
    have hneg := (coefficients_mem q ((coefficient_quadratic_neg_iff q).mp hc)).2.1
    rw [he,gapPolynomial_one] at hneg
    have hfloor : amplitudeFloor (leftRoot (coefficients q))
        (rightRoot (coefficients q))< -(coefficients q).c2 := by
      unfold amplitudeFloor
      apply (div_lt_iff₀ (mul_pos (sub_pos.mpr (ho.trans hu)) (sub_pos.mpr hu))).mpr
      nlinarith
    exact gap_of_root_coordinates q hK hl ho hr hfloor he

@[fun_prop] theorem continuous_gapDiscriminant : Continuous gapDiscriminant := by
  unfold gapDiscriminant
  fun_prop

 theorem isOpen_gap (K : ℕ) : IsOpen {q : Tuning | Geometry.Gap K q} := by
  by_cases hK : 2≤K
  · apply isOpen_iff_mem_nhds.mpr
    intro q hq
    obtain ⟨hc,hΔ,hl,hr⟩ := (gap_iff_discriminant hK q).mp hq
    have hccont : ContinuousAt (fun q : Tuning => (coefficients q).c2) q :=
      (Coefficients.continuous_c2.comp continuous_coefficients).continuousAt
    have hdc : ContinuousAt (fun q : Tuning => gapDiscriminant (coefficients q)) q := (continuous_gapDiscriminant.comp continuous_coefficients).continuousAt
    have hroot : {C : Coefficients | C.c2≠0}∈nhds (coefficients q) := by
      exact (isOpen_ne_fun Coefficients.continuous_c2 continuous_const).mem_nhds
        (ne_of_lt hc)
    have hlc := (continuousOn_leftRoot.continuousAt hroot).comp
      continuous_coefficients.continuousAt
    have hrc := (continuousOn_rightRoot.continuousAt hroot).comp
      continuous_coefficients.continuousAt
    filter_upwards [hccont.eventually_lt_const hc,hdc.eventually_const_lt hΔ,
      hlc.eventually_const_lt hl,hrc.eventually_lt_const hr] with p hp₁ hp₂ hp₃ hp₄
    exact (gap_iff_discriminant hK p).mpr ⟨hp₁,hp₂,hp₃,hp₄⟩
  · have he : {q : Tuning | Geometry.Gap K q}=∅ := by
      ext q
      simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
      exact fun hq=>hK hq.1
    rw [he]
    exact isOpen_empty

end polyak.Levels.Chart
