import polyak.FareyPlateau.Domain.Coordinates

/-! The four half planes are exactly the original geometric gap, rather
than a replacement definition of that gap. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels Set

theorem edgeCoefficients_mem_domain {c₀ h₀ a D l r : ℝ}
    (hc : c₀∈Ioo (-1:ℝ) 1) (hh : 1+c₀<h₀) (hl : l<c₀) (hr : c₀<r)
    (ha : edgeBound c₀ h₀ l r D<a) : edgeCoefficients c₀ h₀ a D∈Chart.CoeffDomain := by
  have hapos := (edgeBound_pos hh hl hr).trans ha
  have hs := (edgeBound_iff hc hl hr).mp ha
  exact ⟨by change -a<0; linarith, hs.1,hs.2.1⟩

theorem edge_center_dip (q : Tuning) {c₀ h₀ a D : ℝ}
    (hc : c₀∈Ioo (-1:ℝ) 1) (hh : 1+c₀<h₀)
    (he : Chart.coefficients q=edgeCoefficients c₀ h₀ a D) :
    ∃ ω : Frequency, ω∈Geometry.dip (tuningCurve q) ∧ Real.cos (ω:ℝ)=c₀ := by
  let ω : Frequency := ⟨Real.arccos c₀,Real.arccos_nonneg _,Real.arccos_le_pi _⟩
  have hcos : Real.cos (ω:ℝ)=c₀ := Real.cos_arccos hc.1.le hc.2.le
  refine ⟨ω,?_,hcos⟩
  have hi : (ω:ℝ)∈Ioo (0:ℝ) Real.pi :=
    ⟨Real.arccos_pos.mpr hc.2,Real.arccos_lt_pi.mpr hc.1⟩
  change q.angle (ω:ℝ)<(ω:ℝ)/2
  rw [Chart.angle_lt_half_iff_Xi q hi, ←Chart.eval_coefficients,he,hcos,edgeCoefficients_center]
  exact hh

theorem edge_gap_iff (q : Tuning) {K : ℕ} (hK : 2≤K) {c₀ h₀ a D : ℝ}
    (hc : c₀∈Ioo (-1:ℝ) 1) (hh : 1+c₀<h₀)
    (hl : Chart.boundaryCosine K<c₀) (hr : c₀<Chart.boundaryCosine (K+1))
    (he : Chart.coefficients q=edgeCoefficients c₀ h₀ a D) :
    Geometry.Gap K q ↔ edgeBound c₀ h₀ (Chart.boundaryCosine K)
      (Chart.boundaryCosine (K+1)) D<a := by
  constructor
  · intro hgap
    apply (edgeBound_iff hc hl hr).mpr
    refine ⟨?_,?_,?_,?_⟩
    · rw [←he,Chart.eval_coefficients]; exact q.Xi_one_neg
    · rw [←he,Chart.eval_coefficients]; exact q.Xi_neg_one_neg
    · rw [←he,Chart.eval_coefficients]
      apply (Chart.angle_gt_half_iff_Xi q (Chart.boundaryAngle_mem hK)).mp
      convert hgap.2.2.2.1 using 1 <;> unfold Chart.boundaryAngle <;> ring
    · rw [←he,Chart.eval_coefficients]
      apply (Chart.angle_gt_half_iff_Xi q
        ⟨(Chart.boundaryAngle_succ_mem hK).1,(Chart.boundaryAngle_succ_mem hK).2.le⟩).mp
      convert hgap.2.2.2.2 using 1 <;> unfold Chart.boundaryAngle <;> push_cast <;> ring
  · intro hbound
    have hapos := (edgeBound_pos hh hl hr).trans hbound
    have hs := (edgeBound_iff hc hl hr).mp hbound
    obtain ⟨ω,hω,hcos⟩ := edge_center_dip q hc hh he
    obtain ⟨_,r₁,r₂,h₁,hr₁₂,h₂,hpoly,hfloor⟩ := Chart.roots_of_nonempty_dip q ⟨ω,hω⟩
    have hamp : -(Chart.coefficients q).c2=a := by rw [he]; simp [edgeCoefficients]
    rw [hamp] at hpoly hfloor
    have hmid := (Chart.dip_gapPolynomial_iff q hapos h₁ hr₁₂ h₂ hpoly ω).mp hω
    rw [hcos] at hmid
    have hlo : Chart.boundaryCosine K<r₁ := by
      have hx := hs.2.2.1
      rw [←he,hpoly,Chart.gapPolynomial_eval] at hx
      have hp : 0<(Chart.boundaryCosine K-r₁)*(Chart.boundaryCosine K-r₂) := by
        exact pos_of_mul_pos_right (by nlinarith :
          0<a*((Chart.boundaryCosine K-r₁)*(Chart.boundaryCosine K-r₂))) hapos.le
      have hn : Chart.boundaryCosine K-r₂<0 := by linarith [hmid.2]
      have := neg_of_mul_pos_left hp hn.le
      linarith
    have hhi : r₂<Chart.boundaryCosine (K+1) := by
      have hx := hs.2.2.2
      rw [←he,hpoly,Chart.gapPolynomial_eval] at hx
      have hp : 0<(Chart.boundaryCosine (K+1)-r₁)*(Chart.boundaryCosine (K+1)-r₂) := by
        exact pos_of_mul_pos_right (by nlinarith :
          0<a*((Chart.boundaryCosine (K+1)-r₁)*(Chart.boundaryCosine (K+1)-r₂))) hapos.le
      have hn : 0<Chart.boundaryCosine (K+1)-r₁ := by linarith [hmid.1]
      have := pos_of_mul_pos_right hp hn.le
      linarith
    exact Chart.gap_of_root_coordinates q hK hlo hr₁₂ hhi hfloor hpoly

def edgeTuning {c₀ h₀ a D l r : ℝ}
    (hc : c₀∈Ioo (-1:ℝ) 1) (hh : 1+c₀<h₀) (hl : l<c₀) (hr : c₀<r)
    (ha : edgeBound c₀ h₀ l r D<a) : Tuning :=
  Chart.inverseTuning ⟨edgeCoefficients c₀ h₀ a D,
    edgeCoefficients_mem_domain hc hh hl hr ha⟩

theorem coefficients_edgeTuning {c₀ h₀ a D l r : ℝ}
    (hc : c₀∈Ioo (-1:ℝ) 1) (hh : 1+c₀<h₀) (hl : l<c₀) (hr : c₀<r)
    (ha : edgeBound c₀ h₀ l r D<a) :
    Chart.coefficients (edgeTuning hc hh hl hr ha)=edgeCoefficients c₀ h₀ a D :=
  Chart.coefficients_inverseTuning _

theorem edgeTuning_gap {K : ℕ} (hK : 2≤K) {c₀ h₀ a D : ℝ}
    (hc : c₀∈Ioo (-1:ℝ) 1) (hh : 1+c₀<h₀)
    (hl : Chart.boundaryCosine K<c₀) (hr : c₀<Chart.boundaryCosine (K+1))
    (ha : edgeBound c₀ h₀ (Chart.boundaryCosine K)
      (Chart.boundaryCosine (K+1)) D<a) :
    Geometry.Gap K (edgeTuning hc hh hl hr ha) :=
  (edge_gap_iff _ hK hc hh hl hr (coefficients_edgeTuning hc hh hl hr ha)).mpr ha

theorem edgeTuning_unique (q : Tuning) {c₀ h₀ a D l r : ℝ}
    (hc : c₀∈Ioo (-1:ℝ) 1) (hh : 1+c₀<h₀) (hl : l<c₀) (hr : c₀<r)
    (ha : edgeBound c₀ h₀ l r D<a)
    (he : Chart.coefficients q=edgeCoefficients c₀ h₀ a D) :
    q=edgeTuning hc hh hl hr ha := by
  have hapos := (edgeBound_pos hh hl hr).trans ha
  have hβ : 0<q.beta := by
    apply (Chart.coefficient_quadratic_neg_iff q).mp
    rw [he]; change -a<0; linarith
  apply Chart.coefficients_injective hβ (Chart.inverseBeta_pos _)
  rw [coefficients_edgeTuning,he]

end polyak.FareyPlateau
