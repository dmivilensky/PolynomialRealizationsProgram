import polyak.Levels.Chart.GapHomeomorphism
import polyak.General.Regions.TongueCriteria

/-! Literal rational tongue graphs in the gap coordinates. -/
noncomputable section
namespace polyak.Levels.Chart
open General Set

def rationalCosine (j k : ℕ) : ℝ := Real.cos (Regions.rationalAngle j k)
def rationalHeight (j k : ℕ) : ℝ :=
  (Real.cos (Real.pi/k)/Real.sin (Real.pi/k))*Real.sin (Regions.rationalAngle j k)
def tongueAmplitude (j k : ℕ) (r₁ r₂ : ℝ) : ℝ :=
  tongueHeight (rationalCosine j k) (rationalHeight j k) r₁ r₂

theorem rationalHeight_gt_baseline {j k : ℕ} (hj : 2≤j) (hjk : 2*j<k) :
    1+rationalCosine j k<rationalHeight j k := by
  have hω := Regions.rationalAngle_mem (show 1≤j by omega) hjk
  have hk : 0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hφ : Real.pi/k∈Ioo (0:ℝ) Real.pi := by
    exact ⟨div_pos Real.pi_pos hk,div_lt_self Real.pi_pos (by exact_mod_cast (show 1<k by omega))⟩
  have hhalf : Regions.rationalAngle j k/2∈Ioo (0:ℝ) Real.pi :=
    ⟨by linarith [hω.1],by linarith [hω.2,Real.pi_pos]⟩
  have hφhalf : Real.pi/k<Regions.rationalAngle j k/2 := by
    have hjr : (1:ℝ)<j := by exact_mod_cast (show 1<j by omega)
    unfold Regions.rationalAngle
    apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_lt_div_iff_of_pos_right hk).mpr
    nlinarith [Real.pi_pos]
  have hcot := (cot_strictAnti hhalf hφ).mpr hφhalf
  rw [cot_half hω] at hcot
  have hsin := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hm := mul_lt_mul_of_pos_right hcot hsin
  rw [div_mul_cancel₀ _ (ne_of_gt hsin)] at hm
  exact hm

theorem rational_tongue_graph (q : Tuning) {j k : ℕ} (hj : 2≤j) (hjk : 2*j<k)
    {a r₁ r₂ : ℝ} (ha : 0<a) (hr : r₁<r₂)
    (he : coefficients q=gapPolynomial a r₁ r₂) :
    q.angle (Regions.rationalAngle j k)≤Real.pi/k ↔
      r₁<rationalCosine j k ∧ rationalCosine j k<r₂ ∧ tongueAmplitude j k r₁ r₂≤a := by
  rw [(Regions.rational_angle_le_iff_explicit q (show 1≤j by omega) hjk).1]
  have hpoly : q.Xi (rationalCosine j k)=(gapPolynomial a r₁ r₂).eval (rationalCosine j k) := by
    rw [←eval_coefficients,he]
  change rationalHeight j k≤q.Xi (rationalCosine j k) ↔ _
  rw [hpoly]
  exact gapPolynomial_tongue_iff ha hr (rationalHeight_gt_baseline hj hjk)

/-- Fractions are expressed as the exact real inequalities from the source. -/
def FractionInWindow (K j k : ℕ) : Prop :=
  0<k ∧ 1/((K:ℝ)+1)<(j:ℝ)/k ∧ (j:ℝ)/k<1/(K:ℝ)

theorem fraction_window_arithmetic {K j k : ℕ} (hK : 2≤K)
    (hf : FractionInWindow K j k) : 2≤j ∧ 2*j<k := by
  have hk : 0<(k:ℝ) := by exact_mod_cast hf.1
  have hkr : 0<(K:ℝ) := by exact_mod_cast (show 0<K by omega)
  have hl : (k:ℝ)<(j:ℝ)*((K:ℝ)+1) := by
    have h := (div_lt_div_iff₀ (by positivity : 0<(K:ℝ)+1) hk).mp hf.2.1
    nlinarith
  have hu : (j:ℝ)*(K:ℝ)<k := by
    have h := (div_lt_div_iff₀ hk hkr).mp hf.2.2
    nlinarith
  have hln : k<j*(K+1) := by exact_mod_cast hl
  have hun : j*K<k := by exact_mod_cast hu
  constructor
  · by_contra hh
    have hj : j=0 ∨ j=1 := by omega
    rcases hj with rfl|rfl <;> omega
  · nlinarith

theorem fraction_cosine_window {K j k : ℕ} (hK : 2≤K)
    (hf : FractionInWindow K j k) :
    boundaryCosine K<rationalCosine j k ∧ rationalCosine j k<boundaryCosine (K+1) := by
  obtain ⟨hj,hjk⟩ := fraction_window_arithmetic hK hf
  have hω := Regions.rationalAngle_mem (show 1≤j by omega) hjk
  apply (cos_window_iff hK ⟨hω.1.le,hω.2.le⟩).mpr
  constructor
  · have hm := mul_lt_mul_of_pos_left hf.2.1 (by positivity : 0<2*Real.pi)
    change 2*Real.pi/((K+1:ℕ):ℝ)<2*Real.pi*j/k
    rw [Nat.cast_add,Nat.cast_one]
    convert hm using 1 <;> ring
  · have hm := mul_lt_mul_of_pos_left hf.2.2 (by positivity : 0<2*Real.pi)
    change 2*Real.pi*j/k<2*Real.pi/(K:ℝ)
    convert hm using 1 <;> ring

theorem gap_tongue_graph {K j k : ℕ} (hK : 2≤K) (hf : FractionInWindow K j k)
    (q : GapTunings K) :
    q.val.angle (Regions.rationalAngle j k)≤Real.pi/k ↔
      (coordinates q.val).2.1<rationalCosine j k ∧
      rationalCosine j k<(coordinates q.val).2.2 ∧
      tongueAmplitude j k (coordinates q.val).2.1 (coordinates q.val).2.2≤(coordinates q.val).1 := by
  obtain ⟨a,r₁,r₂,h₁,hr,h₂,ha,he⟩ := root_coordinates_of_gap q.val q.property
  have hu := h₂.trans (boundaryCosine_succ_lt_one hK)
  have hap := (amplitudeFloor_pos (hr.trans hu) hu).trans ha
  rw [coordinates_of_polynomial q.val hap hr.le he]
  obtain ⟨hj,hjk⟩ := fraction_window_arithmetic hK hf
  exact rational_tongue_graph q.val hj hjk hap hr he

end polyak.Levels.Chart
