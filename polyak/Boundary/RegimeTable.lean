import polyak.Boundary.ActualRegimes

/-!
Article: Table regimes, the six physical condition-number intervals.
Use: these statements concern the actual maximal exponent at each κ, so the
four source-family formulas and their active-lag theorems apply directly.
-/
noncomputable section
namespace polyak.Boundary
open Spectral Regularity Set

theorem switch_lt_iff_exponent_lt {κ : ℝ} (hκ : 1<κ) (i : Fin 5) :
    switchingKappa i<κ ↔ switchingExponent i<conditionExponent κ := by
  simpa only [not_le] using not_congr (le_switch_iff_exponent_le hκ i)

theorem lt_switch_iff_exponent_lt {κ : ℝ} (hκ : 1<κ) (i : Fin 5) :
    κ<switchingKappa i ↔ conditionExponent κ<switchingExponent i := by
  simpa only [not_le] using not_congr (switch_le_iff_exponent_le hκ i)

theorem cosh_lt_iff_abs_lt_arcosh {G t : ℝ} (hG : 1≤G) :
    Real.cosh t<G ↔ |t|<Real.arcosh G := by
  calc
    Real.cosh t<G ↔ Real.cosh t<Real.cosh (Real.arcosh G) := by rw [Real.cosh_arcosh hG]
    _ ↔ |t|<Real.arcosh G := by rw [Real.cosh_lt_cosh,abs_of_nonneg (Real.arcosh_nonneg hG)]

theorem lt_cosh_iff_arcosh_lt_abs {G t : ℝ} (hG : 1≤G) :
    G<Real.cosh t ↔ Real.arcosh G < |t| := by
  calc
    G<Real.cosh t ↔ Real.cosh (Real.arcosh G)<Real.cosh t := by rw [Real.cosh_arcosh hG]
    _ ↔ Real.arcosh G < |t| := by rw [Real.cosh_lt_cosh,abs_of_nonneg (Real.arcosh_nonneg hG)]

theorem regime_p1 {κ : ℝ} (hκ : 1<κ) (hW : κ<switchingKappa 0) :
    GW<Real.cosh (conditionExponent κ) := by
  have ht := (lt_switch_iff_exponent_lt hκ 0).mp hW
  change conditionExponent κ< -Real.arcosh GW at ht
  have hp : 0<Real.arcosh GW := Real.arcosh_pos (by linarith [GW_bounds.1])
  apply (lt_cosh_iff_arcosh_lt_abs (by linarith [GW_bounds.1])).mpr
  rw [abs_of_neg (by linarith : conditionExponent κ<0)]
  linarith

theorem regime_spiral_left {κ : ℝ} (hκ : 1<κ)
    (hW : switchingKappa 0≤κ) (h₁ : κ≤switchingKappa 1) :
    G1≤Real.cosh (conditionExponent κ) ∧ Real.cosh (conditionExponent κ)≤GW := by
  have hl := (switch_le_iff_exponent_le hκ 0).mp hW
  have hu := (le_switch_iff_exponent_le hκ 1).mp h₁
  apply (actual_spiral_cosh_iff_exponents (Threshold.conditionQ_mem hκ).1
    (Threshold.conditionQ_mem hκ).2).mpr
  exact Or.inl ⟨hl,hu⟩

theorem regime_p2_left {κ : ℝ} (hκ : 1<κ)
    (h₁ : switchingKappa 1<κ) (ha : κ<switchingKappa 2) :
    P2.Ga<Real.cosh (conditionExponent κ) ∧ Real.cosh (conditionExponent κ)<G1 := by
  have hl := (switch_lt_iff_exponent_lt hκ 1).mp h₁
  have hu := (lt_switch_iff_exponent_lt hκ 2).mp ha
  change -Real.arcosh G1<conditionExponent κ at hl
  change conditionExponent κ< -Real.arcosh P2.Ga at hu
  have haG : 1<P2.Ga := by linarith [P2.Ga_bounds.1]
  have h₁G : 1<G1 := by linarith [G1_bounds.1]
  have ht : conditionExponent κ<0 := by linarith [Real.arcosh_pos haG]
  constructor
  · apply (lt_cosh_iff_arcosh_lt_abs haG.le).mpr
    rw [abs_of_neg ht]
    linarith
  · apply (cosh_lt_iff_abs_lt_arcosh h₁G.le).mpr
    rw [abs_of_neg ht]
    linarith

theorem regime_p5 {κ : ℝ} (hκ : 1<κ)
    (ha : switchingKappa 2<κ) (hb : κ<switchingKappa 3) :
    Real.cosh (conditionExponent κ)<P2.Ga := by
  have hl := (switch_lt_iff_exponent_lt hκ 2).mp ha
  have hu := (lt_switch_iff_exponent_lt hκ 3).mp hb
  apply (cosh_lt_iff_abs_lt_arcosh (by linarith [P2.Ga_bounds.1])).mpr
  exact abs_lt.mpr ⟨hl,hu⟩

theorem regime_p2_right {κ : ℝ} (hκ : 1<κ)
    (hb : switchingKappa 3<κ) (h₂ : κ<switchingKappa 4) :
    P2.Ga<Real.cosh (conditionExponent κ) ∧ Real.cosh (conditionExponent κ)<G1 := by
  have hl := (switch_lt_iff_exponent_lt hκ 3).mp hb
  have hu := (lt_switch_iff_exponent_lt hκ 4).mp h₂
  change Real.arcosh P2.Ga<conditionExponent κ at hl
  change conditionExponent κ<Real.arcosh G1 at hu
  have haG : 1<P2.Ga := by linarith [P2.Ga_bounds.1]
  have h₁G : 1<G1 := by linarith [G1_bounds.1]
  have ht : 0<conditionExponent κ := (Real.arcosh_pos haG).trans hl
  constructor
  · apply (lt_cosh_iff_arcosh_lt_abs haG.le).mpr
    rwa [abs_of_pos ht]
  · apply (cosh_lt_iff_abs_lt_arcosh h₁G.le).mpr
    rwa [abs_of_pos ht]

theorem regime_spiral_right {κ : ℝ} (hκ : 1<κ) (h₂ : switchingKappa 4≤κ) :
    G1≤Real.cosh (conditionExponent κ) ∧ Real.cosh (conditionExponent κ)≤GW := by
  have hl := (switch_le_iff_exponent_le hκ 4).mp h₂
  apply (actual_spiral_cosh_iff_exponents (Threshold.conditionQ_mem hκ).1
    (Threshold.conditionQ_mem hκ).2).mpr
  exact Or.inr hl

end polyak.Boundary
