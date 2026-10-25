import polyak.ModeLocking.TwoLag.ExactRegular
import polyak.Levels.Geometry.LevelZero

/-! At zero shift, the two exact contacts force the entire dip into the
source window. No additional gap assumption is used. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General Levels Geometry Set

theorem firstFrequency_grid (K : ℕ) (hK : 2≤K) : firstFrequency K hK∈periodicGrid K := by
  have hp : (0 : ℝ)<K := by exact_mod_cast (show 0<K by omega)
  refine ⟨by dsimp [firstFrequency];positivity,1,?_⟩
  dsimp [firstFrequency]
  push_cast
  field_simp

theorem firstFrequency_lag_period (Θ : Curve) (K : ℕ) (hK : 2≤K) :
    Θ.lag (-(K : ℤ)) (firstFrequency K hK)=0 := by
  have h := lag_add_mul_grid Θ (firstFrequency_grid K hK) 0 (-1)
  simpa using h

theorem firstFrequency_lag_neighbor (Θ : Curve) (K : ℕ) (hK : 2≤K) :
    Θ.lag (-(K : ℤ)) (firstFrequency (K+1) (by omega))=
      Θ.lag 1 (firstFrequency (K+1) (by omega)) := by
  have h := lag_add_mul_grid Θ (firstFrequency_grid (K+1) (by omega)) 1 (-1)
  convert h using 1
  congr 1
  push_cast
  ring

namespace ExactData
variable {q : Tuning} {K L : ℕ} (D : ExactData q 0 K L)

include D in
theorem gap_of_first_contact_window (hwin : InWindow K (D.u 0)) : Gap K q := by
  have hK := D.K_ge
  let Θ := Geometry.shiftedCurve q 0
  have hΘ : Θ=tuningCurve q := shiftedCurve_zero q
  have hfirst (k : ℕ) (hk : 2≤k) : 0<(firstFrequency k hk : ℝ) :=
    (firstFrequency_grid k hk).1
  have hloVal : (firstFrequency (K+1) (by omega) : ℝ)=2*Real.pi/((K : ℝ)+1) := by
    simp [firstFrequency]
  have hhi1 := firstFrequency_lag_period Θ K D.K_ge
  have hlo1 := firstFrequency_lag_neighbor Θ K D.K_ge
  have hhi : firstFrequency K D.K_ge∉closedDip Θ := by
    intro hc
    have hneq0 : (firstFrequency K D.K_ge : ℝ)≠0 := (hfirst K D.K_ge).ne'
    have hneqU : (firstFrequency K D.K_ge : ℝ)≠(D.u 0 : ℝ) := by
      intro he
      have h := hwin.2
      change (D.u 0 : ℝ)<(firstFrequency K D.K_ge : ℝ) at h
      linarith
    have hneqV : (firstFrequency K D.K_ge : ℝ)≠(D.u 1 : ℝ) := by
      intro he
      have hfeq : firstFrequency K D.K_ge=D.u 1 := Subtype.ext he
      rw [hfeq] at hhi1
      exact D.opposite₂.ne' hhi1
    have hneg := D.strict_off_zeros (firstFrequency K D.K_ge)
      (firstFrequency K D.K_ge).property (by
        simp only [zeros,Finset.mem_insert,Finset.mem_singleton,not_or]
        exact ⟨hneq0,hneqU,hneqV⟩)
    rw [extension_actual,hhi1,mul_zero,add_zero] at hneg
    have hn := (Geometry.lag_one_neg_iff Θ _).mp (neg_of_mul_neg_right hneg D.a_pos.le)
    exact not_le_of_gt hn.2 hc
  have hlo : firstFrequency (K+1) (by omega)∉closedDip Θ := by
    intro hc
    have hneq0 : (firstFrequency (K+1) (by omega) : ℝ)≠0 := (hfirst (K+1) (by omega)).ne'
    have hneqU : (firstFrequency (K+1) (by omega) : ℝ)≠(D.u 0 : ℝ) := by
      intro he
      have h := hwin.1
      rw [←hloVal] at h
      linarith
    have hneqV : (firstFrequency (K+1) (by omega) : ℝ)≠(D.u 1 : ℝ) := by
      intro he
      have hfeq : firstFrequency (K+1) (by omega)=D.u 1 := Subtype.ext he
      rw [hfeq] at hlo1
      have hpos := D.opposite₂
      have hneg := D.sign₂
      rw [hlo1] at hpos
      linarith
    have hneg := D.strict_off_zeros (firstFrequency (K+1) (by omega))
      (firstFrequency (K+1) (by omega)).property (by
        simp only [zeros,Finset.mem_insert,Finset.mem_singleton,not_or]
        exact ⟨hneq0,hneqU,hneqV⟩)
    rw [extension_actual,hlo1,←add_mul,D.normalized,one_mul] at hneg
    have hn := (Geometry.lag_one_neg_iff Θ _).mp hneg
    exact not_le_of_gt hn.2 hc
  have hu : D.u 0∈closedDip Θ :=
    (show Θ (D.u 0)<(D.u 0 : ℝ)/2 from (lag_one_pos_iff Θ _).mp D.sign₁).le
  have hord : (closedDip Θ).OrdConnected := closedDip_ordConnected q 0
  have hwindow : ∀ω∈closedDip Θ,InWindow K ω := by
    intro ω hω
    constructor
    · by_contra hn
      apply hlo
      apply hord.out hω hu
      constructor
      · change (ω : ℝ)≤(firstFrequency (K+1) (by omega) : ℝ)
        rw [hloVal]
        exact le_of_not_gt hn
      · change (firstFrequency (K+1) (by omega) : ℝ)≤(D.u 0 : ℝ)
        rw [hloVal]
        exact hwin.1.le
    · by_contra hn
      apply hhi
      apply hord.out hu hω
      exact ⟨hwin.2.le,le_of_not_gt hn⟩
  apply gap_of_closedDip_window q D.K_ge
  · exact ⟨D.u 0,by rw [←hΘ];exact (lag_one_pos_iff Θ _).mp D.sign₁⟩
  · simpa only [←hΘ] using hwindow

end ExactData
end polyak.ModeLocking.TwoLag
