import polyak.Farey.Positions.Permutation
import polyak.Levels.Program.AtomicProgram
import polyak.Levels.Geometry.DipSets

/-! The exact position program, including its minimizer constraint, and
the literal bad-position and anchor tests. -/
noncomputable section
namespace polyak.Farey
open Levels MeasureTheory

theorem positionValue_nonneg_iff {k : ℤ} {a ρ : ℝ} (hk : 0<k)
    (ha : 0<a) (hak : a≤k) (hρ : 0<ρ) (hρk : ρ<k) :
    0≤positionValue k a ρ ↔ a≤ρ := by
  rw [←not_lt,positionValue_neg_iff hk ha hak hρ hρk,not_lt]

theorem bad_positions_ceil {k ρ : ℤ} {a : ℝ} (hk : 0<k)
    (ha : 0<a) (hak : a≤k) (hρ : 1≤ρ) (hρk : ρ<k) :
    positionValue k a ρ<0 ↔ ρ≤⌈a⌉-1 := by
  rw [positionValue_neg_iff hk ha hak (by exact_mod_cast (show 0<ρ by omega)) (by exact_mod_cast hρk)]
  rw [←Int.lt_ceil]
  omega

theorem gridPhase_le_index_iff_closedDip (Θ : Curve) (k i : ℤ)
    (hk : 0<k) (hi : 0 ≤ i) (hik : 2 * i ≤ k) :
    gridPhase Θ k i hk hi hik ≤ i ↔ gridFrequency k i hk hi hik∈Geometry.closedDip Θ := by
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  change (k:ℝ)*Θ (gridFrequency k i hk hi hik)/Real.pi ≤ i ↔
    Θ (gridFrequency k i hk hi hik)≤(2*Real.pi*i/k)/2
  rw [div_le_iff₀ Real.pi_pos]
  rw [show (2*Real.pi*i/(k:ℝ))/2=Real.pi*i/k by ring,le_div_iff₀ hkr]
  constructor <;> intro h <;> nlinarith

theorem position_program_iff {J : Type*} [Fintype J] (Θ : Curve) {j k : ℕ}
    (hk : 0<k) (hjk : j.Coprime k) (b : ℤ) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (i : J→ℤ) (hi : ∀z,0 ≤ i z) (hik : ∀z,2 * i z ≤ k)
    (w : J→NNReal) (hw : 0<∑z,w z) :
    let ω:=fun z=>gridFrequency k (i z) (by exact_mod_cast hk) (hi z) (hik z)
    ProgramSolution Θ nonzeroLags (atomicMeasure w ω) ↔
      0≤∑z,(w z:ℝ)*Real.cos (Θ (ω z)) ∧
      ∀p : ℤ,0≤p→p<(k:ℤ)→
        0≤∑z,(w z:ℝ)*positionValue k (gridPhase Θ k (i z)
          (by exact_mod_cast hk) (hi z) (hik z)) (((i z*b)*p)%(k:ℤ):ℤ) := by
  dsimp only
  let ω:=fun z=>gridFrequency k (i z) (by exact_mod_cast hk) (hi z) (hik z)
  have heq (n : ℤ) :
      (∑z,(w z:ℝ)*Θ.lag n (ω z))=
      ∑z,(w z:ℝ)*positionValue k (gridPhase Θ k (i z)
        (by exact_mod_cast hk) (hi z) (hik z)) (((i z*b)*((n*(j:ℤ))%k))%k:ℤ) := by
    apply Finset.sum_congr rfl
    intro z _
    rw [lag_at_grid_eq_positionValue, residue_transport_of_inverse hb]
  constructor
  · intro h
    have hmin:=h.2.2.1
    rw [atomicMeasure_integral] at hmin
    refine ⟨hmin,?_⟩
    intro p hp hpk
    obtain ⟨n,hn⟩:=signed_positions_surjective hjk hk p
    rw [Int.emod_eq_of_lt hp hpk] at hn
    have hnineq : 0≤∑z,(w z:ℝ)*Θ.lag n (ω z) := by
      by_cases hn0 : n=0
      · simp [hn0,Curve.lag_zero]
      · have hh:=h.2.2.2 n hn0
        rwa [atomicMeasure_integral] at hh
    rwa [heq n,hn] at hnineq
  · rintro ⟨hmin,hpos⟩
    refine ⟨inferInstance,atomicMeasure_ne_zero w ω hw,?_,?_⟩
    · rw [atomicMeasure_integral]
      exact hmin
    · intro n _
      rw [atomicMeasure_integral,heq n]
      exact hpos ((n*(j:ℤ))%k)
        (Int.emod_nonneg _ (by exact_mod_cast (ne_of_gt hk)))
        (Int.emod_lt_of_pos _ (by exact_mod_cast hk))

end polyak.Farey
