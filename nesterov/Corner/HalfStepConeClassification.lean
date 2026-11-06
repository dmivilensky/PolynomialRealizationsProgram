import nesterov.Corner.HalfStepCone
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! Every noncanonical frequency in (0,π] lies strictly between two
consecutive canonical rational angles. -/
namespace nesterov.Corner
noncomputable section

 theorem canonical_angle_or_strict_gap {ω : ℝ} (hω : 0<ω) (hωπ : ω≤Real.pi) :
    ∃ K : ℕ,2≤K ∧ (ω=2*Real.pi/K ∨
      2*Real.pi/((K:ℝ)+1)<ω ∧ ω<2*Real.pi/K) := by
  let u : ℝ := 2*Real.pi/ω
  let K : ℕ := Nat.floor u
  have hu : (2:ℝ)≤u := (le_div_iff₀ hω).mpr (by nlinarith)
  have hK : 2≤K := Nat.le_floor hu
  have hKreal : (2:ℝ)≤K := by exact_mod_cast hK
  have hKpos : (0:ℝ)<K := by linarith
  have hKu : (K:ℝ)≤u := Nat.floor_le (by linarith : 0≤u)
  have huK : u<(K:ℝ)+1 := Nat.lt_floor_add_one u
  refine ⟨K,hK,?_⟩
  by_cases he : ω=2*Real.pi/K
  · exact Or.inl he
  · right
    have hstrict : (K:ℝ)<u := by
      by_contra hn
      have heq : (K:ℝ)=u := le_antisymm hKu (le_of_not_gt hn)
      change (K:ℝ)=2*Real.pi/ω at heq
      have hp := (eq_div_iff hω.ne').mp heq
      apply he
      apply (eq_div_iff hKpos.ne').mpr
      nlinarith only [hp]
    have hlo : 2*Real.pi/((K:ℝ)+1)<ω := by
      have hh := (div_lt_iff₀ hω).mp huK
      apply (div_lt_iff₀ (by linarith : 0<(K:ℝ)+1)).mpr
      nlinarith only [hh]
    have hhi : ω<2*Real.pi/K := by
      have hh := (lt_div_iff₀ hω).mp hstrict
      apply (lt_div_iff₀ hKpos).mpr
      nlinarith only [hh]
    exact ⟨hlo,hhi⟩


theorem halfStepUpper_nonneg_iff {ω : ℝ} (hω : 0<ω) (hωπ : ω≤Real.pi) :
    (∀ n : ℕ,0≤halfStepUpper ω n) ↔ ∃ K : ℕ,2≤K ∧ ω=2*Real.pi/K := by
  constructor
  · intro h
    obtain ⟨K,hK,he|⟨hlo,hhi⟩⟩ := canonical_angle_or_strict_gap hω hωπ
    · exact ⟨K,hK,he⟩
    · exact False.elim ((not_lt_of_ge (h K)) (halfStepUpper_gap_negative hK hlo hhi))
  · rintro ⟨K,hK,rfl⟩ n
    exact halfStepUpper_atom hK n

theorem halfStep_singleton_iff {ω : ℝ} (hω : 0<ω) (hωπ : ω≤Real.pi) :
    (∀ n : ℕ,0≤Real.sin ((n:ℝ)*ω/2)*Real.sin (((n:ℝ)+1)*ω/2)) ↔
      ∃ K : ℕ,2≤K ∧ ω=2*Real.pi/K :=
  halfStepUpper_nonneg_iff hω hωπ

theorem halfStep_positive_lags_iff {ω : ℝ} (hω : 0<ω) (hωπ : ω≤Real.pi) :
    (∀ n : ℕ,1≤n → 0≤halfStepUpper ω n ∧ 0≤halfStepLower ω n) ↔
      ∃ K : ℕ,2≤K ∧ ω=2*Real.pi/K := by
  constructor
  · intro h
    apply (halfStepUpper_nonneg_iff hω hωπ).mp
    intro n
    by_cases hn : n=0
    · subst n
      simp [halfStepUpper]
    · exact (h n (by omega)).1
  · rintro ⟨K,hK,rfl⟩ n _
    exact ⟨halfStepUpper_atom hK n,halfStepLower_atom hK n⟩

end
end nesterov.Corner
