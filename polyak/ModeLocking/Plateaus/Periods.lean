import polyak.ModeLocking.Plateaus.Definitions
import polyak.ModeLocking.Periods.Least

/-! The canonical least-period label agrees with the period in every
primary regular certificate; its definition is independent of that choice. -/
noncomputable section
namespace polyak.ModeLocking.Plateaus
open General Levels Set

theorem leastPeriod_eq_chosen (q : RegularTuning) : leastPeriod q=chosenPeriod q := by
  have hleast : IsLeast {L : ℕ | 3≤L ∧ support q⊆periodicGrid L} (chosenPeriod q) := by
    refine ⟨⟨(chosenData q).period_ge,?_⟩,?_⟩
    · rintro _ ⟨i,rfl⟩
      exact (chosenData q).atoms_grid i
    · intro k hk
      apply Nat.le_of_dvd (lt_of_lt_of_le (by norm_num : 0<3) hk.1)
      apply ((chosenData q).support_period_iff_dvd k).mp
      intro i
      exact hk.2 ⟨i,rfl⟩
  exact hleast.csInf_eq

theorem leastPeriod_eq {q : Tuning} (hq : q∈regularTunings) {L : ℕ}
    (D : RegularData q (Threshold.sigma q) L) : leastPeriod ⟨q,hq⟩=L := by
  have hsupport := support_eq hq D
  have hleast : IsLeast {k : ℕ | 3≤k ∧ support ⟨q,hq⟩⊆periodicGrid k} L := by
    refine ⟨⟨D.period_ge,?_⟩,?_⟩
    · intro ω hω
      rw [hsupport] at hω
      obtain ⟨i,rfl⟩ := hω
      exact D.atoms_grid i
    · intro k hk
      apply Nat.le_of_dvd (lt_of_lt_of_le (by norm_num : 0<3) hk.1)
      apply (D.support_period_iff_dvd k).mp
      intro i
      exact hk.2 (hsupport ▸ ⟨i,rfl⟩)
  exact hleast.csInf_eq

end polyak.ModeLocking.Plateaus
