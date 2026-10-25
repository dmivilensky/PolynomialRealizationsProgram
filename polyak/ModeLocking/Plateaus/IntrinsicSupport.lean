import polyak.ModeLocking.Regular.Uniqueness

/-! The finite positive support is intrinsic to a regular tuning. In
particular it is independent of the chosen grid period or certificate. -/
noncomputable section
namespace polyak.ModeLocking.Plateaus
open General Levels MeasureTheory Set Filter

/-- Any atom of positive mass belongs to every almost-everywhere carrier. -/
theorem atom_mem_of_carried {w : Measure Frequency} {A : Set Frequency}
    (hcar : ∀ᵐω∂w,ω∈A) {ω : Frequency} (hpos : 0<w {ω}) : ω∈A := by
  by_contra hn
  have hnull : w {x | x∉A}=0 := by simpa only [ae_iff] using hcar
  have hs : ({ω} : Set Frequency)⊆{x | x∉A} := by
    intro x hx
    rw [mem_singleton_iff] at hx
    subst x
    exact hn
  exact hpos.ne' (measure_mono_null hs hnull)

theorem atomicMeasure_atom_pos {J : Type*} [Fintype J] (w : J→NNReal)
    (a : J→Frequency) (i : J) (hi : 0<w i) : 0<atomicMeasure w a {a i} := by
  have hbound := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun j : J=>((w j : ENNReal)•Measure.dirac (a j)) {a i})
    (fun _ _=>bot_le) (Finset.mem_univ i)
  have hp : (0 : ENNReal)<w i := ENNReal.coe_pos.mpr hi
  apply lt_of_lt_of_le hp
  simpa only [atomicMeasure,Measure.finsetSum_apply,Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_singleton _),smul_eq_mul,mul_one] using hbound

/-- This is the support equality needed to make plateau labels canonical. -/
theorem regular_support_eq {q : Tuning} {s : ℝ} {L M : ℕ}
    (D : RegularData q s L) (E : RegularData q s M) : Set.range D.atoms=Set.range E.atoms := by
  apply Subset.antisymm
  · rintro _ ⟨i,rfl⟩
    have hcar := E.program_carried (N':=nonzeroLags)
      (fun n hn=>E.lags_nonzero n hn) D.primal_feasible
    have hmem := atom_mem_of_carried hcar
      (atomicMeasure_atom_pos D.primal D.atoms i (D.primal_pos i))
    rcases hmem with h0|⟨j,hj⟩
    · have hp := (D.atoms_grid i).1
      rw [h0] at hp
      exact (lt_irrefl 0 hp).elim
    · exact ⟨j,hj.symm⟩
  · rintro _ ⟨i,rfl⟩
    have hcar := D.program_carried (N':=nonzeroLags)
      (fun n hn=>D.lags_nonzero n hn) E.primal_feasible
    have hmem := atom_mem_of_carried hcar
      (atomicMeasure_atom_pos E.primal E.atoms i (E.primal_pos i))
    rcases hmem with h0|⟨j,hj⟩
    · have hp := (E.atoms_grid i).1
      rw [h0] at hp
      exact (lt_irrefl 0 hp).elim
    · exact ⟨j,hj.symm⟩

end polyak.ModeLocking.Plateaus
