import polyak.ModeLocking.Periods.Least

/-! Every feasible threshold measure has all regular support atoms. In
particular a three-atom regular point admits no two-atom optimizer, even
when arbitrary candidate weights and frequencies are allowed. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels ModeLocking MeasureTheory

theorem regular_atoms_carried {q : Tuning} {s : ℝ} {L : ℕ}
    (D : RegularData q s L) {w : Measure Frequency}
    (hw : ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags w)
    (A : Set Frequency) (hA : ∀ᵐ ω ∂w, ω∈A) : ∀i,D.atoms i∈A := by
  obtain ⟨c,a,hc,he,_⟩ := D.extremal_classification
    (fun n hn=>D.lags_nonzero n hn) hw
  rw [he] at hA
  have hcar : ∀ᵐ ω ∂((c:ENNReal) • D.measure), ω∈A :=
    ae_mono (Measure.le_add_right (le_refl ((c:ENNReal) • D.measure))) hA
  have hcn : (c:ENNReal)≠0 := by exact_mod_cast hc.ne'
  rw [Measure.ae_ennreal_smul_measure_iff hcn] at hcar
  exact (D.measure_carried_iff A).mp hcar

theorem regular_support_card_le {q : Tuning} {s : ℝ} {L m : ℕ}
    (D : RegularData q s L) (weights : Fin m→NNReal) (sites : Fin m→Frequency)
    (hw : ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags
      (atomicMeasure weights sites)) : D.d≤m := by
  classical
  have hcar : ∀ᵐ ω ∂atomicMeasure weights sites, ω∈Set.range sites := by
    unfold atomicMeasure
    rw [ae_finsetSum_measure_iff]
    intro i _
    apply Measure.ae_smul_measure
    rw [ae_dirac_eq]
    exact ⟨i,rfl⟩
  have ha := regular_atoms_carried D hw (Set.range sites) hcar
  let f : Fin D.d→Fin m := fun i=>Classical.choose (ha i)
  have hf : Function.Injective f := by
    intro i j hij
    apply D.atoms_injective
    calc
      D.atoms i=sites (f i) := (Classical.choose_spec (ha i)).symm
      _=sites (f j) := congrArg sites hij
      _=D.atoms j := Classical.choose_spec (ha j)
  simpa using Fintype.card_le_of_injective f hf

theorem regular_no_two_atom {q : Tuning} {s : ℝ} {L : ℕ}
    (D : RegularData q s L) (hd : 3≤D.d)
    (weights : Fin 2→NNReal) (sites : Fin 2→Frequency) :
    ¬ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags
      (atomicMeasure weights sites) := by
  intro hw
  have := regular_support_card_le D weights sites hw
  omega

end polyak.CertifiedExamples.Plateaus
