import polyak.ModeLocking.Plateaus.TightClasses

/-! Positive kernels on an intrinsic two-point support, without identifying
or choosing the indexing of two different regular certificates. -/
noncomputable section
namespace polyak.ModeLocking.Plateaus
open General Levels Set MeasureTheory
open scoped BigOperators

theorem two_point_primal {q : Tuning} {s : ℝ} {L : ℕ} (R : RegularData q s L)
    (u : Fin 2→Frequency) (hu : Function.Injective u) (hS : Set.range R.atoms=Set.range u) :
    ∃a b : ℝ,0<a ∧ 0<b ∧ ∀f : Frequency→ℝ,
      (∑i,(R.primal i : ℝ)*f (R.atoms i))=a*f (u 0)+b*f (u 1) := by
  classical
  obtain ⟨i₀,hi₀⟩ := (hS.symm ▸ (show u 0∈Set.range u from ⟨0,rfl⟩))
  obtain ⟨i₁,hi₁⟩ := (hS.symm ▸ (show u 1∈Set.range u from ⟨1,rfl⟩))
  have hne : i₀≠i₁ := by
    intro he
    have h := hu (hi₀.symm.trans ((congrArg R.atoms he).trans hi₁))
    exact (by decide : (0 : Fin 2)≠1) h
  have hall (i : Fin R.d) : i=i₀ ∨ i=i₁ := by
    obtain ⟨j,hj⟩ := hS ▸ (show R.atoms i∈Set.range R.atoms from ⟨i,rfl⟩)
    fin_cases j
    · exact Or.inl (R.atoms_injective (hj.symm.trans hi₀.symm))
    · exact Or.inr (R.atoms_injective (hj.symm.trans hi₁.symm))
  have huniv : (Finset.univ : Finset (Fin R.d))={i₀,i₁} := by
    ext i
    simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
    exact hall i
  refine ⟨R.primal i₀,R.primal i₁,by exact_mod_cast R.primal_pos i₀,
    by exact_mod_cast R.primal_pos i₁,?_⟩
  intro f
  rw [huniv]
  simp only [Finset.sum_pair hne,hi₀,hi₁]

theorem two_point_tight_determinant {q : Tuning} {s : ℝ} {L : ℕ}
    (R : RegularData q s L) (u : Fin 2→Frequency) (hu : Function.Injective u)
    (hS : Set.range R.atoms=Set.range u) {n m : ℤ}
    (hn : TightLagAt q s n) (hm : TightLagAt q s m) :
    (Geometry.shiftedCurve q s).lag n (u 0)*(Geometry.shiftedCurve q s).lag m (u 1)-
      (Geometry.shiftedCurve q s).lag n (u 1)*(Geometry.shiftedCurve q s).lag m (u 0)=0 := by
  obtain ⟨a,b,ha,_,hsum⟩ := two_point_primal R u hu hS
  have he₁ := hn R.measure R.primal_feasible
  have he₂ := hm R.measure R.primal_feasible
  rw [RegularData.measure,atomicMeasure_integral,hsum] at he₁ he₂
  have he : a*((Geometry.shiftedCurve q s).lag n (u 0)*(Geometry.shiftedCurve q s).lag m (u 1)-
      (Geometry.shiftedCurve q s).lag n (u 1)*(Geometry.shiftedCurve q s).lag m (u 0))=0 := by
    linear_combination (Geometry.shiftedCurve q s).lag m (u 1)*he₁-
      (Geometry.shiftedCurve q s).lag n (u 1)*he₂
  exact (mul_eq_zero.mp he).resolve_left ha.ne'

end polyak.ModeLocking.Plateaus
