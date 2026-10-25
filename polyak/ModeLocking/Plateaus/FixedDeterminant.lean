import polyak.ModeLocking.Plateaus.TightClasses
import polyak.ModeLocking.Continuation.Determinant

/-! The determinant equation uses one fixed ordering of the support and
classes on the entire component, rather than a different matrix at each point. -/
noncomputable section
namespace polyak.ModeLocking.Plateaus
open General Levels Set MeasureTheory Matrix
open scoped BigOperators

theorem fixed_tight_determinant_zero {q : Tuning} {s : ℝ} {L : ℕ}
    (R : RegularData q s L) {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (u : I→Frequency) (hu : Function.Injective u) (hS : Set.range R.atoms=Set.range u)
    (rows : I→ℤ) (ht : ∀r,TightLagAt q s (rows r)) :
    Matrix.det (fun r i=>(Geometry.shiftedCurve q s).lag (rows r) (u i))=0 := by
  classical
  have hex (i : I) : ∃j,R.atoms j=u i := by
    have hm : u i∈Set.range R.atoms := hS.symm ▸ (show u i∈Set.range u from ⟨i,rfl⟩)
    exact hm
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j he
    apply hu
    exact (hf i).symm.trans ((congrArg R.atoms he).trans (hf j))
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨i,hi⟩ := hS ▸ (show R.atoms j∈Set.range R.atoms from ⟨j,rfl⟩)
    exact ⟨i,R.atoms_injective ((hf i).trans hi)⟩
  let e : I≃Fin R.d := Equiv.ofBijective f ⟨hinj,hsurj⟩
  let v : I→ℝ:=fun i=>(R.primal (e i) : ℝ)
  let M : Matrix I I ℝ:=fun r i=>(Geometry.shiftedCurve q s).lag (rows r) (u i)
  have hk : M.mulVec v=0 := by
    funext r
    have h := ht r R.measure R.primal_feasible
    rw [RegularData.measure,atomicMeasure_integral] at h
    have he := e.sum_comp (fun j=>(R.primal j : ℝ)*(Geometry.shiftedCurve q s).lag (rows r) (R.atoms j))
    have hfi (i : I) : R.atoms (e i)=u i := hf i
    simp only [hfi] at he
    change (∑i,(Geometry.shiftedCurve q s).lag (rows r) (u i)*(R.primal (e i) : ℝ))=0
    simpa only [mul_comm] using he.trans h
  have hv : v≠0 := by
    obtain ⟨i⟩ := ‹Nonempty I›
    intro he
    have hi := congrFun he i
    have hp : 0<v i := by exact_mod_cast R.primal_pos (e i)
    exact hp.ne' hi
  by_contra hn
  have hi := Matrix.mulVec_injective_of_det_ne_zero (show M.det≠0 from hn)
  apply hv
  apply hi
  simpa only [Matrix.mulVec_zero] using hk

/-- One fixed source matrix vanishes at every point of the full component. -/
theorem plateau_fixed_determinant_zero (q : regularBoundary) {r : regularBoundary}
    (hr : r.val∈plateau q.val) :
    Matrix.det (fun j i : Fin (chosenData ⟨q.val.val,q.property⟩).d=>
      (tuningCurve r.val.val).lag ((chosenData ⟨q.val.val,q.property⟩).reps j)
        ((chosenData ⟨q.val.val,q.property⟩).atoms i))=0 := by
  let D := chosenData (⟨q.val.val,q.property⟩ : RegularTuning)
  let R := chosenData (⟨r.val.val,r.property⟩ : RegularTuning)
  have : Nonempty (Fin D.d) := ⟨⟨0,D.d_pos⟩⟩
  have hS : Set.range R.atoms=Set.range D.atoms := support_constant_on_plateau hr
  have ht (j : Fin D.d) : TightLagAt r.val.val (Threshold.sigma r.val.val) (D.reps j) := by
    have he := tightLags_constant_on_plateau hr
    have hbase : D.reps j∈boundaryTightLags q := (tightLagAt_iff D _).mpr
      (Or.inr (by rw [Int.emod_eq_of_lt (D.reps_pos j).le (D.reps_lt j)];exact ⟨j,rfl⟩))
    rw [← he] at hbase
    exact hbase
  have he := fixed_tight_determinant_zero R D.atoms D.atoms_injective hS D.reps ht
  rw [(mem_frontier_iff_sigma_zero r.val.val).mp r.val.property,Geometry.shiftedCurve_zero] at he
  exact he

end polyak.ModeLocking.Plateaus
