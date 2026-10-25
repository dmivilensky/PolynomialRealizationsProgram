import polyak.ModeLocking.Continuation.AdjugateTransversality
import polyak.ModeLocking.Continuation.AdjugateDerivative

/-! Jacobi's formula at the actual tight matrix gives the source's nonzero
shift derivative of its determinant, directly from R1--R3. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

def shiftEntryDerivative (r i : Fin D.d) : ℝ :=
  deriv (fun t => (Geometry.shiftedCurve q t).lag (D.reps r) (D.atoms i)) s

theorem hasDerivAt_tightMatrix_shift (r i : Fin D.d) :
    HasDerivAt (fun t => Continuation.tightMatrix D.reps D.atoms
      (Continuation.sourcePoint q t) r i) (D.shiftEntryDerivative r i) s := by
  have hh := (Continuation.hasDerivAt_lag_shift q s (D.reps r) (D.atoms i)
    ⟨(D.atoms_grid i).1,D.atoms_lt_pi i⟩).differentiableAt.hasDerivAt
  convert hh using 1
  · funext t
    exact Continuation.ambientLag_actual q t (D.reps r) (D.atoms i)
  · rfl

theorem weighted_shiftEntryDerivative (r : Fin D.d) :
    (∑ i,D.shiftEntryDerivative r i*(D.primal i:ℝ))=D.shiftVector r := by
  unfold shiftVector primalResidual
  rw [deriv_fun_sum (fun i _ =>
    ((Continuation.hasDerivAt_lag_shift q s (D.reps r) (D.atoms i)
      ⟨(D.atoms_grid i).1,D.atoms_lt_pi i⟩).differentiableAt.const_mul _))]
  simp only [deriv_const_mul_field,shiftEntryDerivative]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The exact nonzero adjugate scalar multiplies the positive source
transversality contraction in the determinant derivative. -/
theorem tightDeterminant_shift_factor : ∃ c : ℝ, c≠0 ∧
    deriv (fun t => Continuation.tightDeterminant D.reps D.atoms
      (Continuation.sourcePoint q t)) s =
      c*(∑ r,D.classWeight r*D.shiftVector r) := by
  let M : ℝ → Matrix (Fin D.d) (Fin D.d) ℝ := fun t =>
    Continuation.tightMatrix D.reps D.atoms (Continuation.sourcePoint q t)
  have hM : M s=D.matrix := by
    ext r i
    exact Continuation.ambientLag_actual q s (D.reps r) (D.atoms i)
  have hd := Continuation.hasDerivAt_det M D.shiftEntryDerivative s
    (fun r i => D.hasDerivAt_tightMatrix_shift r i)
  rw [hM] at hd
  obtain ⟨c,hc,hfactor⟩ := D.adjugate_contraction_factor D.shiftEntryDerivative
  simp_rw [D.weighted_shiftEntryDerivative] at hfactor
  refine ⟨c,hc,?_⟩
  exact hd.deriv.trans hfactor

theorem tightDeterminant_shift_ne_zero :
    deriv (fun t => Continuation.tightDeterminant D.reps D.atoms
      (Continuation.sourcePoint q t)) s ≠ 0 := by
  obtain ⟨c,hc,hfactor⟩ := D.tightDeterminant_shift_factor
  rw [hfactor]
  exact mul_ne_zero hc D.transversality_pos.ne'

end polyak.ModeLocking.RegularData
