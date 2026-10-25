import polyak.ModeLocking.Continuation.Bordered

/-! Transversality of the original normalized primal system is derived
from positive primal/dual masses and P>0 at every support frequency. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

def primalResidual (t : ℝ) (r : Fin D.d) : ℝ :=
  ∑ i, (D.primal i : ℝ) * (Geometry.shiftedCurve q t).lag (D.reps r) (D.atoms i)

def shiftVector (r : Fin D.d) : ℝ := deriv (fun t => D.primalResidual t r) s

theorem differentiable_primalResidual (r : Fin D.d) :
    DifferentiableAt ℝ (fun t => D.primalResidual t r) s := by
  apply DifferentiableAt.fun_sum
  intro i _
  exact (Continuation.hasDerivAt_lag_shift q s (D.reps r) (D.atoms i)
    ⟨(D.atoms_grid i).1, D.atoms_lt_pi i⟩).differentiableAt.const_mul _

theorem transversality_identity : (∑ r, D.classWeight r * D.shiftVector r) =
    ∑ i, (D.primal i : ℝ) * deriv (fun t => finiteSymbol q t D.lags D.dual (D.atoms i)) s := by
  have he : (fun t => ∑ r, D.classWeight r * D.primalResidual t r) =
      fun t => ∑ i, (D.primal i : ℝ) * finiteSymbol q t D.lags D.dual (D.atoms i) := by
    funext t
    simp only [primalResidual, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← D.class_sum_symbol_at t (D.atoms i) (D.atoms_grid i), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hder := congrArg (fun f : ℝ → ℝ => deriv f s) he
  rw [deriv_fun_sum (fun r _ => (D.differentiable_primalResidual r).const_mul _),
    deriv_fun_sum (fun i _ => (Continuation.hasDerivAt_finiteSymbol_shift q s D.lags D.dual
      (D.atoms i) ⟨(D.atoms_grid i).1, D.atoms_lt_pi i⟩
      (D.symbol_zero_support i)).differentiableAt.const_mul _)] at hder
  simpa only [deriv_const_mul_field, shiftVector] using hder

theorem transversality_pos : 0 < ∑ r, D.classWeight r * D.shiftVector r := by
  rw [D.transversality_identity]
  have hp (i : Fin D.d) : 0 < (D.primal i : ℝ) *
      deriv (fun t => finiteSymbol q t D.lags D.dual (D.atoms i)) s :=
    mul_pos (by exact_mod_cast D.primal_pos i) (D.shift_derivative_pos i)
  exact Finset.sum_pos' (fun i _ => (hp i).le)
    ⟨⟨0, D.d_pos⟩, Finset.mem_univ _, hp _⟩

def primalDerivativeEquiv : (ℝ × (Fin D.d → ℝ)) ≃L[ℝ] ((Fin D.d → ℝ) × ℝ) :=
  D.borderedEquiv D.shiftVector D.transversality_pos.ne'

end polyak.ModeLocking.RegularData
