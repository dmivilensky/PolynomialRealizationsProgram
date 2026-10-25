import polyak.ModeLocking.TwoLag.ExactData

/-! E1–E3 give the literal normalized primal, all residue constraints,
and the required rank without assuming regularity. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag.ExactData
open General Levels Matrix
variable {q : Tuning} {s : ℝ} {K L : ℕ} (D : ExactData q s K L)

theorem primal_sum_mul (f : Fin 2→ℝ) :
    (∑i,(D.primal i : ℝ)*f i)=(-D.B*f 0+D.A*f 1)/(D.A-D.B) := by
  rw [Fin.sum_univ_two]
  change (-D.B)/(D.A-D.B)*f 0+D.A/(D.A-D.B)*f 1=_
  ring

theorem matrix_rank :
    Matrix.rank (fun r i : Fin 2=>(Geometry.shiftedCurve q s).lag (D.reps r) (D.u i))=1 := by
  have h := rank_one_of_positive_dual D.sign₁ D.b_pos (D.dual_zero 0) (D.dual_zero 1)
  convert h using 1
  congr 1
  ext r i
  rw [D.lag_reps]
  fin_cases r <;> fin_cases i <;> rfl

theorem tight (r : Fin 2) :
    (∑i,(D.primal i : ℝ)*(Geometry.shiftedCurve q s).lag (D.reps r) (D.u i))=0 := by
  have h := (positive_primal_kernel D.sign₁ D.sign₂ D.b_pos (D.dual_zero 0) (D.dual_zero 1)).2.2.2
  have hr := congrFun h r
  rw [D.primal_sum_mul]
  rw [D.lag_reps r 0, D.lag_reps r 1]
  fin_cases r
  · change (-D.B*D.A+D.A*D.B)/(D.A-D.B)=0
    ring
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hr
    change _=0
    convert hr using 1
    dsimp [A,B]
    ring

theorem inactive_strict (r : ℤ) (hr : 0<r) (hrL : r<L) (hne : ∀i,r≠D.reps i) :
    0<∑i,(D.primal i : ℝ)*(Geometry.shiftedCurve q s).lag r (D.u i) := by
  rw [D.primal_sum_mul]
  apply div_pos
  · exact D.inactive r hr hrL (hne 0) (hne 1)
  · have hA := D.sign₁
    have hB := D.sign₂
    dsimp [A,B]
    linarith

theorem minimizer_strict :
    0<∑i,(D.primal i : ℝ)*(Geometry.shiftedCurve q s).minimizer (D.u i) := by
  rw [D.primal_sum_mul]
  apply div_pos D.minimizer
  have hA := D.sign₁
  have hB := D.sign₂
  dsimp [A,B]
  linarith

end polyak.ModeLocking.TwoLag.ExactData
