import polyak.ModeLocking.TwoLag.ExactPerturbation
import polyak.ModeLocking.TwoLag.ExactPrimal

/-! Complete construction of R1, R2 and R3 from the primary E1–E4 data. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag.ExactData
open General Levels Matrix Set
variable {q : Tuning} {s : ℝ} {K L : ℕ} (D : ExactData q s K L)

theorem reps_pos (i : Fin 2) : 0<D.reps i := by
  have hK := D.K_ge
  have hL := D.L_ge
  fin_cases i
  · norm_num [reps]
  · simp only [reps]
    change (0 : ℤ)<(L : ℤ)-K
    omega

theorem reps_lt (i : Fin 2) : D.reps i<L := by
  have hK := D.K_ge
  have hL := D.L_ge
  fin_cases i <;> simp [reps] <;> omega

theorem reps_injective : Function.Injective D.reps := by
  have hK := D.K_ge
  have hL := D.L_ge
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (simp [reps] at hij; omega)

theorem sin_reps (i r : Fin 2) :
    Real.sin ((D.reps r : ℝ)*(D.u i : ℝ)-Geometry.shiftedCurve q s (D.u i))=
      Real.sin (((![1,-(K : ℤ)] : Fin 2→ℤ) r : ℝ)*(D.u i : ℝ)-
        Geometry.shiftedCurve q s (D.u i)) := by
  fin_cases r
  · rfl
  · simp [reps]
    have h := sin_lag_add_mul_grid (D.grid i) (-(K : ℤ)) 1 (Geometry.shiftedCurve q s (D.u i))
    convert h using 1
    all_goals simp only [Geometry.shiftedCurve_apply]
    all_goals congr 1
    all_goals push_cast
    all_goals ring

/-- Theorem exact: all three source regularity conditions are obtained,
with exactly the displayed six signed lags. -/
theorem exists_regularData : ∃R : RegularData q s L,
    Set.range R.atoms=Set.range D.u ∧ R.lags=pinLags K L := by
  obtain ⟨ε,hε,hεa,hεb,⟨C⟩⟩ := exists_positive_pinning D
  have hcurv (z : ℝ) (hz : z∈D.zeros) :
      deriv^[2] (finiteSymbol q s (pinLags K L) (pinWeight K D.a D.b ε)) z<0 := by
    have h := C.local_bound z hz z (D.zeros_subset z hz) (by
      simp only [sub_self, abs_zero]
      exact C.radius_pos.le)
    rw [iteratedDeriv_eq_iterate] at h
    exact h.trans_lt (neg_neg_of_pos C.curvature_pos)
  refine ⟨{
    period_ge := by have hK:=D.K_ge;have hL:=D.L_ge;omega
    d := 2
    atoms := D.u
    atoms_injective := D.u_injective
    atoms_grid := D.grid
    atoms_lt_pi := fun i=>(D.interior i).2
    reps := D.reps
    reps_pos := D.reps_pos
    reps_lt := D.reps_lt
    reps_injective := D.reps_injective
    lags := pinLags K L
    lags_nonzero := pinLags_nonzero D.K_ge D.L_ge
    classes := ?_
    primal := D.primal
    primal_pos := D.primal_pos
    primal_sum := D.primal_sum
    dual := pinWeight K D.a D.b ε
    dual_pos := fun n _=>pinWeight_positive K hε hεa hεb n
    dual_sum := pinWeight_normalized D.K_ge D.L_ge D.normalized
    tight := D.tight
    inactive := D.inactive_strict
    minimizer_strict := D.minimizer_strict
    rank := by simpa using D.matrix_rank
    dual_strict := ?_
    support_curvature := fun i=>hcurv (D.u i) (by fin_cases i <;> simp [zeros])
    endpoint_curvature := ?_
    pinning_pos := fun i=>pinningPolynomial_positive hε hεa hεb (D.interior i)
    class_pair := ?_
    pinning_det := ?_
  }, rfl, rfl⟩
  · intro n hn
    right
    rcases pinLags_classes D.K_ge D.L_ge hn with h|h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
  · intro x hx0 hxpi hx
    exact C.strict ⟨hx0.le,hxpi⟩ (by
      simp only [zeros, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ne_of_gt hx0,hx 0,hx 1⟩)
  · have h := hcurv 0 (by simp [zeros])
    rw [finiteSymbol_second_zero] at h
    linarith
  · intro i
    apply pinLags_class_pairs D.K_ge D.L_ge
    fin_cases i <;> simp [reps]
  · have heq : (fun i r : Fin 2=>Real.sin ((D.reps r : ℝ)*(D.u i : ℝ)-Geometry.shiftedCurve q s (D.u i)))=
        (fun i r : Fin 2=>Real.sin (((![1,-(K : ℤ)] : Fin 2→ℤ) r : ℝ)*(D.u i : ℝ)-Geometry.shiftedCurve q s (D.u i))) := by
      funext i r
      exact D.sin_reps i r
    rw [heq]
    exact D.determinant

include D in
theorem regular : RegularPoint q s L := by
  obtain ⟨R,_,_⟩ := D.exists_regularData
  exact ⟨R⟩

end polyak.ModeLocking.TwoLag.ExactData
