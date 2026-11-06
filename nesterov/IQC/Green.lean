import nesterov.IQC.Companion
import polyak.General.IQC.FreePlant

/-!
Real Green coefficients for a stable arbitrary-order companion. The estimates
are scalar and therefore apply to trajectories in every real Hilbert space
with the same constants.
-/
namespace nesterov.IQC
noncomputable section
open scoped BigOperators
variable {d : ℕ}

/-- Real coordinate of the full complex companion Green matrix. -/
def green (a : Fin d→ℝ) (n : ℕ) (i j : Fin d) : ℝ :=
  ((companion d (fun j=>(a j:ℂ))^n) (Pi.single j 1) i).re

@[simp] theorem green_zero (a : Fin d→ℝ) (i j : Fin d) :
    green a 0 i j=if i=j then 1 else 0 := by
  by_cases h : i=j <;> simp [green,h]

/-- Exact recurrence for every Green coordinate, including the final row. -/
theorem green_succ (a : Fin d→ℝ) (n : ℕ) (i j : Fin d) :
    green a (n+1) i j=
      if hi : i.val+1<d then green a n ⟨i.val+1,hi⟩ j else ∑ k,a k*green a n k j := by
  by_cases hi : i.val+1<d
  · simp [green,pow_succ',mul_apply_eq_comp,companion_apply,hi]
  · simp [green,pow_succ',mul_apply_eq_comp,companion_apply,hi,Complex.mul_re]

theorem green_abs_le (a : Fin d→ℝ) (n : ℕ) (i j : Fin d) :
    |green a n i j|≤‖companion d (fun j=>(a j:ℂ))^n‖ := by
  have hv : ‖(Pi.single j (1:ℂ):Fin d→ℂ)‖≤1 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro k
    by_cases hk : k=j <;> simp [hk]
  calc
    _≤‖(companion d (fun j=>(a j:ℂ))^n) (Pi.single j 1) i‖:=Complex.abs_re_le_norm _
    _≤‖(companion d (fun j=>(a j:ℂ))^n) (Pi.single j 1)‖:=norm_le_pi_norm _ _
    _≤‖companion d (fun j=>(a j:ℂ))^n‖*‖(Pi.single j (1:ℂ):Fin d→ℂ)‖:=
      ContinuousLinearMap.le_opNorm _ _
    _≤_:=mul_le_of_le_one_right (norm_nonneg _) hv

theorem green_abs_summable (a : Fin d→ℝ)
    (hs : Summable (fun n : ℕ=>‖companion d (fun j=>(a j:ℂ))^n‖)) (i j : Fin d) :
    Summable (fun n : ℕ=>|green a n i j|) :=
  hs.of_nonneg_of_le (fun _=>abs_nonneg _) (fun n=>green_abs_le a n i j)

section Vector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Apply the scalar Green matrix to an arbitrary real spatial history. -/
def freeState (a : Fin d→ℝ) (initial : Fin d→E) (n : ℕ) (i : Fin d) : E :=
  ∑ j,green a n i j • initial j

@[simp] theorem freeState_zero (a : Fin d→ℝ) (initial : Fin d→E) (i : Fin d) :
    freeState a initial 0 i=initial i := by
  simp [freeState,green_zero]

/-- Genuine free-state evolution, with no spatial dimension in its coefficients. -/
theorem freeState_succ (a : Fin d→ℝ) (initial : Fin d→E) (n : ℕ) (i : Fin d) :
    freeState a initial (n+1) i=
      if hi : i.val+1<d then freeState a initial n ⟨i.val+1,hi⟩ else ∑ k,a k • freeState a initial n k := by
  unfold freeState
  simp_rw [green_succ]
  split
  · rfl
  · simp only [Finset.sum_smul,Finset.smul_sum,mul_smul]
    rw [Finset.sum_comm]

theorem freeState_norm (a : Fin d→ℝ) (initial : Fin d→E) (n : ℕ) (i : Fin d) :
    ‖freeState a initial n i‖≤
      ‖companion d (fun j=>(a j:ℂ))^n‖*(∑ j,‖initial j‖) := by
  calc
    _≤∑ j,‖green a n i j • initial j‖:=norm_sum_le _ _
    _=∑ j,|green a n i j| *‖initial j‖:=by simp only [norm_smul,Real.norm_eq_abs]
    _≤∑ j,‖companion d (fun j=>(a j:ℂ))^n‖*‖initial j‖:=by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (green_abs_le a n i j) (norm_nonneg _)
    _=_:=by rw [Finset.mul_sum]

end Vector
end
end nesterov.IQC
