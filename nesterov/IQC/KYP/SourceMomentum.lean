import nesterov.IQC.KYP.SourceCoordinates
import nesterov.Momentum.Stationary

/-! The exact momentum source state and the fixed discount diagonal. -/

namespace nesterov.IQC.KYP
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def momentumSourceEquiv (M : ℕ) (μ L β τ h : ℝ) (hh : h ≠ 0) (hμL : μ < L) :
    (Fin (M + 2) → E) ≃L[ℝ] (Fin (M + 2) → E) := by
  let A := Momentum.method β τ h hh
  have hp : A.normalizedCoeff μ L (2 : Fin 3) ≠ 0 := A.normalizedCoeff_top_ne hμL
  exact sourceCoordinatesEquiv M (A.normalizedCoeff μ L 0)
    (A.normalizedCoeff μ L 1) (A.normalizedCoeff μ L 2) hp

theorem momentum_sourceCoordinates_actual {μ L β τ h : ℝ} (hh : h ≠ 0)
    {f : E → ℝ} (hf : Differentiable ℝ f) {w : ℕ → E}
    (hw : (Momentum.method β τ h hh).IsTrajectory (gradient f) w) (M k : ℕ) :
    sourceCoordinates M ((Momentum.method β τ h hh).normalizedCoeff μ L 0)
      ((Momentum.method β τ h hh).normalizedCoeff μ L 1)
      ((Momentum.method β τ h hh).normalizedCoeff μ L 2) (window (M + 2) w k) =
      fun i : Fin (M + 2) => if i.val = 0 then w k else if i.val = 1 then w (k + 1) else
        gradient (polyak.normalizeFunction μ L f)
          ((Momentum.method β τ h hh).query w (k + (i.val - 2))) := by
  refine sourceCoordinates_window M _ _ _ w
    (fun n => gradient (polyak.normalizeFunction μ L f) ((Momentum.method β τ h hh).query w n)) ?_ k
  intro n
  have he := hw.normalized (Momentum.method β τ h hh) (μ := μ) (L := L) hf n
  change (∑ j : Fin 3, (Momentum.method β τ h hh).normalizedCoeff μ L j • w (n + j.val)) =
    gradient (polyak.normalizeFunction μ L f) ((Momentum.method β τ h hh).query w n) at he
  rw [Fin.sum_univ_three] at he
  convert he using 1
  norm_num
  congr 2

/-- The time-independent diagonal taking an actual latent window to the
discounted window after removing its common exp(-kt) factor. -/
def discountWindow {N : ℕ} (t : ℝ) (x : Fin N → E) : Fin N → E :=
  fun i => Real.exp (-(i : ℝ) * t) • x i

def discountWindowCLM (N : ℕ) (t : ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun i => Real.exp (-(i : ℝ) * t) • ContinuousLinearMap.proj i

omit [CompleteSpace E] in
theorem discounted_window (N : ℕ) (t : ℝ) (w : ℕ → E) (k : ℕ) :
    window N (fun j => Real.exp (-(j : ℝ) * t) • w j) k =
      Real.exp (-(k : ℝ) * t) • discountWindow t (window N w k) := by
  funext i
  dsimp [window, discountWindow]
  rw [smul_smul, ← Real.exp_add]
  congr 2
  push_cast
  ring

omit [CompleteSpace E] in
theorem scalarAction_discount_comp {N : ℕ} (t : ℝ)
    (A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (X : Fin N → E) :
    scalarAction ((discountWindowCLM N t).comp A) X = discountWindow t (scalarAction A X) := by
  funext i
  dsimp [scalarAction, discountWindowCLM, discountWindow]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    mul_smul, Finset.smul_sum]

omit [CompleteSpace E] in
/-- The exact fixed scalar quadratic matrix in the source state, including
the discount diagonal required by the article's r² Lyapunov convention. -/
theorem source_tensor_discount_window (M : ℕ) (t p₀ p₁ p₂ : ℝ) (hp₂ : p₂ ≠ 0)
    (W : Bilinear (Fin (M + 2) → ℝ)) (w : Fin (M + 2) → E) :
    tensorForm W (discountWindow t w) (discountWindow t w) =
      tensorForm (W.bilinearComp
        ((discountWindowCLM (M + 2) t).comp
          (sourceCoordinatesEquiv (E := ℝ) M p₀ p₁ p₂ hp₂).symm.toContinuousLinearMap)
        ((discountWindowCLM (M + 2) t).comp
          (sourceCoordinatesEquiv (E := ℝ) M p₀ p₁ p₂ hp₂).symm.toContinuousLinearMap))
        (sourceCoordinates M p₀ p₁ p₂ w) (sourceCoordinates M p₀ p₁ p₂ w) := by
  rw [tensorForm_scalarAction, scalarAction_discount_comp,
    ← sourceCoordinatesEquiv_symm_scalarAction,
    ← sourceCoordinatesEquiv_apply M p₀ p₁ p₂ hp₂ w,
    ContinuousLinearEquiv.symm_apply_apply]

end
end nesterov.IQC.KYP
