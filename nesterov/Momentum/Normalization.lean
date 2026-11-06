import nesterov.Momentum.Execution
import polyak.Functions.Normalization
import polyak.Functions.Transforms

/-!
Article: accelerated-scaling normalization L=1 in §2.
Use: original objectives and actual executions are transported by the exact
positive objective/step scaling, with no change to β, τ or the horizon.
-/
namespace nesterov.Momentum
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem normalized_objective {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.SmoothStronglyConvex μ L f) :
    polyak.SmoothStronglyConvex (μ/L) 1 (fun x => f x/L) := by
  have hL : 0<L := hf.mu_pos.trans hf.mu_lt_L
  have hs := hf.mul_pos (inv_pos.mpr hL)
  convert hs using 1 <;> simp [div_eq_mul_inv,ne_of_gt hL,mul_comm]

theorem gradient_normalized {f : E → ℝ} (hf : Differentiable ℝ f) (L : ℝ) (x : E) :
    gradient (fun y => f y/L) x = (1/L) • gradient f x := by
  have hg := polyak.hasGradientAt_quadratic_add (hf x).hasGradientAt 0 (1/L)
  simpa [div_eq_mul_inv,mul_comm] using hg.gradient

theorem step_normalized {f : E → ℝ} (hf : Differentiable ℝ f)
    {L : ℝ} (hL : L≠0) (β τ h : ℝ) (p : E×E) :
    step (gradient (fun x => f x/L)) β τ (h*L) p=step (gradient f) β τ h p := by
  simp only [step,gradient_normalized hf L,smul_smul]
  have he : h*L*(1/L)=h := by field_simp
  rw [he]

theorem state_normalized {f : E → ℝ} (hf : Differentiable ℝ f)
    {L : ℝ} (hL : L≠0) (β τ h : ℝ) (a b : E) (n : ℕ) :
    state (gradient (fun x => f x/L)) β τ (h*L) a b n=
      state (gradient f) β τ h a b n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [state,state,ih,step_normalized hf hL]

theorem iterate_normalized {f : E → ℝ} (hf : Differentiable ℝ f)
    {L : ℝ} (hL : L≠0) (β τ h : ℝ) (x₀ : E) (n : ℕ) :
    iterate (gradient (fun x => f x/L)) β τ (h*L) x₀ n=
      iterate (gradient f) β τ h x₀ n := by
  exact congrArg Prod.snd (state_normalized hf hL β τ h x₀ x₀ n)

end
end nesterov.Momentum
