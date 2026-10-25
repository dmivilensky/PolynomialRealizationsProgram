import polyak.General.IQC.SequenceSpace
import polyak.Functions.Normalization

/-! Appendix D: the actual rescaled gradient is a causal nonexpansive map
on every finite prefix, and τψ stays in the normalized class. -/
noncomputable section
namespace polyak.General.IQC
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def scaledGradient (ψ : E → ℝ) (t : ℝ) (x : ℕ → E) (k : ℕ) : E :=
  Real.exp (-((k:ℝ)*t)) • gradient ψ (Real.exp ((k:ℝ)*t) • x k)

theorem scaledGradient_causal (ψ : E → ℝ) (t : ℝ) : Causal (scaledGradient ψ t) := by
  intro N x y hxy k hk
  simp only [scaledGradient,hxy k hk]

theorem scaledGradient_zero {ψ : E → ℝ} (hψ : NormalizedSmooth ψ) (t : ℝ) :
    scaledGradient ψ t 0=0 := by
  funext k
  simp [scaledGradient,hψ.gradient_zero]

theorem exp_cancel (a : ℝ) : Real.exp (-a)*Real.exp a=1 := by
  rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]

theorem scaledGradient_norm_sub {ψ : E → ℝ} (hψ : NormalizedSmooth ψ) (t : ℝ)
    (x y : ℕ → E) (k : ℕ) :
    ‖scaledGradient ψ t x k-scaledGradient ψ t y k‖≤‖x k-y k‖ := by
  have hh:=hψ.grad_lipschitz.dist_le_mul
    (Real.exp ((k:ℝ)*t) • x k) (Real.exp ((k:ℝ)*t) • y k)
  simp only [dist_eq_norm,NNReal.coe_one,one_mul] at hh
  calc
    _=Real.exp (-((k:ℝ)*t))*
      ‖gradient ψ (Real.exp ((k:ℝ)*t) • x k)-gradient ψ (Real.exp ((k:ℝ)*t) • y k)‖:=by
        rw [scaledGradient,scaledGradient,←smul_sub,norm_smul,Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
    _≤Real.exp (-((k:ℝ)*t))*‖Real.exp ((k:ℝ)*t) • x k-Real.exp ((k:ℝ)*t) • y k‖:=
      mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    _=‖x k-y k‖:=by
      rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
        ←mul_assoc,exp_cancel,one_mul]

theorem scaledGradient_nonexpansive {ψ : E → ℝ} (hψ : NormalizedSmooth ψ) (t : ℝ)
    (x y : ℕ → E) (N : ℕ) :
    prefixNorm (scaledGradient ψ t x-scaledGradient ψ t y) N≤prefixNorm (x-y) N := by
  apply (sq_le_sq₀ (prefixNorm_nonneg _ _) (prefixNorm_nonneg _ _)).mp
  rw [prefixNorm_sq,prefixNorm_sq]
  apply Finset.sum_le_sum
  intro k _
  exact pow_le_pow_left₀ (norm_nonneg _) (scaledGradient_norm_sub hψ t x y k) 2

theorem normalizedSmooth_homotopy {ψ : E → ℝ} (hψ : NormalizedSmooth ψ)
    {τ : ℝ} (hτ : τ∈Set.Icc (0 : ℝ) 1) : NormalizedSmooth (fun x => τ*ψ x) := by
  have hg (x : E) : HasGradientAt (fun y => τ*ψ y) (τ • gradient ψ x) x:=by
    simpa using hasGradientAt_quadratic_add (hψ.differentiable x).hasGradientAt 0 τ
  refine ⟨fun x => (hg x).differentiableAt,?_,by simp [hψ.value_zero],?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [(hg x).gradient,(hg y).gradient]
    simp only [dist_eq_norm,NNReal.coe_one,one_mul,←smul_sub,norm_smul,
      Real.norm_eq_abs,abs_of_nonneg hτ.1]
    have hh:=hψ.grad_lipschitz.dist_le_mul x y
    simp only [dist_eq_norm,NNReal.coe_one,one_mul] at hh
    exact (mul_le_mul_of_nonneg_left hh hτ.1).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hτ.2 (norm_nonneg (x-y)))
  · rw [(hg 0).gradient,hψ.gradient_zero,smul_zero]

theorem scaledGradient_homotopy {ψ : E → ℝ} (hψ : NormalizedSmooth ψ)
    (t τ : ℝ) (x : ℕ → E) :
    scaledGradient (fun y => τ*ψ y) t x=τ • scaledGradient ψ t x := by
  have hg (x : E) : HasGradientAt (fun y => τ*ψ y) (τ • gradient ψ x) x:=by
    simpa using hasGradientAt_quadratic_add (hψ.differentiable x).hasGradientAt 0 τ
  funext k
  simp only [scaledGradient,(hg _).gradient,Pi.smul_apply]
  exact smul_comm _ _ _

end polyak.General.IQC
