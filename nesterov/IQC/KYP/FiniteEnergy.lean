import nesterov.IQC.KYP.SourceCoordinates

/-! Dimension-uniform comparison of the source and latent finite Hilbert states. -/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators
variable {I : Type*} [Fintype I]
variable {E : Type*} [NormedAddCommGroup E]

def finiteEnergy (x : I→E) : ℝ:=∑ i,‖x i‖^2

theorem finiteEnergy_nonneg (x : I→E) : 0≤finiteEnergy x:=
  Finset.sum_nonneg (fun _ _=>sq_nonneg _)

theorem norm_sq_le_finiteEnergy (x : I→E) : ‖x‖^2≤finiteEnergy x := by
  have hn : ‖x‖≤Real.sqrt (finiteEnergy x) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (finiteEnergy_nonneg x)]
    exact Finset.single_le_sum (fun j _=>sq_nonneg ‖x j‖) (Finset.mem_univ i)
  have hh:=(sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hn
  rwa [Real.sq_sqrt (finiteEnergy_nonneg x)] at hh

theorem finiteEnergy_le_card_norm_sq (x : I→E) :
    finiteEnergy x≤Fintype.card I*‖x‖^2 := by
  unfold finiteEnergy
  calc
    _≤∑ _i : I,‖x‖^2:=by
      apply Finset.sum_le_sum
      intro i _
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_le_pi_norm x i)
    _=_:=by simp

variable [InnerProductSpace ℝ E]

theorem source_energy_le (M : ℕ) (p₀ p₁ p₂ : ℝ) (w : Fin (M+2)→E) :
    finiteEnergy (sourceCoordinates M p₀ p₁ p₂ w)≤
      ((M+2:ℕ):ℝ)*(1+|p₀|+|p₁|+|p₂|)^2*finiteEnergy w := by
  have hf:=sourceCoordinates_forward_uniform_bound M p₀ p₁ p₂ w
  have hF : 0≤1+|p₀|+|p₁|+|p₂|:=by positivity
  have hs:=(sq_le_sq₀ (norm_nonneg _) (mul_nonneg hF (norm_nonneg _))).mpr hf
  rw [mul_pow] at hs
  have h1:=finiteEnergy_le_card_norm_sq (sourceCoordinates M p₀ p₁ p₂ w)
  simp only [Fintype.card_fin] at h1
  have h2:=mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (M+2): (0:ℝ)≤((M+2:ℕ):ℝ))
  have h3:=mul_le_mul_of_nonneg_left (norm_sq_le_finiteEnergy w)
    (mul_nonneg (Nat.cast_nonneg (M+2): (0:ℝ)≤((M+2:ℕ):ℝ)) (sq_nonneg (1+|p₀|+|p₁|+|p₂|)))
  nlinarith

theorem latent_energy_le (M : ℕ) (p₀ p₁ p₂ : ℝ) (hp₂ : p₂≠0) (w : Fin (M+2)→E) :
    finiteEnergy w≤((M+2:ℕ):ℝ)*(sourceInverseBound M p₀ p₁ p₂ hp₂)^2*
      finiteEnergy (sourceCoordinates M p₀ p₁ p₂ w) := by
  have hi : 0<sourceInverseBound M p₀ p₁ p₂ hp₂:=scalarActionBound_pos _
  have hf:=sourceCoordinates_inverse_uniform_bound M p₀ p₁ p₂ hp₂ w
  have hs:=(sq_le_sq₀ (norm_nonneg _) (mul_nonneg hi.le (norm_nonneg _))).mpr hf
  rw [mul_pow] at hs
  have h1:=finiteEnergy_le_card_norm_sq w
  simp only [Fintype.card_fin] at h1
  have h2:=mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (M+2): (0:ℝ)≤((M+2:ℕ):ℝ))
  have h3:=mul_le_mul_of_nonneg_left
    (norm_sq_le_finiteEnergy (sourceCoordinates M p₀ p₁ p₂ w))
    (mul_nonneg (Nat.cast_nonneg (M+2): (0:ℝ)≤((M+2:ℕ):ℝ)) (sq_nonneg (sourceInverseBound M p₀ p₁ p₂ hp₂)))
  nlinarith

end
end nesterov.IQC.KYP
