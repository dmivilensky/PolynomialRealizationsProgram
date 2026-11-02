import krylov.Correction.ObservedGateAcceptance

/-!
Article: main_krylov, thm:UCg(iii), actual arbitrary-threshold comparison.
Use: Preserve the ordinary nonstagnation constant while shrinking only the
actual source radius for a requested measured spectral-gate threshold.
Source: true Hermitian Rayleigh conditioning, actual column-normalized
model algebra and the genuine full observed correction executor.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Stability krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {p : ℕ}

/-- Every actual matrix diagonal deviation from one is bounded by its genuine spectral distance to the identity.
Use: Transfer the real uniform ordinary-RFC conclusions to the original gated method.
Article: main_krylov, thm:UCg(iii).
Proof: Test the true operator deviation on the corresponding standard Euclidean unit vector and apply Cauchy--Schwarz.
-/
theorem matrix_diagonal_spectral_deviation (M : Matrix (Fin p) (Fin p) ℝ) (i : Fin p) :
    |M i i-1|≤‖M-1‖ := by
  let v : EuclideanSpace ℝ (Fin p) := PiLp.single 2 i 1
  have hv : ‖v‖=1 := by simp only [v,PiLp.norm_single,norm_one]
  have he : inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (M-1) v)=M i i-1 := by
    simp [v,EuclideanSpace.inner_single_left,Matrix.ofLp_toEuclideanCLM,Matrix.mulVec,dotProduct,PiLp.single_apply]
  have hi := norm_inner_le_norm (𝕜 := ℝ) v (Matrix.toEuclideanCLM (𝕜 := ℝ) (M-1) v)
  rw [Real.norm_eq_abs,he,hv,one_mul] at hi
  exact hi.trans (by simpa only [hv,mul_one,Matrix.l2_opNorm_toEuclideanCLM] using (Matrix.toEuclideanCLM (𝕜 := ℝ) (M-1)).le_opNorm v)

/-- A genuine Hermitian model close to the identity passes the actual measured spectral test under the precise scalar threshold margin.
Use: Transfer the real uniform ordinary-RFC conclusions to the original gated method.
Article: main_krylov, thm:UCg(iii).
Proof: Real diagonal energies lie between one minus and one plus the spectral allowance. The genuine Rayleigh perturbation gives the model lower endpoint; its actual inverse-square-root diagonal congruence transfers that endpoint with the exact reciprocal factor.
-/
theorem near_identity_matrix_spectral_gate (M : Matrix (Fin p) (Fin p) ℝ) (hM : M.IsHermitian)
    {δ γ : ℝ} (hδ : 0≤δ) (hδ1 : δ<1)
    (hnear : ‖M-1‖≤δ) (hmargin : δ+γ*δ≤1-γ) : matrixSpectralGate γ M := by
  have hdiag i := (matrix_diagonal_spectral_deviation M i).trans hnear
  have he i : 0<M i i := by have ht := (abs_le.mp (hdiag i)).1; linarith
  have hu i : M i i≤1+δ := by have ht := (abs_le.mp (hdiag i)).2; linarith
  have hbase : ∀ i, (1 : ℝ)≤(Matrix.isHermitian_one : (1 : Matrix (Fin p) (Fin p) ℝ).IsHermitian).eigenvalues i := by
    apply spectral_lower_of_form
    intro v
    simp only [one_mul,map_one,one_apply_eq_self,real_inner_self_eq_norm_sq,le_refl]
  have hlo := spectral_lower_perturbation 1 M Matrix.isHermitian_one hM hbase hnear
  let q : Fin p → ℝ := fun i => (Real.sqrt (M i i))⁻¹
  have hq i : (1+δ)⁻¹≤(q i)^2 := by
    dsimp only [q]
    rw [inv_pow,Real.sq_sqrt (he i).le]
    exact (inv_le_inv₀ (by positivity : 0<1+δ) (he i)).mpr (hu i)
  have hg : (diagonal q*M*diagonal q).IsHermitian := by
    have ht := Matrix.isHermitian_conjTranspose_mul_mul (diagonal q) hM
    have hdiag : (diagonal q).IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      by_cases hij : i=j <;> simp [Matrix.diagonal,hij,eq_comm]
    simpa only [hdiag.eq] using ht
  have hs := diagonal_congruence_spectral_lower M hM q hg (by linarith : 0≤1-δ) hlo hq
  have hγbound : γ≤(1-δ)*(1+δ)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0<1+δ)).mpr
    nlinarith only [hmargin]
  refine ⟨he,?_,?_⟩
  · exact hg
  · intro i
    exact hγbound.trans (hs i)


/-- A positive common radius upgrades a fixed model-error coefficient to every real spectral threshold below one.
Use: Transfer the real uniform ordinary-RFC conclusions to the original gated method.
Article: main_krylov, thm:UCg(iii).
Proof: Choose an explicit positive reciprocal radius from the actual threshold gap and model coefficient. Multiplying its scalar inequality proves the real diagonal and spectral margins.
-/
theorem uniform_model_gate_radius {C γ : ℝ} (hC : 0≤C) (hγ : 0<γ) (hγ1 : γ<1) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, 0≤ε → ε≤δ → C*ε<1 ∧ C*ε+γ*(C*ε)≤1-γ := by
  let D := 2*(1+γ)*(C+1)
  have hD : 0<D := by dsimp only [D]; positivity
  refine ⟨(1-γ)/D,div_pos (by linarith) hD,?_⟩
  intro ε hε he
  have hbound : ε*D≤1-γ := (le_div_iff₀ hD).mp he
  have hcoef : (1+γ)*C≤D := by dsimp only [D]; nlinarith [mul_nonneg hγ.le hC]
  have hm : C*ε+γ*(C*ε)≤1-γ := by
    have ht := mul_le_mul_of_nonneg_right hcoef hε
    nlinarith only [ht,hbound]
  have hgδ := mul_nonneg hγ.le (mul_nonneg hC hε)
  exact ⟨by linarith,hm⟩

end
end krylov.Correction
