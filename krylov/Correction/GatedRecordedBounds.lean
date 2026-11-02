import krylov.Correction.ObservedSpectralScaling
import krylov.Correction.GatedExecution
import krylov.Methods.CanonicalWindows

/-!
Article: main_krylov, thm:UCq and thm:UCg, actual uniform gated-RFC recording.
Use: Derive genuine physical correction and secant bounds from the measured
spectral test, without any minimum individual step or reference energy.
Source: original measured RFC execution, true canonical metric covariance,
the proved observed spectral-gate conditioning and coefficient noncancellation.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine uniform spectral-gate correction constant is nonnegative, including the zero horizon.
Use: Supply the actual finite uniform spectral-gated RFC induction.
Article: main_krylov, thm:UCq and thm:UCg, genuine uniform recording.
Proof: Use the true nonnegative square roots and their totalized reciprocals.
-/
theorem gatedCorrectionConstant_nonneg (N : ℕ) (γ : ℝ) :
    0≤gatedCorrectionConstant N γ := by
  unfold gatedCorrectionConstant
  positivity

/-- The genuine spectral-gate correction constant increases with the finite horizon.
Use: Supply the actual finite uniform spectral-gated RFC induction.
Article: main_krylov, thm:UCq and thm:UCg, genuine uniform recording.
Proof: Both nonnegative dimension factors increase; the common reciprocal square-root factor is nonnegative.
-/
theorem gatedCorrectionConstant_mono {N M : ℕ} (hNM : N≤M) (γ : ℝ) :
    gatedCorrectionConstant N γ≤gatedCorrectionConstant M γ := by
  unfold gatedCorrectionConstant
  have h : (N : ℝ)≤M := by exact_mod_cast hNM
  gcongr

/-- The actual spectral-gated phase has a uniform correction-to-recorded-step bound from its genuine observed pairs, including both fallback branches.
Use: Supply the actual finite uniform spectral-gated RFC induction.
Article: main_krylov, thm:UCq and thm:UCg, genuine uniform recording.
Proof: The accepted spectral test gives positive actual pair energies and the measured normalized spectrum. The proved noncancellation bound controls the real correction, while both skipped branches have zero movement.
-/
theorem gatedArrayPhase_recorded_bound {p N : ℕ} (S Y : Fin p → E) (g d : E)
    (A B : E →L[ℝ] E) {γ η : ℝ} (hγ : 0<γ) (hη : 0≤η)
    (hsize : p+1≤N) (hhalf : η≤1/2) (hsmall : (N : ℝ)*η≤γ/4)
    (hηsize : (N : ℝ)*η≤1) (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤η)
    (hy : ∀ j, ‖Y j-S j‖≤η*‖S j‖) :
    ‖(gatedArrayPhase γ S Y g d (A d) B).movement‖≤gatedCorrectionConstant N γ*
      ‖lineLength g d (A d) • d+(gatedArrayPhase γ S Y g d (A d) B).movement‖ := by
  classical
  by_cases hgate : matrixSpectralGate γ (pairModel (Fin.cons d S) (Fin.cons (A d) Y))
  · obtain ⟨he,hherm,heigen⟩ := hgate
    have henergy (j : Fin (p+1)) :
        0 < inner ℝ ((Fin.cons d S : Fin (p+1) → E) j) ((Fin.cons (A d) Y : Fin (p+1) → E) j) := by
      simpa only [pairModel,max_self,min_self] using he j
    have heigen' : ∀ j, γ≤(observedPairModel_hermitian (Fin.cons d S) (Fin.cons (A d) Y)).eigenvalues j := by
      simpa only [diagonalNormalizedModel,observedPairModel,pairModel,max_self,min_self] using heigen
    have hdiff (j : Fin (p+1)) : ‖(Fin.cons (A d) Y : Fin (p+1) → E) j-
        (Fin.cons d S : Fin (p+1) → E) j‖≤η*‖(Fin.cons d S : Fin (p+1) → E) j‖ := by
      refine Fin.cases ?_ (fun j => hy j) j
      simpa only [Fin.cons_zero,_root_.sub_apply,ContinuousLinearMap.id_apply] using
        ((A-ContinuousLinearMap.id ℝ E).le_opNorm d).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg d))
    have hpN : ((p+1 : ℕ) : ℝ)≤N := by exact_mod_cast hsize
    have hco := observed_gate_correction_recorded (Fin.cons d S) (Fin.cons (A d) Y)
      (searchedGradient g d (A d)) (lineLength g d (A d)) henergy hγ hη hhalf
      ((mul_le_mul_of_nonneg_right hpN hη).trans hsmall)
      ((mul_le_mul_of_nonneg_right hpN hη).trans hηsize) hdiff heigen'
      (searchedGradient_inner_zero g d (A d) (by simpa only [Fin.cons_zero] using (henergy 0).ne'))
    unfold gatedArrayPhase
    rw [ite_eq_left ⟨he,hherm,heigen⟩]
    unfold rfcArrayPhase
    split
    · change ‖combine _ (modelCoefficients _ _ _) + 0‖≤_ * ‖_ + (combine _ (modelCoefficients _ _ _) + 0)‖
      simp only [add_zero]
      exact hco.trans (mul_le_mul_of_nonneg_right (gatedCorrectionConstant_mono hsize γ) (norm_nonneg _))
    · simp only
      simpa only [norm_zero,add_zero] using mul_nonneg (gatedCorrectionConstant_nonneg N γ) (norm_nonneg (lineLength g d (A d) • d))
  · unfold gatedArrayPhase
    rw [ite_eq_right hgate]
    simpa only [norm_zero,add_zero] using mul_nonneg (gatedCorrectionConstant_nonneg N γ) (norm_nonneg (lineLength g d (A d) • d))

end
end krylov.Correction
