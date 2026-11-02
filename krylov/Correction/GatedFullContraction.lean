import krylov.Correction.FullReconstruction
import krylov.Methods.ProjectedRecording
import krylov.Correction.ObservedSpectralScaling
import krylov.Stability.WeightedCGFlags

/-!
Article: main_krylov, thm:UCq and thm:UCg, actual recorded/full-window estimates.
Use: Close genuine finite-cycle angle and terminal-gradient bounds without
replacing observed columns by hypothetical reference vectors.
Source: proved weighted normalization, actual model residual identities,
true spectral Gram conditioning and the original full Euclidean reconstruction.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A genuine full Euclidean family with a positive Gram lower endpoint controls the norm of every actual vector by its true projected residual.
Use: Complete the actual uniform gated-RFC finite-cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, real recorded and full-window bounds.
Proof: The actual Gram determinant forces the true square column determinant nonzero. Construct its genuine synthesis coefficients, use the proved coefficient lower-Gram bound and actual coordinate pairing, then cancel the nonzero vector norm after separating zero.
-/
theorem full_projectedResidual_lower (u : Fin n → EuclideanSpace ℝ (Fin n)) {a : ℝ}
    (ha : 0<a) (hgram : ∀ i, a≤(crossGram_isHermitian u).eigenvalues i)
    (g : EuclideanSpace ℝ (Fin n)) :
    ‖g‖≤(Real.sqrt a)⁻¹*‖projectedResidual u g‖ := by
  let T := fullBasisMatrix u
  have hG := (inverse_bound_of_eigenvalues (crossGram u u) (crossGram_isHermitian u) ha hgram).1
  have hT : IsUnit T.det := by
    have he : Tᵀ*T=crossGram u u := transpose_mul_columnGram T
    rw [← he,Matrix.det_mul,Matrix.det_transpose] at hG
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have ht := isUnit_iff_ne_zero.mp hG
    rw [hz,mul_zero] at ht
    exact ht rfl
  let c := WithLp.ofLp (Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ g)
  have hsyn : combine u c=g := by
    have he : combine u c=Matrix.toEuclideanCLM (𝕜 := ℝ) T (WithLp.toLp 2 c) := by
      ext i
      simp only [combine,WithLp.ofLp_sum,WithLp.ofLp_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Matrix.ofLp_toEuclideanCLM,Matrix.mulVec,dotProduct]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [he]
    change Matrix.toEuclideanCLM (𝕜 := ℝ) T (Matrix.toEuclideanCLM (𝕜 := ℝ) T⁻¹ g)=g
    rw [← mul_apply_eq_comp,← map_mul,Matrix.mul_nonsing_inv _ hT,map_one,one_apply_eq_self]
  have hc := combine_coefficients_bound u c ha hgram
  rw [hsyn] at hc
  have hi := real_inner_le_norm (WithLp.toLp 2 c) (projectedResidual u g)
  have he : inner ℝ (WithLp.toLp 2 c) (projectedResidual u g)=‖g‖^2 := by
    rw [← combine_inner_coordinates,hsyn,real_inner_self_eq_norm_sq]
  rw [he] at hi
  have hm := mul_le_mul_of_nonneg_right hc (norm_nonneg (projectedResidual u g))
  by_cases hg : g=0
  · rw [hg,norm_zero]
    positivity
  · have hpos := norm_pos_iff.mpr hg
    nlinarith

/-- A genuine full measured model correction contracts the actual gradient by the real operator-and-secant budget with a dimension-and-gate constant.
Use: Complete the actual uniform gated-RFC finite-cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, real recorded and full-window bounds.
Proof: The original measured spectral test and actual pair errors derive both true normalized model and full Gram lower endpoints. The real corrected projected residual is the actual model mismatch times the actual inverse solve. Bound its true incoming coordinates and reconstruct the actual full output using the proved full Gram domain.
-/
theorem full_observed_gate_correction_contraction (s y : Fin n → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : ∀ i, 0 < inner ℝ (s i) (y i)) {γ ε η : ℝ} (hγ : 0<γ) (hε : 0≤ε) (hη : 0≤η)
    (hhalf : η≤1/2) (hsmall : (n : ℝ)*η≤γ/4)
    (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖)
    (hgate : ∀ i, γ≤(observedPairModel_hermitian s y).eigenvalues i)
    (hB : ‖B-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) :
    ‖g+B (combine s (modelCoefficients s (pairModel s y) g))‖≤
      ((Real.sqrt (γ/4))⁻¹*(n : ℝ)*(γ/2)⁻¹*Real.sqrt n)*(ε+η)*‖g‖ := by
  have hs := positive_pair_steps_ne s y he
  have hgram := observed_gate_unit_gram_lower s y he hγ.le hη hhalf hsmall hy hgate
  have hlo : ∀ i, γ/2≤(rescale_pairModel_isHermitian s y (fun j => ‖s j‖⁻¹)).eigenvalues i := by
    intro i
    have h := observed_gate_unit_model_lower s y he hγ.le hy hgate i
    nlinarith [mul_le_mul_of_nonneg_left hhalf hγ.le]
  obtain ⟨hu,hinv⟩ := inverse_bound_of_eigenvalues _ (rescale_pairModel_isHermitian s y _)
    (by positivity : 0<γ/2) hlo
  have hρ : ‖projectedResidual (unitWindow s) g‖≤Real.sqrt n*‖g‖ := by
    apply coordinate_norm_le_sqrt_card _ (norm_nonneg g)
    intro i
    have h := norm_inner_le_norm (𝕜 := ℝ) (unitWindow s i) g
    simpa only [coordinates,Real.norm_eq_abs,unitWindow_norm s hs i,one_mul] using h
  have hres := normalizedCorrection_bound s (pairModel s y) (fun i => ‖s i‖⁻¹)
    (unitWindow_diagonal_unit s hs) hu B g
  change ‖projectedResidual (unitWindow s) (g+B (combine s (modelCoefficients s (pairModel s y) g)))‖≤
    ‖correctionCompression (unitWindow s) B-rescaleModel (pairModel s y) (fun i => ‖s i‖⁻¹)‖*
    ‖(rescaleModel (pairModel s y) (fun i => ‖s i‖⁻¹))⁻¹‖*‖projectedResidual (unitWindow s) g‖ at hres
  have hmodel := normalized_pairModel_error_bound s y hs B hε hη hB hy
  have hres' : ‖projectedResidual (unitWindow s) (g+B (combine s (modelCoefficients s (pairModel s y) g)))‖≤
      (n : ℝ)*(ε+η)*(γ/2)⁻¹*(Real.sqrt n*‖g‖) := by
    apply hres.trans
    gcongr
  have hout := full_projectedResidual_lower (unitWindow s) (by positivity : 0<γ/4) hgram
    (g+B (combine s (modelCoefficients s (pairModel s y) g)))
  exact (hout.trans (mul_le_mul_of_nonneg_left hres' (by positivity))).trans_eq (by ring)

end
end krylov.Correction
