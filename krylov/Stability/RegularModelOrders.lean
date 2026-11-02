import krylov.Stability.AnalyticCorrection
import krylov.Stability.AnalyticMatrix
import krylov.Methods.ProjectedCorrectionOrder
import krylov.Secant.CorrectionOrder

/-!
Article: main_krylov, lem:projected-residual, discharged local orders at genuine model references.
Use: derive incoming residual, normalized error and inverse estimates from
actual analytic data and genuine quadratic model identities at the reference.
Source: the existing spectral matrix asymptotic calculus and actual finite
model-query estimates; all normalization denominators are proved locally nonzero.
-/

namespace krylov.Stability
noncomputable section
open Matrix Filter Asymptotics krylov.Methods krylov.LinearAlgebra
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {p : ℕ}

/-- The genuine finite coefficient vector of a regular actual model correction has first order when its real reference projection vanishes.
Use: discharge the source's w_k=O(ω) statement for actual finite observed coefficient solves.
Article: main_krylov, lem:projected-residual, first correction coefficients.
Proof: the actual inverse-model coefficient entries are analytic and all
vanish by the genuine zero reference projection; differentiability of the finite coefficient vector gives the order. -/
theorem regular_model_coefficients_order (s : X → Fin p → E) (H : X → Matrix (Fin p) (Fin p) ℝ)
    (g : X → E) (hs : ∀ i, AnalyticAt ℝ (fun z => s z i) 0)
    (hH : ∀ i j, AnalyticAt ℝ (fun z => H z i j) 0) (hg : AnalyticAt ℝ g 0)
    (hu : (H 0).det≠0) (hρ : coordinates (s 0) (g 0)=0) :
    (fun z => modelCoefficients (s z) (H z) (g z)) =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
  have ha : AnalyticAt ℝ (fun z => modelCoefficients (s z) (H z) (g z)) 0 :=
    AnalyticAt.pi (analytic_modelCoefficients s H g 0 hs hH hg hu)
  have hz := modelCoefficients_zero (s 0) (H 0) (g 0) hρ
  simpa only [hz,sub_zero] using ha.differentiableAt.isBigO_sub.norm_right

/-- Genuine analytic model data with zero reference residual give a first-order actual physical correction.
Use: discharge the physical-movement order in the source's actual recorded-pair quadratic defect.
Article: main_krylov, lem:projected-residual, χ=O(ω).
Proof: the actual model correction is analytic on its genuine inverse domain;
its real reference coefficient vector vanishes, so differentiability gives the stated order. -/
theorem regular_model_movement_order (s : X → Fin p → E) (H : X → Matrix (Fin p) (Fin p) ℝ)
    (g : X → E) (hs : ∀ i, AnalyticAt ℝ (fun z => s z i) 0)
    (hH : ∀ i j, AnalyticAt ℝ (fun z => H z i j) 0) (hg : AnalyticAt ℝ g 0)
    (hu : (H 0).det≠0) (hρ : coordinates (s 0) (g 0)=0) :
    (fun z => combine (s z) (modelCoefficients (s z) (H z) (g z))) =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
  have ha := analytic_modelCorrection s H g 0 hs hH hg hu
  have hz : combine (s 0) (modelCoefficients (s 0) (H 0) (g 0))=0 := by
    rw [modelCoefficients_zero _ _ _ hρ]
    simp only [combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero]
  simpa only [hz,sub_zero] using ha.differentiableAt.isBigO_sub.norm_right

/-- All fixed finite repeated actual model corrections have the printed normalized projected-residual order, with every local order and inverse premise discharged.
Use: the incoming actual projection has first order and every real model correction raises its order once.
Article: main_krylov, lem:projected-residual, O(ω^(c+1)) near a genuine nondegenerate reference.
Proof: analytic actual data give first-order raw model error and incoming
projection. Genuine nonzero columns make the real diagonal normalizer locally
bounded. The real normalized model has a genuine nonsingular reference and
therefore a locally bounded inverse. The actual finite-query bound then proves
the claimed order without an assumed residual expansion or inverse estimate. -/
theorem regular_repeated_model_projected_order (s : X → Fin p → E)
    (H : X → Matrix (Fin p) (Fin p) ℝ) (B : X → E →L[ℝ] E) (g : X → E) (c : ℕ)
    (hs : ∀ i, AnalyticAt ℝ (fun z => s z i) 0)
    (hH : ∀ i j, AnalyticAt ℝ (fun z => H z i j) 0) (hB : AnalyticAt ℝ B 0)
    (hg : AnalyticAt ℝ g 0) (hn : ∀ i, s 0 i≠0) (hu : (H 0).det≠0)
    (hmodel : correctionCompression (s 0) (B 0)=H 0) (hρ : coordinates (s 0) (g 0)=0) :
    (fun z => projectedResidual (unitWindow (s z))
      (runCorrections (repeatedModelTree (s z) (H z) c (g z)) (B z) (g z)).gradient) =O[𝓝 (0 : X)]
        (fun z => ‖z‖^(c+1)) := by
  -- All normalizers, inverse bounds and incoming orders are derived here from the actual reference data.
  let d := fun z i => ‖s z i‖⁻¹
  let D := fun z => diagonal (d z)
  let Hn := fun z => rescaleModel (H z) (d z)
  let N := fun z => correctionCompression (s z) (B z)-H z
  have hN : AnalyticAt ℝ N 0 := analytic_spectral_matrix N 0 fun i j =>
    (analytic_inner (hs i) (analytic_operator_apply hB (hs j))).sub (hH i j)
  have hN0 : N 0=0 := by dsimp only [N]; rw [hmodel,sub_self]
  have hNo : N =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
    simpa only [hN0,sub_zero] using hN.differentiableAt.isBigO_sub.norm_right
  have hd : ContinuousAt (fun z => d z) (0 : X) := continuousAt_pi.mpr fun i =>
    (hs i).continuousAt.norm.inv₀ (norm_ne_zero_iff.mpr (hn i))
  have hD : ContinuousAt D (0 : X) :=
    (continuous_id : Continuous (fun v : Fin p → ℝ => v)).matrix_diagonal.continuousAt.comp hd
  have hDo : D =O[𝓝 (0 : X)] (fun _ => (1 : ℝ)) := hD.tendsto.isBigO_one ℝ
  have hHn : ContinuousAt Hn (0 : X) := (hD.mul (analytic_spectral_matrix H 0 hH).continuousAt).mul hD
  have hdu := unitWindow_diagonal_unit (s 0) hn
  have hHu : IsUnit (H 0).det := isUnit_iff_ne_zero.mpr hu
  have hHnu : IsUnit (Hn 0).det := by
    simp only [Hn,rescaleModel,det_mul]
    exact (hdu.mul hHu).mul hdu
  have hinv : ContinuousAt (fun z => (Hn z)⁻¹) (0 : X) :=
    (continuousAt_matrix_inv (Hn 0) (by
      rw [show (Ring.inverse : ℝ → ℝ)=Inv.inv from funext Ring.inverse_eq_inv]
      exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp hHnu))).comp hHn
  have hi : (fun z => (Hn z)⁻¹) =O[𝓝 (0 : X)] (fun _ => (1 : ℝ)) := hinv.tendsto.isBigO_one ℝ
  have hdet : ContinuousAt (fun z => (Hn z).det) (0 : X) :=
    continuous_id.matrix_det.continuousAt.comp hHn
  have hunit : ∀ᶠ z in 𝓝 (0 : X), IsUnit (Hn z).det :=
    (hdet.eventually_ne (isUnit_iff_ne_zero.mp hHnu)).mono fun _ hz => isUnit_iff_ne_zero.mpr hz
  have hsn : ∀ᶠ z in 𝓝 (0 : X), ∀ i, s z i≠0 :=
    Filter.eventually_all.mpr fun i => (hs i).continuousAt.eventually_ne (hn i)
  have hNn : (fun z => correctionCompression (unitWindow (s z)) (B z)-Hn z) =O[𝓝 (0 : X)]
      (fun z => ‖z‖) := by
    have ht := matrix_mul_bigO D (fun z => N z*D z) (fun _ => (1 : ℝ)) (fun z => ‖z‖) hDo
      (by simpa only [mul_one] using matrix_mul_bigO N D (fun z => ‖z‖) (fun _ => (1 : ℝ)) hNo hDo)
    apply (ht.congr_right (fun z => one_mul ‖z‖)).congr_left
    intro z
    change D z*(N z*D z)=correctionCompression (rescaleWindow (s z) (d z)) (B z)-rescaleModel (H z) (d z)
    rw [correctionCompression_rescale]
    dsimp only [rescaleModel,D,N]
    noncomm_ring
  have hρa := analytic_projectedResidual s g 0 hs hg
  have hρ0 : projectedResidual (s 0) (g 0)=0 := congrArg (WithLp.toLp 2) hρ
  have hρo : (fun z => projectedResidual (s z) (g z)) =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
    simpa only [hρ0,sub_zero] using hρa.differentiableAt.isBigO_sub.norm_right
  have hρn : (fun z => projectedResidual (unitWindow (s z)) (g z)) =O[𝓝 (0 : X)] (fun z => ‖z‖^1) := by
    have ht := operator_action_order (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (D z))
      (fun z => projectedResidual (s z) (g z)) (fun _ => (1 : ℝ)) (fun z => ‖z‖)
      (krylov.Secant.matrix_bigO_toEuclideanCLM D _ hDo) hρo
    simpa only [unitWindow,projectedResidual_rescale,one_mul,pow_one,D,d] using ht
  simpa only [Nat.add_comm 1 c] using repeatedModel_projected_order s H B g (fun z => ‖z‖) 1 c hsn hunit hNn hi hρn

end
end krylov.Stability
