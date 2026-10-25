import polyak.General.IQC.ZeroExtension
import polyak.General.IQC.CertificateBilinear
import polyak.General.IQC.CertificateGraph
import polyak.General.IQC.Nonlinearity

/-! Pull the actual bounded Hermitian certificate back isometrically to
the causal space used in the homotopy theorem.  Positivity is inherited
from real interpolation on the whole-line zero extension. -/

namespace polyak.General.IQC
noncomputable section
open Duality Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : C(Frequency,ℂ)} {t : ℝ}

def zeroExtendChannels : SequenceSpace E×SequenceSpace E →L[ℝ] ZSpace E×ZSpace E :=
  (zeroExtendCLM (E:=E)).prodMap zeroExtendCLM

theorem zeroExtendChannels_norm (u : SequenceSpace E×SequenceSpace E) :
    ‖zeroExtendChannels u‖=‖u‖ := by
  change max ‖zeroExtendCLM u.1‖ ‖zeroExtendCLM u.2‖=max ‖u.1‖ ‖u.2‖
  rw [zeroExtendCLM_norm,zeroExtendCLM_norm]

def halfLineCertificate (cert : StrictCertificate m t) : BilinearIQC (SequenceSpace E) :=
  (certificateForm cert).bilinearComp zeroExtendChannels zeroExtendChannels

@[simp] theorem halfLineCertificate_apply (cert : StrictCertificate m t)
    (u v : SequenceSpace E×SequenceSpace E) :
    halfLineCertificate cert u v=certificateForm cert (zeroExtendChannels u) (zeroExtendChannels v) := rfl

theorem halfLineCertificate_symmetric (cert : StrictCertificate m t)
    (u v : SequenceSpace E×SequenceSpace E) :
    halfLineCertificate cert u v=halfLineCertificate cert v u :=
  certificateForm_symmetric cert _ _

local instance halfLineDualNormedSpace : NormedSpace ℝ ((SequenceSpace E×SequenceSpace E) →L[ℝ] ℝ) := inferInstance
local instance halfLineDualSeminormedGroup : SeminormedAddCommGroup ((SequenceSpace E×SequenceSpace E) →L[ℝ] ℝ) := inferInstance
local instance pullbackZDualNormedSpace : NormedSpace ℝ ((ZSpace E×ZSpace E) →L[ℝ] ℝ) := inferInstance
local instance pullbackZDualSeminormedGroup : SeminormedAddCommGroup ((ZSpace E×ZSpace E) →L[ℝ] ℝ) := inferInstance

theorem halfLineCertificate_norm_le (cert : StrictCertificate m t) :
    ‖halfLineCertificate (E:=E) cert‖ ≤ ‖certificateForm (E:=E) cert‖ := by
  apply (halfLineCertificate (E:=E) cert).opNorm_le_bound₂ (norm_nonneg (certificateForm (E:=E) cert))
  intro u v
  change ‖certificateForm cert (zeroExtendChannels u) (zeroExtendChannels v)‖ ≤ _
  calc
    _ ≤ ‖certificateForm (E:=E) cert‖*‖zeroExtendChannels u‖*‖zeroExtendChannels v‖ :=
      ((certificateForm cert (zeroExtendChannels u)).le_opNorm (zeroExtendChannels v)).trans
        (mul_le_mul_of_nonneg_right ((certificateForm cert).le_opNorm (zeroExtendChannels u)) (norm_nonneg _))
    _ = _ := by rw [zeroExtendChannels_norm,zeroExtendChannels_norm]

variable [CompleteSpace E]

theorem scaledGradient_squareSummable {ψ : E → ℝ} (hψ : NormalizedSmooth ψ)
    (t : ℝ) {x : ℕ → E} (hx : SquareSummable x) : SquareSummable (scaledGradient ψ t x) := by
  apply hx.of_nonneg_of_le (fun _ => sq_nonneg _)
  intro n
  have h := scaledGradient_norm_sub hψ t x 0 n
  rw [scaledGradient_zero hψ t] at h
  simp only [Pi.zero_apply,sub_zero] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

def halfGradientL2 {ψ : E → ℝ} (hψ : NormalizedSmooth ψ) (t : ℝ)
    (x : SequenceSpace E) : SequenceSpace E :=
  toL2 (scaledGradient ψ t x) (scaledGradient_squareSummable hψ t (lp_squareSummable x))

@[simp] theorem halfGradientL2_apply {ψ : E → ℝ} (hψ : NormalizedSmooth ψ)
    (t : ℝ) (x : SequenceSpace E) (n : ℕ) :
    halfGradientL2 hψ t x n=scaledGradient ψ t x n := rfl

theorem zeroExtend_scaledGradient {ψ : E → ℝ} (hψ : NormalizedSmooth ψ)
    (t : ℝ) (x : ℕ → E) (k : ℤ) :
    zeroExtend (scaledGradient ψ t x) k=zScaledGradient ψ t (zeroExtend x) k := by
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk
    simp [zeroExtend_nat,scaledGradient,zScaledGradient,zUnscale]
  · rw [zeroExtend_neg _ (lt_of_not_ge hk)]
    simp [zScaledGradient,zUnscale,zeroExtend, hk,hψ.gradient_zero]

theorem halfLineCertificate_nonneg {ψ : E → ℝ} (hψ : NormalizedSmooth ψ)
    (cert : StrictCertificate m t) (x : SequenceSpace E) :
    0 ≤ iqcValue (halfLineCertificate cert) x (halfGradientL2 hψ t x) := by
  change 0 ≤ certificateForm cert
    (zeroExtendL2 x,zeroExtendL2 (halfGradientL2 hψ t x))
    (zeroExtendL2 x,zeroExtendL2 (halfGradientL2 hψ t x))
  rw [certificateForm_eq_tsum]
  have hσ : (fun k => zeroExtendL2 (halfGradientL2 hψ t x) k)=
      zScaledGradient ψ t (fun k => zeroExtendL2 x k) := by
    funext k
    exact zeroExtend_scaledGradient hψ t (fun n => x n) k
  simpa only [hσ] using normalizedSmooth_IQC cert hψ (zlp_squareSummable (zeroExtendL2 x))

theorem halfGradientL2_homotopy {ψ : E → ℝ} (hψ : NormalizedSmooth ψ)
    (cert : StrictCertificate m t) {tau : ℝ} (htau : tau∈Set.Icc (0:ℝ) 1)
    (x : SequenceSpace E) :
    0 ≤ iqcValue (halfLineCertificate cert) x (tau • halfGradientL2 hψ t x) := by
  have hscaled := normalizedSmooth_homotopy hψ htau
  have he : halfGradientL2 hscaled t x=tau • halfGradientL2 hψ t x := by
    apply Subtype.ext
    exact scaledGradient_homotopy hψ t tau x
  rw [← he]
  exact halfLineCertificate_nonneg hscaled cert x

end
end polyak.General.IQC
