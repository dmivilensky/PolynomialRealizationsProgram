import polyak.General.IQC.CertificateBilinear
import polyak.General.IQC.CertificateGraph
import polyak.General.IQC.KernelL2
import polyak.Energy.Circle
import polyak.Energy.Symbol

/-! Article: lem:iqc. The source certificate acts on the actual nonlinear
gradient graph and on the actual recurrence-filtered linear graph. -/
noncomputable section
namespace polyak.General.IQC
open polyak Energy Duality Spectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : C(Frequency,ℂ)} {t : ℝ}

theorem certificateForm_nonneg [CompleteSpace E] (cert : StrictCertificate m t)
    {ψ : E → ℝ} (hψ : NormalizedSmooth ψ) (x σ : ZSpace E)
    (hσ : ∀ k,σ k=zScaledGradient ψ t x k) :
    0≤certificateForm cert (x,σ) (x,σ) := by
  rw [certificateForm_eq_tsum]
  have he : (fun k => σ k)=zScaledGradient ψ t x := funext hσ
  exact (congrArg (fun s : ℤ → E => 0≤∑' k,zCertificateQuadratic cert (fun j => x j) s k) he).mpr
    (normalizedSmooth_IQC cert hψ (zlp_squareSummable x))

theorem zCertificateQuadratic_gradientFilter (A B β t : ℝ)
    (cert : StrictCertificate m t) (x : ℤ → E) (k : ℤ) :
    zCertificateQuadratic cert x (filterEval (gradientFilter A B β t) x) k=
      kernelEval (certificateKernel A B β t cert) x k :=
  (kernelEval_certificate A B β t cert x k).symm

theorem certificateForm_kernel (A B β t : ℝ) (cert : StrictCertificate m t)
    (x σ : ZSpace E) (hσ : ∀ k,σ k=filterEval (gradientFilter A B β t) x k) :
    certificateForm cert (x,σ) (x,σ)=kernelBilinear (certificateKernel A B β t cert) x x := by
  rw [certificateForm_eq_tsum,kernelBilinear_eq_tsum]
  apply tsum_congr
  intro k
  have he : (fun k => σ k)=filterEval (gradientFilter A B β t) x := funext hσ
  exact (congrArg (fun s : ℤ → E => zCertificateQuadratic cert (fun j => x j) s k) he).trans
    (zCertificateQuadratic_gradientFilter A B β t cert x k)

theorem certificateForm_strict_graph (A B β t : ℝ) (hB : B≠0)
    (cert : StrictCertificate (Waves.multiplierMap A B β t) t)
    (x σ : ZSpace E) (hσ : ∀ k,σ k=filterEval (gradientFilter A B β t) x k) :
    certificateForm cert (x,σ) (x,σ)≤ -cert.ε*‖x‖^2 := by
  rw [certificateForm_kernel A B β t cert x σ hσ]
  apply kernelBilinear_le
  exact certificateKernel_symbol_le A B β t hB cert

end polyak.General.IQC
