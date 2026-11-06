import nesterov.IQC.KYP.Coercivity

/-!
The certificate-determined finite scalar matrix and all-Hilbert Lyapunov theorem.
All choices are made before the spatial Hilbert space or objective is selected.
-/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators

structure LyapunovData (A : StationaryMethod) (μ L t : ℝ) (M : ℕ)
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t) where
  matrix : Bilinear (Fin (A.memory+M)→ℝ)
  eta : ℝ
  eta_pos : 0<eta
  symmetric : ∀ x y,matrix x y=matrix y x
  dissipation : ∀ (x : Fin (A.memory+M)→ℝ) (d : ℝ),
    matrix (registerStep x d) (registerStep x d)-matrix x x+
      instantaneous (ofKernel (A.polynomialKernel cert)) x d≤
        -eta*((∑ j,‖x j‖^2)+‖d‖^2)

namespace LyapunovData
variable {A : StationaryMethod} {μ L t : ℝ} {M : ℕ}
variable {cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t}

def dissipationConstant (D : LyapunovData A μ L t M cert) : ℝ:=D.eta*Real.exp (-2*(A.memory+M:ℕ)*|t|)
def lowerConstant (D : LyapunovData A μ L t M cert) : ℝ:=D.dissipationConstant/Real.exp (2*t)
def upperConstant (D : LyapunovData A μ L t M cert) : ℝ:=A.lyapunovUpper cert D.matrix

theorem dissipationConstant_pos (D : LyapunovData A μ L t M cert) : 0<D.dissipationConstant:=
  mul_pos D.eta_pos (Real.exp_pos _)
theorem lowerConstant_pos (D : LyapunovData A μ L t M cert) : 0<D.lowerConstant:=
  div_pos D.dissipationConstant_pos (Real.exp_pos _)
theorem upperConstant_pos (D : LyapunovData A μ L t M cert) : 0<D.upperConstant:=
  A.lyapunovUpper_pos cert D.matrix

/-- The same scalar matrix gives the source-form Lyapunov function on any
real Hilbert space and every genuine normalized stationary execution. -/
theorem comparison (D : LyapunovData A μ L t M cert) (hμ : 0<μ) (hμL : μ<L)
    (hr : middleRadius A μ L<Real.exp t) (hM : ∀ n∈cert.lags,n≤M)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ) (w : ℕ→E)
    (hw : ∀ k,(∑ j : Fin (A.memory+1),A.normalizedCoeff μ L j • w (k+j))=
      gradient ψ (A.query w k)) (k : ℕ) :
    D.lowerConstant*windowEnergy (A.memory+M) w k≤A.lyapunov cert D.matrix ψ w k ∧
      A.lyapunov cert D.matrix ψ w k≤D.upperConstant*windowEnergy (A.memory+M) w k :=
  A.lyapunov_comparison hμ hμL hr cert hM D.matrix D.eta D.eta_pos D.dissipation hψ w hw k

theorem step (D : LyapunovData A μ L t M cert) (hM : ∀ n∈cert.lags,n≤M)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ) (w : ℕ→E)
    (hw : ∀ k,(∑ j : Fin (A.memory+1),A.normalizedCoeff μ L j • w (k+j))=
      gradient ψ (A.query w k)) (k : ℕ) :
    A.lyapunov cert D.matrix ψ w (k+1)≤Real.exp (2*t)*A.lyapunov cert D.matrix ψ w k-
      D.dissipationConstant*windowEnergy (A.memory+M) w k :=
  A.lyapunov_dissipation cert hM D.matrix D.eta D.eta_pos.le D.dissipation hψ w hw k

end LyapunovData

/-- Existence of the scalar storage data from the actual finite certificate. -/
theorem lyapunovData_nonempty {A : StationaryMethod} {μ L t : ℝ} {M : ℕ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t)
    (hM : ∀ n∈cert.lags,n≤M) : Nonempty (LyapunovData A μ L t M cert) := by
  obtain ⟨W,η,hη,hs,hd⟩:=A.exists_polynomial_storage cert hM
  exact ⟨⟨W,η,hη,hs,hd⟩⟩

/-- One certificate-determined scalar choice, independent of H, f and trajectory. -/
def certificateLyapunovData {A : StationaryMethod} {μ L t : ℝ} {M : ℕ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t)
    (hM : ∀ n∈cert.lags,n≤M) : LyapunovData A μ L t M cert:=
  Classical.choice (lyapunovData_nonempty cert hM)

end
end nesterov.IQC.KYP
