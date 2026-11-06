import nesterov.IQC.KYP.UniformStorage
import nesterov.IQC.KYP.PolynomialSupport

/-! The fixed scalar KYP storage applied to actual complete latent windows. -/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators
open polyak.General.IQC polyak.Energy

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def window (N : ℕ) (w : ℕ→E) (k : ℕ) : Fin N→E:=fun j=>w (k+j.val)

/-- A supported natural kernel sees exactly the current finite window. -/
theorem kernel_window_eval {N : ℕ} {K : NatKernel} (hK : K.Supported N) (w : ℕ→E) (k : ℕ) :
    instantaneous K (window N w k) (w (k+N))=NatKernel.eval K w k := by
  have hh:=instantaneous_head hK (window (N+1) w k)
  change instantaneous K (window N w k) (w (k+N))=
      NatKernel.eval K (fun n=>w (k+(boundedIndex N n).val)) 0 at hh
  rw [hh]
  unfold NatKernel.eval
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have hb:=hK p hp
  simp only [Nat.zero_add,boundedIndex,min_eq_left hb.1,min_eq_left hb.2]

/-- The one scalar storage inequality acts on every actual Hilbert window. -/
theorem tensor_window_dissipation {N : ℕ} {K : NatKernel} (hK : K.Supported N)
    (W : Bilinear (Fin N→ℝ)) (η : ℝ)
    (hW : ∀ (x : Fin N→ℝ) (d : ℝ),
      W (registerStep x d) (registerStep x d)-W x x+instantaneous K x d≤
        -η*((∑ j,‖x j‖^2)+‖d‖^2)) (w : ℕ→E) (k : ℕ) :
    tensorForm W (window N w (k+1)) (window N w (k+1))-
      tensorForm W (window N w k) (window N w k)+NatKernel.eval K w k≤
        -η*(∑ j : Fin (N+1),‖w (k+j.val)‖^2) := by
  have hh:=tensor_storage_dissipation hK W η hW (window (N+1) w k)
  have ht : tailOf (window (N+1) w k)=window N w (k+1) := by
    funext j
    dsimp [tailOf,window]
    congr 1
    omega
  have hd : headOf (window (N+1) w k)=window N w k:=rfl
  rw [ht,hd] at hh
  change tensorForm W (window N w (k+1)) (window N w (k+1))-
    tensorForm W (window N w k) (window N w k)+instantaneous K (window N w k) (w (k+N))≤_ at hh
  rw [kernel_window_eval hK] at hh
  exact hh

end Hilbert
end
end nesterov.IQC.KYP

namespace nesterov.StationaryMethod
noncomputable section
open scoped BigOperators
open nesterov.IQC nesterov.IQC.KYP polyak.General.IQC polyak.Energy
variable (A : StationaryMethod)

/-- The literal finite certificate kernel through both polynomial amplitudes. -/
def polynomialKernel {μ L t : ℝ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t) : Kernel:=
  twoFilterKernel (A.queryFilter t) (A.normalizedFilter μ L t) cert

theorem polynomialKernel_supported {μ L t : ℝ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t) {M : ℕ}
    (hM : ∀ n∈cert.lags,n≤M) : KernelSupported 0 (A.memory+M) (A.polynomialKernel cert) :=
  twoFilterKernel_supported cert
    (coefficientFilter_supported _ (by omega : A.memory≤A.memory+1))
    (coefficientFilter_supported _ le_rfl) hM

theorem polynomialKernel_strict {μ L t : ℝ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t) (θ : FrequencyCircle) :
    kernelSymbol (A.polynomialKernel cert) θ≤ -cert.ε := by
  apply kernelSymbol_le_of_halfCircle
  intro ω hω0 hωπ
  let c : nesterov.Spectral.Frequency:=⟨Real.cos ω,Real.neg_one_le_cos ω,Real.cos_le_one ω⟩
  have hc : Real.arccos c=ω:=Real.arccos_cos hω0 hωπ
  rw [←hc]
  rw [polynomialKernel,twoFilterKernel_symbol _ _ cert c
    (A.queryFilter_symbol μ L t c) (A.normalizedFilter_symbol μ L t c)]
  exact cert.strict c

/-- A finite real symmetric storage matrix is produced from every strict
certificate, with exactly D+M latent coordinates. It has one fixed set of
coefficients for every spatial Hilbert space by tensor_window_dissipation. -/
theorem exists_polynomial_storage {μ L t : ℝ}
    (cert : nesterov.Duality.StrictCertificate (A.symbolPair μ L t) t) {M : ℕ}
    (hM : ∀ n∈cert.lags,n≤M) :
    ∃ (W : Bilinear (Fin (A.memory+M)→ℝ)) (η : ℝ),0<η ∧
      (∀ x y,W x y=W y x) ∧ ∀ (x : Fin (A.memory+M)→ℝ) (d : ℝ),
        W (registerStep x d) (registerStep x d)-W x x+
          instantaneous (ofKernel (A.polynomialKernel cert)) x d≤
            -η*((∑ j,‖x j‖^2)+‖d‖^2) := by
  have hs:=A.polynomialKernel_supported cert hM
  apply exists_strict_storage (by have :=A.memory_pos; omega) (ofKernel_supported hs) cert.ε_pos
  intro θ
  rw [ofKernel_toKernel hs]
  exact A.polynomialKernel_strict cert θ

end
end nesterov.StationaryMethod
