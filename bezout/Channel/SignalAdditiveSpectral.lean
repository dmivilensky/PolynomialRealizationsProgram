import bezout.Channel.SignalAdditive
import bezout.History.Transport

/-!
Article: bezout, Appendix D, the exact fixed-Hessian additive-energy gain.
Use: discharges the orthonormal-coordinate assumption for every actual finite
real self-adjoint Hessian, with no prescribed basis or distinct-eigenvalue hypothesis.
Proof: the actual finite-dimensional spectral theorem intertwines the physical
response maps; its isometry transports energies and attaining error profiles.
-/

namespace bezout.Channel
noncomputable section
open Polynomial
open scoped BigOperators
variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual terminal deviation in the genuine orthonormal eigenbasis. -/
theorem additive_physical_spectral_coordinates (h : bezout.History N)
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (initial : E) (noise : Fin N → E) :
    (hH.eigenvectorBasis rfl).repr
      ((h.run H initial noise).output-(aeval H h.terminal) initial)=
      (h.run (bezout.History.matrixEnd (Matrix.diagonal (hH.eigenvalues rfl)))
        ((hH.eigenvectorBasis rfl).repr initial)
        (fun s => (hH.eigenvectorBasis rfl).repr (noise s))).output-
        (aeval (bezout.History.matrixEnd (Matrix.diagonal (hH.eigenvalues rfl))) h.terminal)
          ((hH.eigenvectorBasis rfl).repr initial) := by
  rw [h.physical_response,add_sub_cancel_left,h.physical_response,add_sub_cancel_left,map_sum]
  ext i
  simp only [WithLp.ofLp_sum,Finset.sum_apply,bezout.Analysis.polynomial_spectral_coordinates,
    diagonal_polynomial_apply]

variable [Nontrivial E]

/-- The true maximal squared response-row norm over the spectrum of a self-adjoint Hessian. -/
def spectralAdditiveEnergyMax (h : bezout.History N) (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) : ℝ :=
  let _ : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0,Module.finrank_pos⟩⟩
  additiveEnergyMax h (hH.eigenvalues rfl)

/-- Its maximum is attained at an actual spectral value, and controls all spectral values. -/
theorem spectralAdditiveEnergyMax_spectrum (h : bezout.History N)
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) :
    (∃ lam∈spectrum ℝ H, spectralAdditiveEnergyMax h H hH=
      bezout.Probability.varianceProfile h lam) ∧
    (∀ lam∈spectrum ℝ H, bezout.Probability.varianceProfile h lam≤
      spectralAdditiveEnergyMax h H hH) := by
  let _ : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0,Module.finrank_pos⟩⟩
  constructor
  · obtain ⟨j,hj⟩ := additiveEnergyMax_attained h (hH.eigenvalues rfl)
    exact ⟨_,Module.End.hasEigenvalue_iff_mem_spectrum.mp (hH.hasEigenvalue_eigenvalues rfl j),hj⟩
  · intro lam hlam
    obtain ⟨j,hj⟩ := hH.exists_eigenvalues_eq rfl
      (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hlam)
    rw [← hj]
    exact responseEnergy_le_max h (hH.eigenvalues rfl) j

/-- Every finite self-adjoint physical Hessian has exactly the maximal spectral
response-row gain, attained by an actual physical error sequence. -/
theorem additive_physical_sharp_selfAdjoint (h : bezout.History N)
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (initial : E) :
    (∀ noise : Fin N → E, (∑ s, ‖noise s‖^2)≤1 →
      ‖(h.run H initial noise).output-(aeval H h.terminal) initial‖≤
        Real.sqrt (spectralAdditiveEnergyMax h H hH)) ∧
    ∃ noise : Fin N → E, (∑ s, ‖noise s‖^2)≤1 ∧
      ‖(h.run H initial noise).output-(aeval H h.terminal) initial‖=
        Real.sqrt (spectralAdditiveEnergyMax h H hH) := by
  let _ : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0,Module.finrank_pos⟩⟩
  let B := (hH.eigenvectorBasis rfl).repr
  have hn (noise : Fin N → E) :
      ‖(h.run H initial noise).output-(aeval H h.terminal) initial‖=
      ‖(h.run (bezout.History.matrixEnd (Matrix.diagonal (hH.eigenvalues rfl)))
        (B initial) (fun s => B (noise s))).output-
        (aeval (bezout.History.matrixEnd (Matrix.diagonal (hH.eigenvalues rfl))) h.terminal) (B initial)‖ := by
    rw [← B.norm_map]
    exact congrArg norm (additive_physical_spectral_coordinates h H hH initial noise)
  have hd := additive_physical_sharp h (hH.eigenvalues rfl) (B initial)
  constructor
  · intro noise hnoise
    rw [hn]
    apply hd.1
    simpa only [B.norm_map] using hnoise
  · obtain ⟨noise,henergy,he⟩ := hd.2
    refine ⟨fun s => B.symm (noise s),?_,?_⟩
    · simpa only [B.symm.norm_map] using henergy
    · rw [hn]
      have hnoise : (fun s => B (B.symm (noise s)))=noise := by
        funext s
        exact B.apply_symm_apply (noise s)
      rw [hnoise]
      exact he

end
end bezout.Channel
