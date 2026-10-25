import polyak.General.IQC.SequenceSpace
import polyak.General.IQC.Apriori

/-! Appendix D, Lemma homotopy: the bounded two-channel IQC gives an
a priori estimate, and finite causal continuation establishes actual ℓ²
stability. All constants are explicit coefficient bounds. -/
noncomputable section
namespace polyak.General.IQC
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Feedback
variable (F : Feedback E) (B : BilinearIQC (SequenceSpace E))
variable {M ε : ℝ} (hM : ‖B‖≤M) (hε : 0<ε)
variable (hneg : ∀ z : SequenceSpace E,iqcValue B (F.plantL2 z) z≤ -ε*‖z‖^2)
variable (hpos : ∀ τ : ℝ,τ∈Icc (0 : ℝ) 1 → ∀ x : SequenceSpace E,
  0≤ iqcValue B x (τ • F.deltaL2 x))
include B hM hε hneg hpos

theorem iqc_apriori (τ : ℝ) (hτ : τ∈Icc (0 : ℝ) 1) :
    F.Apriori (aprioriConstant M F.gain ε) τ := by
  intro f hf hx
  have h:=uniform_apriori_bound B F.plantL2 hM F.plantL2_norm_le hε hneg
    (toL2 (F.run τ f) hx) (τ • F.deltaL2 (toL2 (F.run τ f) hx)) (toL2 f hf)
    (F.run_toL2_equation τ f hf hx) (hpos τ hτ _)
  simpa only [toL2_norm] using h

theorem iqc_uniform_bound {τ : ℝ} (hτ : τ∈Icc (0 : ℝ) 1)
    (f : ℕ → E) (hf : SquareSummable f) :
    SquareSummable (F.run τ f) ∧
      sequenceNorm (F.run τ f)≤aprioriConstant M F.gain ε*sequenceNorm f :=
  F.uniform_bound_of_apriori
    (aprioriConstant_pos ((norm_nonneg B).trans hM) F.gain_nonneg hε)
    (fun τ hτ => F.iqc_apriori B hM hε hneg hpos τ hτ) hτ f hf

end Feedback
end polyak.General.IQC
