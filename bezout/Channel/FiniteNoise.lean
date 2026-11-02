import bezout.Channel.FiniteNoiseState

/-!
Article: bezout, Appendix D, exact finite-noise multilinearity.
Use: constructs every vector coefficient from the actual chronological physical
prediction operators, for arbitrary time-dependent perturbation directions.
Proof: the noncommutative subset product expansion and selected-coordinate
multilinearity factor out one scalar amplitude for each selected oracle call.
-/

namespace bezout.Channel
noncomputable section
open Polynomial chebyshev1
open scoped BigOperators
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The unperturbed physical prediction operators. -/
def nominalStages (h : bezout.History N) (H : E →ₗ[ℝ] E) : ℕ → Module.End ℝ (PredictionSpace N E) :=
  predictionStageNat h (fun _ => H)

/-- A perturbation insertion occurs only at its own physical call. -/
def channelInsertions (h : bezout.History N) (P : Fin N → E →ₗ[ℝ] E) (k : ℕ) :
    Module.End ℝ (PredictionSpace N E) :=
  if hk : k<N then predictionInsertion h ⟨k,hk⟩ (P ⟨k,hk⟩) else 0

/-- One physical perturbed stage is affine in precisely its own scalar amplitude. -/
theorem predictionStageNat_affine (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (a : ℕ → ℝ) (k : ℕ) :
    predictionStageNat h (fun s => H+a s.val • P s) k=
      nominalStages h H k+a k • channelInsertions h P k := by
  by_cases hk : k<N
  · apply LinearMap.ext
    intro v
    funext i
    simp only [predictionStageNat, nominalStages, channelInsertions, hk, dite_true,
      predictionStage_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Pi.add_apply, Pi.smul_apply, predictionInsertion]
    change v i-h.predictionCoefficient i ⟨k,hk⟩ •
      (H (v (some ⟨k,hk⟩))+a k • P ⟨k,hk⟩ (v (some ⟨k,hk⟩)))=
      v i-h.predictionCoefficient i ⟨k,hk⟩ • H (v (some ⟨k,hk⟩))+
        a k • (-(h.predictionCoefficient i ⟨k,hk⟩ • P ⟨k,hk⟩ (v (some ⟨k,hk⟩))))
    module
  · simp [predictionStageNat, nominalStages, channelInsertions, hk]

/-- Actual physical channel output at independently specified call amplitudes. -/
def finiteNoiseOutput (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) (a : ℕ → ℝ) : E :=
  h.oracleOutput initial (fun s v => H v+a s.val • P s v)

/-- The vector coefficient for a selected finite set of physical perturbation calls.
Use: all coefficients are constructed from the history and fixed operators,
independently of noise size or random signs. -/
def finiteNoiseCoefficient (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) (S : Finset ℕ) : E :=
  insertionTerm (nominalStages h H) (channelInsertions h P) N S (fun _ => initial) none

/-- Independently scaling selected insertion directions factors out their scalar product. -/
theorem insertionTerm_variable_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C D : ℕ → Module.End ℝ V) (a : ℕ → ℝ) (n : ℕ) (S : Finset ℕ)
    (hS : S⊆Finset.range n) :
    insertionTerm C (fun k => a k • D k) n S=
      (∏ k ∈ S, a k) • insertionTerm C D n S := by
  rw [← insertionMultilinear_apply (K := ℝ) C (fun k => a k • D k) n S hS,
    ← insertionMultilinear_apply (K := ℝ) C D n S hS]
  simpa only [Finset.prod_coe_sort] using
    (insertionMultilinear (K := ℝ) C n S hS).map_smul_univ (fun k => a k.val) (fun k => D k.val)

/-- Exact physical multilinear expansion for arbitrary scalar amplitudes.
Use: applies to the full finite noisy execution, with no small-noise truncation. -/
theorem finiteNoise_expansion (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) (a : ℕ → ℝ) :
    finiteNoiseOutput h H P initial a=
      ∑ S ∈ (Finset.range N).powerset, (∏ s ∈ S, a s) • finiteNoiseCoefficient h H P initial S := by
  have he : predictionStageNat h (fun s => H+a s.val • P s)=
      fun k => nominalStages h H k+a k • channelInsertions h P k :=
    funext (predictionStageNat_affine h H P a)
  have ho := predictionPrefix_output h (fun s => H+a s.val • P s) initial
  change _=finiteNoiseOutput h H P initial a at ho
  rw [← ho, predictionPrefix, he, orderedProduct_add_expansion]
  simp only [LinearMap.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro S hS
  rw [insertionTerm_variable_smul _ _ a N S (Finset.mem_powerset.mp hS)]
  rfl

/-- The zero-degree coefficient is the actual noiseless terminal. -/
theorem finiteNoiseCoefficient_empty (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) :
    finiteNoiseCoefficient h H P initial ∅=(aeval H h.terminal) initial := by
  simp only [finiteNoiseCoefficient, insertionTerm_empty]
  change predictionPrefix h (fun _ => H) initial N none=_
  rw [predictionPrefix_output]
  have he : (fun (_s : Fin N) (v : E) => H v)=(fun _ v => H v+(0:E)) := by simp
  rw [he, h.oracleOutput_linear, h.nominal_output]

/-- Common noise size and one independent sign per call give the displayed finite expansion. -/
theorem finiteNoise_sign_expansion (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) (δ : ℝ) (ξ : ℕ → ℝ) :
    finiteNoiseOutput h H P initial (fun s => δ*ξ s)=
      ∑ S ∈ (Finset.range N).powerset,
        (δ^S.card * ∏ s ∈ S, ξ s) • finiteNoiseCoefficient h H P initial S := by
  rw [finiteNoise_expansion]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib, Finset.prod_const]

end
end bezout.Channel
