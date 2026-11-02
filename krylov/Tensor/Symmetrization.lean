import krylov.Tensor.ProjectiveDuality
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
Article: main_krylov, thm:Hp, actual tensor symmetrization and nuclear duality.
Use: define the genuine finite permutation averages on tensors and continuous
multilinear forms. Their exact pairing identity and norm contraction reduce
symmetric tensor duality to the proved projective Hahn--Banach duality.
Source: Friedland--Lim (2018), symmetric spectral/nuclear norm duality;
mathlib's actual projective tensor space and isometric index permutations.
-/

namespace krylov.Tensor
noncomputable section
open scoped TensorProduct BigOperators
open ContinuousMultilinearMap
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual permutation average of a continuous multilinear form.
Article: main_krylov, thm:Hp. -/
def formSymmetrization (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : ι => E) ℝ :=
  (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ • ∑ σ : Equiv.Perm ι, domDomCongr σ f

/-- The actual permutation average of a projective tensor.
Article: main_krylov, thm:Hp. -/
def tensorSymmetrization (X : ⨂[ℝ] _ : ι, E) : ⨂[ℝ] _ : ι, E :=
  (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ •
    ∑ σ : Equiv.Perm ι, (PiTensorProduct.reindex ℝ (fun _ : ι => E) σ).symm X

/-- Permutation averaging is contractive for the true multilinear operator norm.
Article: main_krylov, thm:Hp.
Proof: every actual index permutation is isometric, and their normalized
finite sum has norm at most the average of their equal norms. -/
theorem norm_formSymmetrization_le (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) ℝ) :
    ‖formSymmetrization f‖ ≤ ‖f‖ := by
  have hcard : (0 : ℝ) < Fintype.card (Equiv.Perm ι) := by exact_mod_cast Fintype.card_pos
  rw [formSymmetrization, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hcard.le)]
  calc
    _ ≤ (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm ι, ‖domDomCongr σ f‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hcard.le)
    _ = ‖f‖ := by simp only [norm_domDomCongr, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]; rw [← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul]

/-- The tensor and form symmetrizers are genuinely adjoint under the actual pairing.
Article: main_krylov, thm:Hp.
Proof: commute the true linear lift with the finite average and use the exact
tensor index-reindexing universal property on every summand. -/
theorem lift_tensorSymmetrization (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) ℝ)
    (X : ⨂[ℝ] _ : ι, E) :
    PiTensorProduct.lift f.toMultilinearMap (tensorSymmetrization X) =
      PiTensorProduct.lift (formSymmetrization f).toMultilinearMap X := by
  change (PiTensorProduct.liftIsometry ℝ (fun _ : ι => E) ℝ f) (tensorSymmetrization X) =
    (PiTensorProduct.liftIsometry ℝ (fun _ : ι => E) ℝ (formSymmetrization f)) X
  simp only [tensorSymmetrization, formSymmetrization, _root_.map_smul, _root_.map_sum,
    smul_apply, sum_apply, smul_eq_mul, PiTensorProduct.liftIsometry_apply_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [PiTensorProduct.lift_reindex_symm]
  apply congrArg (fun h : MultilinearMap ℝ (fun _ : ι => E) ℝ => PiTensorProduct.lift h X)
  ext v
  simp only [MultilinearMap.domDomCongrLinearEquiv'_apply, MultilinearMap.coe_mk,
    Function.comp_apply, ContinuousMultilinearMap.domDomCongr_toMultilinearMap,
    MultilinearMap.domDomCongr_apply]
  congr 1
  ext i
  simp [Equiv.piCongrLeft'_apply]

/-- Reindexing an already averaged form leaves it unchanged.
Article: main_krylov, thm:Hp.
Proof: multiplication by the fixed permutation bijects the actual finite
averaging group. -/
theorem formSymmetrization_invariant (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) ℝ)
    (τ : Equiv.Perm ι) : domDomCongr τ (formSymmetrization f) = formSymmetrization f := by
  ext v
  simp only [formSymmetrization, ContinuousMultilinearMap.domDomCongr_apply,
    smul_apply, sum_apply, smul_eq_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)

/-- The true form symmetrizer is idempotent.
Article: main_krylov, thm:Hp. Proof: average the proved permutation invariance. -/
theorem formSymmetrization_idempotent (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) ℝ) :
    formSymmetrization (formSymmetrization f) = formSymmetrization f := by
  have hcard : (Fintype.card (Equiv.Perm ι) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  change (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ •
    (∑ σ : Equiv.Perm ι, domDomCongr σ (formSymmetrization f)) = formSymmetrization f
  simp only [formSymmetrization_invariant, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- A genuine symmetric multilinear form is invariant under every slot permutation.
Article: main_krylov, thm:Hp. -/
def IsSymmetricForm (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) ℝ) : Prop :=
  ∀ σ : Equiv.Perm ι, domDomCongr σ f = f

/-- Averaging a form does not change its actual pairing with a symmetrized tensor.
Article: main_krylov, thm:Hp.
Proof: adjointness of the two real symmetrizers and true idempotence. -/
theorem lift_formSymmetrization_on_tensorSymmetrization
    (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) ℝ) (X : ⨂[ℝ] _ : ι, E) :
    PiTensorProduct.lift (formSymmetrization f).toMultilinearMap (tensorSymmetrization X) =
      PiTensorProduct.lift f.toMultilinearMap (tensorSymmetrization X) := by
  rw [lift_tensorSymmetrization, lift_tensorSymmetrization, formSymmetrization_idempotent]

/-- The genuine tensor symmetrizer is contractive in the actual projective/nuclear norm.
Article: main_krylov, thm:Hp.
Proof: norm the actual symmetrized tensor with Hahn--Banach, transfer that
pairing to the contractive form symmetrizer, and apply the genuine dual bound. -/
theorem norm_tensorSymmetrization_le (X : ⨂[ℝ] _ : ι, E) :
    ‖tensorSymmetrization X‖ ≤ ‖X‖ := by
  obtain ⟨f, hf, he⟩ := (projective_multilinear_duality (tensorSymmetrization X)).1
  rw [← he]
  change PiTensorProduct.lift f.toMultilinearMap (tensorSymmetrization X) ≤ ‖X‖
  rw [lift_tensorSymmetrization]
  exact projective_pairing_le X (formSymmetrization f) ((norm_formSymmetrization_le f).trans hf)

/-- The true symmetric tensor nuclear norm is the attained dual support of symmetric multilinear unit forms.
Article: main_krylov, thm:Hp, symmetric spectral/nuclear duality.
Proof: a genuine norming multilinear functional exists by Hahn--Banach;
averaging it preserves its tensor pairing and cannot increase its norm.
The converse is the actual projective tensor universal-property estimate. -/
theorem symmetric_projective_duality (X : ⨂[ℝ] _ : ι, E) :
    IsGreatest ((fun f : ContinuousMultilinearMap ℝ (fun _ : ι => E) ℝ =>
      PiTensorProduct.lift f.toMultilinearMap (tensorSymmetrization X)) ''
        {f | ‖f‖ ≤ 1 ∧ IsSymmetricForm f}) ‖tensorSymmetrization X‖ := by
  obtain ⟨f, hf, he⟩ := (projective_multilinear_duality (tensorSymmetrization X)).1
  refine ⟨⟨formSymmetrization f, ⟨(norm_formSymmetrization_le f).trans hf,
    formSymmetrization_invariant f⟩, ?_⟩, ?_⟩
  · change PiTensorProduct.lift (formSymmetrization f).toMultilinearMap (tensorSymmetrization X) =
      ‖tensorSymmetrization X‖
    rw [lift_formSymmetrization_on_tensorSymmetrization]
    exact he
  · rintro v ⟨g, hg, rfl⟩
    exact projective_pairing_le _ g hg.1

/-- Symmetrization fixes every genuine slot-symmetric form.
Article: main_krylov, thm:Hp. Proof: average its exact slot invariance. -/
theorem formSymmetrization_of_symmetric (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) ℝ)
    (hf : IsSymmetricForm f) : formSymmetrization f = f := by
  have hcard : (Fintype.card (Equiv.Perm ι) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hf' : ∀ σ : Equiv.Perm ι, domDomCongr σ f = f := hf
  simp only [formSymmetrization, hf', Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- The true tensor symmetrization is a bounded linear operator.
Article: main_krylov, thm:Hp, continuity of the actual directional nuclear norm.
Proof: the actual finite average is linear and its proved nuclear contraction
supplies the genuine continuous-linear bound. -/
def tensorSymmetrizationL : (⨂[ℝ] _ : ι, E) →L[ℝ] ⨂[ℝ] _ : ι, E :=
  let L : (⨂[ℝ] _ : ι, E) →ₗ[ℝ] ⨂[ℝ] _ : ι, E :=
    (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ •
      ∑ σ : Equiv.Perm ι, (PiTensorProduct.reindex ℝ (fun _ : ι => E) σ).symm.toLinearMap
  L.mkContinuous 1 (by
    intro X
    simpa only [L, LinearMap.smul_apply, LinearMap.sum_apply, one_mul,
      tensorSymmetrization, LinearEquiv.coe_coe] using norm_tensorSymmetrization_le X)

/-- The continuous symmetrizer acts by the exact finite permutation average.
Article: main_krylov, thm:Hp. Proof: evaluate the constructed true linear map. -/
theorem tensorSymmetrizationL_apply (X : ⨂[ℝ] _ : ι, E) :
    tensorSymmetrizationL X = tensorSymmetrization X := by
  simp [tensorSymmetrizationL, tensorSymmetrization]

end
end krylov.Tensor
