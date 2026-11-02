import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
Article: main_krylov, thm:Hp, genuine tensor spectral/projective duality.
Use: reuse mathlib's actual projective tensor seminorm, defined by infima of
finite rank-one decompositions, and its isometric multilinear universal
property. Hahn--Banach gives the attained dual support; no nuclear dual
formula is postulated as the definition of the norm.
Source: Friedland--Lim (2018), tensor spectral/nuclear duality; mathlib
PiTensorProduct.liftIsometry and the real Hahn--Banach norming functional.
-/

namespace krylov.Tensor
noncomputable section
open scoped TensorProduct
variable {ι : Type*} [Fintype ι] {E : ι → Type*}
variable [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- Every actual multilinear unit functional is bounded by the genuine projective tensor norm.
Article: main_krylov, thm:Hp, the nuclear-dual upper bound.
Proof: use the proved projective tensor universal-property estimate. -/
theorem projective_pairing_le (X : ⨂[ℝ] i, E i) (f : ContinuousMultilinearMap ℝ E ℝ)
    (hf : ‖f‖ ≤ 1) : PiTensorProduct.lift f.toMultilinearMap X ≤ ‖X‖ := by
  calc
    _ ≤ ‖PiTensorProduct.lift f.toMultilinearMap X‖ := le_abs_self _
    _ ≤ ‖f‖ * ‖X‖ := PiTensorProduct.norm_eval_le_projectiveSeminorm f X
    _ ≤ ‖X‖ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hf (norm_nonneg X)

/-- The genuine projective tensor norm is the attained support of the actual multilinear unit ball.
Article: main_krylov, thm:Hp, tensor spectral/nuclear duality before symmetrization.
Proof: apply real Hahn--Banach to the actual projective seminormed tensor
space and transport its norming functional through mathlib's isometric
multilinear universal property. This also treats the zero tensor. -/
theorem projective_multilinear_duality (X : ⨂[ℝ] i, E i) :
    IsGreatest ((fun f : ContinuousMultilinearMap ℝ E ℝ =>
      PiTensorProduct.lift f.toMultilinearMap X) '' {f | ‖f‖ ≤ 1}) ‖X‖ := by
  obtain ⟨g, hg, hval⟩ := exists_dual_vector'' ℝ X
  let f := (PiTensorProduct.liftIsometry ℝ E ℝ).symm g
  have hf : ‖f‖ ≤ 1 := by
    simpa only [f, LinearIsometryEquiv.norm_map] using hg
  have he : PiTensorProduct.lift f.toMultilinearMap X = ‖X‖ := by
    rw [← PiTensorProduct.liftIsometry_apply_apply]
    change PiTensorProduct.liftIsometry ℝ E ℝ
      ((PiTensorProduct.liftIsometry ℝ E ℝ).symm g) X = ‖X‖
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hval
  refine ⟨⟨f, hf, he⟩, ?_⟩
  rintro v ⟨h, hh, rfl⟩
  exact projective_pairing_le X h hh

end
end krylov.Tensor
