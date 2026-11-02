import krylov.Tensor.CubicMultilinear
import krylov.LinearAlgebra.SupportDuality

/-!
Article: main_krylov, thm:Hp, exact vector-response tensor duality.
Use: pair the actual finite compatible cubic response with an arbitrary unit
output direction and obtain exactly its symmetrized target nuclear norm.
The genuine attaining form and attaining output direction are constructed
from the proved projective tensor duality and compactness.
Source: Friedland--Lim (2018); the reused finite-dimensional directional
support-to-vector-norm theorem.
-/

namespace krylov.Tensor
noncomputable section
open Set
open scoped TensorProduct BigOperators InnerProductSpace NNReal
variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual finite compatible vector response of a cubic tensor.
Article: main_krylov, thm:Hp. -/
def cubicResponse (a b c d : ι → E)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) : E :=
  ∑ j, f ![b j, c j, d j] • a j

/-- The genuine rank-one target tensor paired with a response direction.
Article: main_krylov, thm:Hp. -/
def responseTensor (a b c d : ι → E) (u : E) : ⨂[ℝ] _ : Fin 3, E :=
  ∑ j, inner ℝ u (a j) • PiTensorProduct.tprod ℝ ![b j, c j, d j]

/-- Pairing the actual response equals the genuine tensor contraction.
Article: main_krylov, thm:Hp.
Proof: expand the actual finite response, commute the linear tensor lift
with its true sum, and evaluate each genuine rank-one tensor. -/
theorem inner_cubicResponse (a b c d : ι → E)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (u : E) :
    inner ℝ u (cubicResponse a b c d f) =
      PiTensorProduct.lift f.toMultilinearMap (responseTensor a b c d u) := by
  simp only [cubicResponse, responseTensor, inner_sum, inner_smul_right,
    map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [PiTensorProduct.lift.tprod]
  exact mul_comm _ _

/-- A symmetric tensor response pairs with exactly the symmetrized target.
Article: main_krylov, thm:Hp.
Proof: the actual form is fixed by symmetrization and the two true
symmetrizers are adjoint under the genuine tensor pairing. -/
theorem inner_cubicResponse_symmetric (a b c d : ι → E)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hf : IsSymmetricForm f) (u : E) :
    inner ℝ u (cubicResponse a b c d f) = PiTensorProduct.lift f.toMultilinearMap
      (tensorSymmetrization (responseTensor a b c d u)) := by
  rw [lift_tensorSymmetrization, formSymmetrization_of_symmetric f hf]
  exact inner_cubicResponse a b c d f u

/-- The actual finite rank-one target varies continuously with its real output direction.
Article: main_krylov, thm:Hp.
Proof: it is a finite sum of continuous genuine inner-product coefficients
times fixed projective tensors. -/
theorem continuous_responseTensor (a b c d : ι → E) : Continuous (responseTensor a b c d) := by
  unfold responseTensor
  fun_prop

/-- The actual symmetrized directional nuclear norm is continuous.
Article: main_krylov, thm:Hp, existence of the displayed maximum.
Proof: compose the finite rank-one target with the proved continuous
nuclear symmetrizer and the genuine tensor norm. -/
theorem continuous_responseNuclear (a b c d : ι → E) :
    Continuous (fun u : E => ‖tensorSymmetrization (responseTensor a b c d u)‖₊) := by
  have hc := (tensorSymmetrizationL (ι := Fin 3) (E := E)).continuous.comp
    (continuous_responseTensor a b c d)
  simpa only [Function.comp_apply, tensorSymmetrizationL_apply] using hc.nnnorm

variable [FiniteDimensional ℝ E]

/-- Every actual directional cubic response has its exact attained nuclear support.
Article: main_krylov, thm:Hp, before maximizing the output direction.
Proof: use the proved actual symmetric spectral/nuclear duality and the
exact contraction dictionary of the finite response. -/
theorem cubicResponse_directional_support (a b c d : ι → E) (C : ℝ≥0) (u : E) :
    IsGreatest ((fun f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ =>
      inner ℝ u (cubicResponse a b c d f)) ''
        {f | IsSymmetricForm f ∧ ∀ x : E, ‖x‖ = 1 → |f (fun _ : Fin 3 => x)| ≤ (C : ℝ)})
      ((C * ‖tensorSymmetrization (responseTensor a b c d u)‖₊ : ℝ≥0) : ℝ) := by
  have h := symmetric_cubic_nuclear_support (responseTensor a b c d u) C.coe_nonneg
  convert h using 1
  · apply Set.image_congr
    intro f hf
    exact inner_cubicResponse_symmetric a b c d f hf.1 u
  · simp only [NNReal.coe_mul, coe_nnnorm]

/-- The true compatible cubic amplification is exactly the maximum directional nuclear norm.
Article: main_krylov, thm:Hp, the displayed equality for Gamma_T.
Proof: each actual directional support has the proved genuine tensor
norming form; compactness of the real unit sphere supplies an actual
maximizing direction, and the common support-to-vector-norm theorem gives
the exact attained vector response. No tensor maximum is an input field. -/
theorem cubicResponse_nuclear_amplification [Nontrivial E]
    (a b c d : ι → E) (C : ℝ≥0) :
    ∃ A : ℝ≥0,
      IsGreatest ((fun u : E => C * ‖tensorSymmetrization (responseTensor a b c d u)‖₊) ''
        {u : E | ‖u‖ = 1}) A ∧
      IsGreatest ((fun f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ =>
        ‖cubicResponse a b c d f‖) ''
          {f | IsSymmetricForm f ∧ ∀ x : E, ‖x‖ = 1 → |f (fun _ : Fin 3 => x)| ≤ (C : ℝ)}) (A : ℝ) := by
  apply krylov.LinearAlgebra.norm_duality_of_continuous_support
    (out := cubicResponse a b c d) (φ := fun u => C * ‖tensorSymmetrization (responseTensor a b c d u)‖₊)
  · exact continuous_const.mul (continuous_responseNuclear a b c d)
  · exact cubicResponse_directional_support a b c d C

end
end krylov.Tensor
