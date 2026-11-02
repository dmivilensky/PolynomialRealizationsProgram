import krylov.Methods.DirectBroydenInverse
import krylov.Reference.CanonicalGradient
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), complete original relative source.
Use: instantiate the genuine native comparison with the literal original
physical pair images and actual inverse-root relative perturbation norm.
Source: exact positive-root cancellation and the proved native comparison;
all model bounds and inverse domains remain derived.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability krylov.LinearAlgebra krylov.Secant
open Matrix Filter Topology Asymptotics
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {α : Type*} {n p : ℕ} {l : Filter α} {t : α → ℝ}

/-- The actual relative matrix perturbation order gives the genuine
physical operator perturbation order at the fixed positive reference.
Use: the original source inverse-root norm assumption supplies the true
primitive native image errors, without an extra physical rate hypothesis.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: cancel the true positive root against both actual inverse-root
factors. Multiplication by the fixed root preserves the genuine spectral
rate, as does the actual isometric physical operator dictionary. -/
theorem directBroyden_relative_operator_order (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (Ai : α → Matrix (Fin n) (Fin n) ℝ)
    (hAi : (fun z => relativeOperator A (Ai z-A)) =O[l] t) :
    (fun z => cgOperator (Ai z-A)) =O[l] t := by
  have he (F : Matrix (Fin n) (Fin n) ℝ) : metricRoot A*relativeOperator A F*metricRoot A=F := by
    unfold relativeOperator
    calc
      _ = (metricRoot A*(metricRoot A)⁻¹)*F*((metricRoot A)⁻¹*metricRoot A) := by noncomm_ring
      _ = F := by rw [Matrix.mul_nonsing_inv _ (metricRoot_det_unit A hA),
        Matrix.nonsing_inv_mul _ (metricRoot_det_unit A hA),Matrix.one_mul,Matrix.mul_one]
  have h := matrix_mul_const_bigO _ (metricRoot A) t (matrix_const_mul_bigO (metricRoot A) _ t hAi)
  exact matrix_bigO_toEuclideanCLM _ _ (h.congr_left (fun z => he (Ai z-A)))

/-- The literal original source data define a genuine primitive native
direct Broyden perturbation with their exact images y_i=A_i s_i and exact
relative norm assumptions. No model comparison, updated-model bounds,
pivots, smooth schedule or first-order step convergence is supplied.
Use: instantiate the full native spectral model and final inverse-step
theorems directly from the hypotheses printed in the source proposition.
Article: main_krylov, prop:classical(c), apE:broyden. -/
def directBroydenRelativePerturbation
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (B0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB0 : B0.toLinearMap.IsSymmetric) (hBpos : ∀ w,w≠0 → 0 < inner ℝ w (B0 w))
    (s : α → ℕ → EuclideanSpace ℝ (Fin n)) (s0 : ℕ → EuclideanSpace ℝ (Fin n))
    (hs0 : ∀ i<p,s0 i≠0) (hs : ∀ i<p,Tendsto (fun z => s z i) l (𝓝 (s0 i)))
    (Ai : α → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hAi : ∀ i<p,(fun z => relativeOperator A (Ai z i-A)) =O[l] t)
    (hcross : ∀ i<p,∀ j<p,i≠j → (fun z => inner ℝ (s z i) (cgOperator A (s z j))) =O[l] t)
    (phi : α → ℕ → ℝ) (hphi : ∀ᶠ z in l,∀ i<p,0≤phi z i ∧ phi z i≤1)
    (ht : Tendsto t l (𝓝 0)) : DirectBroydenPerturbation (E := EuclideanSpace ℝ (Fin n)) l t p where
  reference := cgOperator A
  reference_symmetric := (cgOperator_positive A hA).1
  reference_positive := (cgOperator_positive A hA).2
  initial := B0
  initial_symmetric := hB0
  initial_positive := hBpos
  step := s
  image := fun z i => cgOperator (Ai z i) (s z i)
  referenceStep := s0
  referenceStep_ne := hs0
  step_limit := hs
  image_error := by
    intro i hi
    have h := clm_apply_bigO (fun z => cgOperator (Ai z i-A)) (fun z => s z i) _ _
      (directBroyden_relative_operator_order A hA (fun z => Ai z i) (hAi i hi)) ((hs i hi).isBigO_one ℝ)
    have he (z : α) : cgOperator (Ai z i-A) (s z i)=cgOperator (Ai z i) (s z i)-cgOperator A (s z i) := by
      change Matrix.toEuclideanCLM (𝕜 := ℝ) (Ai z i-A) (s z i)=_
      rw [map_sub,_root_.sub_apply]
      rfl
    simpa only [mul_one,he] using h
  cross_error := hcross
  parameter := phi
  parameter_cube := hphi
  scale_limit := ht

end
end krylov.Methods
