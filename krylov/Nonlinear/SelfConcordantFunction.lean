import krylov.Nonlinear.SelfConcordantHessian
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
Article: main_krylov, thm:RFCS, actual standard self-concordant scalar functions.
Use: Give the standard mixed differential formulation on a genuine open
convex domain using the actual Riesz gradient of the scalar function,
its true Hessian and third derivative. These primitive function data imply
actual C^3 regularity and the usual diagonal self-concordance inequality;
no trajectory, expansion or local convergence bound is stored.
Source: Nesterov18, Lemma 5.1.2, mixed self-concordance formulation;
mathlib gradient/fderiv Riesz identity and the open-domain ContDiff derivative
characterization. The genuine derivative fields are proved uniquely determined.
-/

namespace krylov.Nonlinear
noncomputable section
open Set InnerProductSpace
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Genuine scalar-function differential data for standard self-concordance in its mixed formulation on an open convex domain.
Use: Keep the actual scalar function, its true gradient, Hessian and third variation as the primitive nonlinear hypotheses.
Article: main_krylov, thm:RFCS, original scalar-function self-concordance data.
Source: Nesterov18, Lemma 5.1.2, standard mixed differential formulation.
-/
structure StandardSelfConcordantData (f : E → ℝ) (U : Set E) where
  /-- The genuine scalar-function domain is open. -/
  open_domain : IsOpen U
  /-- The original domain is convex, so all admitted true comparison segments are enclosed. -/
  convex_domain : Convex ℝ U
  /-- The scalar function is genuinely differentiable on its original domain. -/
  differentiable : DifferentiableOn ℝ f U
  /-- The actual Hessian field, identified with the true gradient derivative below. -/
  hessian : E → E →L[ℝ] E
  /-- The actual third variation, identified with the true Hessian derivative below. -/
  variation : E → E →L[ℝ] E →L[ℝ] E
  /-- The true mathematical gradient of the scalar function has exactly this Hessian derivative. -/
  gradient_derivative : ∀ x∈U, HasFDerivAt (gradient f) (hessian x) x
  /-- The genuine Hessian field has exactly this true third derivative. -/
  hessian_derivative : ∀ x∈U, HasFDerivAt hessian (variation x) x
  /-- The actual third derivative is continuous on the original domain. -/
  variation_continuous : ContinuousOn variation U
  /-- The actual Hessian is self-adjoint in the original physical coordinates. -/
  hessian_symmetric : ∀ x∈U, (hessian x).toLinearMap.IsSymmetric
  /-- The true Hessian is positive semidefinite on the original convex domain. -/
  hessian_nonnegative : ∀ x∈U, ∀ v : E, 0 ≤ inner ℝ v (hessian x v)
  /-- The standard mixed self-concordance differential inequality holds for the actual Hessian and actual third variation. -/
  mixed : ∀ x∈U, ∀ u v w : E, |inner ℝ v (variation x u w)|≤
    2*Real.sqrt (inner ℝ u (hessian x u))*Real.sqrt (inner ℝ v (hessian x v))*Real.sqrt (inner ℝ w (hessian x w))

/-- A genuine scalar function is standard self-concordant on its open convex domain when its actual differential fields satisfy the standard mixed formulation.
Use: State the source nonlinear theorem directly for actual scalar functions.
Article: main_krylov, thm:RFCS, original scalar-function self-concordance data.
Source: Nesterov18, Lemma 5.1.2, standard mixed differential formulation.
-/
def IsStandardSelfConcordantOn (f : E → ℝ) (U : Set E) : Prop := Nonempty (StandardSelfConcordantData f U)

/-- The supplied genuine self-concordant Hessian is the actual derivative of the mathematical scalar-function gradient.
Use: Identify the prescribed reference base with the true minimizer Hessian.
Article: main_krylov, thm:RFCS, original scalar-function self-concordance data.
Source: Nesterov18, Lemma 5.1.2, standard mixed differential formulation.
Proof: Use uniqueness of the actual Fréchet derivative.
-/
theorem StandardSelfConcordantData.hessian_eq_fderiv (f : E → ℝ) (U : Set E)
    (D : StandardSelfConcordantData f U) (x : E) (hx : x∈U) : D.hessian x=fderiv ℝ (gradient f) x :=
  (D.gradient_derivative x hx).fderiv.symm

/-- The genuine self-concordant third variation is exactly the actual derivative of its true Hessian field.
Use: Keep the mixed self-concordance condition tied to actual scalar derivatives.
Article: main_krylov, thm:RFCS, original scalar-function self-concordance data.
Source: Nesterov18, Lemma 5.1.2, standard mixed differential formulation.
Proof: Use uniqueness of the actual Fréchet derivative.
-/
theorem StandardSelfConcordantData.variation_eq_fderiv (f : E → ℝ) (U : Set E)
    (D : StandardSelfConcordantData f U) (x : E) (hx : x∈U) : D.variation x=fderiv ℝ D.hessian x :=
  (D.hessian_derivative x hx).fderiv.symm

/-- The genuine standard mixed self-concordance data imply the usual diagonal cubic differential bound.
Use: Connect the chosen standard mixed formulation to the ordinary local cubic self-concordance condition.
Article: main_krylov, thm:RFCS, original scalar-function self-concordance data.
Source: Nesterov18, Lemma 5.1.2, standard mixed differential formulation.
Proof: Evaluate the genuine mixed differential inequality on three copies of the actual direction.
-/
theorem StandardSelfConcordantData.diagonal (f : E → ℝ) (U : Set E)
    (D : StandardSelfConcordantData f U) (x : E) (hx : x∈U) (v : E) :
    |inner ℝ v (D.variation x v v)|≤2*(Real.sqrt (inner ℝ v (D.hessian x v)))^3 := by
  exact (D.mixed x hx v v v).trans_eq (by ring)


/-- Genuine self-concordant scalar-function differential data imply actual C^3 regularity on the original open domain.
Use: Discharge the source C^3 regularity from the true continuous third derivative data.
Article: main_krylov, thm:RFCS, original scalar-function self-concordance data.
Source: Nesterov18, Lemma 5.1.2, standard mixed differential formulation.
Proof: Use the open-domain derivative characterization twice to prove actual Hessian and gradient regularity, then transport the gradient through the genuine Riesz map to identify the true scalar Fréchet derivative.
-/
theorem StandardSelfConcordantData.contDiffOn (f : E → ℝ) (U : Set E)
    (D : StandardSelfConcordantData f U) : ContDiffOn ℝ 3 f U := by
  have hH : ContDiffOn ℝ 1 D.hessian U := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0) D.open_domain.uniqueDiffOn).mpr
    exact ⟨by simp,D.variation,contDiffOn_zero.mpr D.variation_continuous,
      fun x hx => (D.hessian_derivative x hx).hasFDerivWithinAt⟩
  have hg : ContDiffOn ℝ 2 (gradient f) U := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 1) D.open_domain.uniqueDiffOn).mpr
    exact ⟨by simp,D.hessian,hH,fun x hx => (D.gradient_derivative x hx).hasFDerivWithinAt⟩
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 2) D.open_domain).mpr
  refine ⟨D.differentiable,by simp,?_⟩
  let R := (toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap
  have hR : ContDiff ℝ 2 R := R.contDiff
  have hdf : ContDiffOn ℝ 2 (fun x => R (gradient f x)) U := hR.comp_contDiffOn hg
  have he : (fun x => R (gradient f x))=fderiv ℝ f := by
    funext x
    change (toDual ℝ E) (gradient f x)=fderiv ℝ f x
    exact toDual_gradient
  rw [he] at hdf
  exact hdf

end
end krylov.Nonlinear
