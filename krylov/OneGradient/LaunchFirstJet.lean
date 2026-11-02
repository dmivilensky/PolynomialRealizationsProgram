import krylov.OneGradient.LaunchModelRegularity
import krylov.Information.FullModelQuery
import krylov.Information.PhysicalRadius
set_option autoImplicit false
/-!
Article: main_krylov, prop:launch, actual full-window physical output derivative.
Use: derive the genuine semantic gradient's canonical first variation directly
from primitive smooth columns, actual observations and incoming gradient.
Source: the original full observed coefficient solve, exact canonical model
error identity, true model inverse domain and zero-reference-factor differentiation.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open krylov.Correction krylov.Information
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine semantic output of the original full-window observed-model solve.
Use: the correction is the real inverse of the actual observed physical model.
Article: main_krylov, prop:launch. -/
def launchSemanticGradient (S : Matrix (Fin n) (Fin n) ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  g-cgOperator (A n) (cgOperator (launchObservedModel S A)⁻¹ g)

/-- The semantic full-model output is exactly the original physical observed
coefficient correction, in its true chronological stored-column coordinates.
Use: no replacement model, assumed update or surrogate output enters the launch derivative.
Article: main_krylov, prop:launch.
Proof: the actual full physical column matrix is the original S. The reused
true full_model_query identifies its native coefficient solve with the genuine
inverse ambient observed model; apply the real output segment operator. -/
theorem launch_semantic_coefficients (S : Matrix (Fin n) (Fin n) ℝ) (hu : IsUnit S.det)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    let s := fun i : Fin n => WithLp.toLp 2 (fun a => S a i)
    let H := latest (Sᵀ*pairImages S A)
    launchSemanticGradient S A g=g+cgOperator (A n) (combine s (modelCoefficients s H g)) := by
  let s := fun i : Fin n => WithLp.toLp 2 (fun a => S a i)
  have hs : fullBasisMatrix s=S := by rfl
  have hq := full_model_query s (latest (Sᵀ*pairImages S A)) (by rw [hs];exact hu) g
  rw [hs] at hq
  dsimp only
  rw [hq,map_neg]
  rfl

/-- The genuine full-model output satisfies its exact canonical model-error action.
Use: first variation follows from the actual solve and a truly vanishing
reference error, not from a postulated update or coefficient expansion.
Article: main_krylov, prop:launch.
Proof: true inverse-model cancellation rewrites the original semantic residual
as minus the actual physical model error acting on the true inverse query;
the proved genuine positive-root action gives its canonical form. -/
theorem launch_normal_identity
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (S : Matrix (Fin n) (Fin n) ℝ) (A : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hJ : IsUnit (launchObservedModel S A).det) (g : EuclideanSpace ℝ (Fin n)) :
    cgOperator (metricRoot base)⁻¹ (launchSemanticGradient S A g)=
      -cgOperator (relativeOperator base (A n-launchObservedModel S A))
        (cgOperator (metricRoot base) (cgOperator (launchObservedModel S A)⁻¹ g)) := by
  let J := launchObservedModel S A
  change IsUnit J.det at hJ
  have hcancel : cgOperator J (cgOperator J⁻¹ g)=g := by
    simp only [cgOperator,← mul_apply_eq_comp,← map_mul,Matrix.mul_nonsing_inv _ hJ,map_one,one_apply_eq_self]
  have he : launchSemanticGradient S A g= -cgOperator (A n-J) (cgOperator J⁻¹ g) := by
    simp only [launchSemanticGradient,cgOperator,map_sub,_root_.sub_apply]
    change g-cgOperator (A n) (cgOperator J⁻¹ g)=
      -(cgOperator (A n) (cgOperator J⁻¹ g)-cgOperator J (cgOperator J⁻¹ g))
    rw [hcancel]
    abel
  rw [he,map_neg]
  exact congrArg Neg.neg (canonical_form_action base (A n-J) hb (cgOperator J⁻¹ g)).symm

/-- The actual full-window observed coefficient solve has exactly the original
canonical launch-compression first derivative from primitive C1 data.
Use: derivatives of the moving columns, actual inverse model and incoming
gradient contribute no extra first-order terms at the true quadratic reference.
Article: main_krylov, prop:launch, general first-variation identity.
Proof: primitive observations derive the actual model inverse regularity and
genuine local inverse domains. The proved real model-error jet acts on the
true reference canonical launch gradient; its zero value removes the other
product derivative. Exact physical normal form identifies the actual semantic output. -/
theorem launch_semantic_first_jet
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (S : ℝ → Matrix (Fin n) (Fin n) ℝ) (hS : ContDiffAt ℝ 1 S 0) (hu : IsUnit (S 0).det)
    (A : ℝ → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ 1 (fun t => A t k) 0)
    (hsym : ∀ t k,(A t k).IsSymm) (hA0 : ∀ k,A 0 k=base)
    (g : ℝ → EuclideanSpace ℝ (Fin n)) (hg : ContDiffAt ℝ 1 g 0) :
    let P := fun l => transportedFlag (metricRoot base*S 0) l
    let R := cgOperator (metricRoot base)⁻¹
    let C := ∑ l∈Finset.range n,cgOperator (P l)ᵀ*
      (R*(deriv (fun t => cgOperator (A t (l+1))) 0-deriv (fun t => cgOperator (A t l)) 0)*R)*cgOperator (P l)
    HasDerivAt (fun t => R (launchSemanticGradient (S t) (A t) (g t))) (-(C (R (g 0)))) 0 := by
  let J := fun t => launchObservedModel (S t) (A t)
  let E := fun t => cgOperator (relativeOperator base (A t n-J t))
  let R := cgOperator (metricRoot base)⁻¹
  let C := ∑ l∈Finset.range n,cgOperator (transportedFlag (metricRoot base*S 0) l)ᵀ*
    (R*(deriv (fun t => cgOperator (A t (l+1))) 0-deriv (fun t => cgOperator (A t l)) 0)*R)*
      cgOperator (transportedFlag (metricRoot base*S 0) l)
  let v := fun t => cgOperator (metricRoot base) (cgOperator (J t)⁻¹ (g t))
  have hJ0 : J 0=base := by
    change launchObservedModel (S 0) (A 0)=base
    rw [show A 0=(fun _ => base) from funext hA0]
    exact launch_model_reference base (S 0) hb.1.isSymm hu
  have hmodel := (launch_model_contDiff S hS hu A hA).2
  have hinv := launch_model_inverse_contDiff base hb S hS hu A hA hA0
  have hv : ContDiffAt ℝ 1 v 0 :=
    (cgOperator (metricRoot base)).contDiff.contDiffAt.comp 0
      ((matrixOperator_contDiffAt _ 0 hinv).clm_apply hg)
  have hv0 : v 0=R (g 0) := by
    change cgOperator (metricRoot base) (cgOperator (J 0)⁻¹ (g 0))=R (g 0)
    rw [hJ0]
    have hcancel : cgOperator base (cgOperator base⁻¹ (g 0))=g 0 := by
      simp only [cgOperator,← mul_apply_eq_comp,← map_mul,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hb.det_pos.ne'),map_one,one_apply_eq_self]
    have he := canonical_reference_action base hb (cgOperator base⁻¹ (g 0))
    rw [hcancel] at he
    exact he.symm
  have hE0 : E 0=0 := by
    simp only [E,hJ0,hA0,sub_self,relativeOperator,Matrix.mul_zero,Matrix.zero_mul,cgOperator,map_zero]
  have hjet := launch_model_error_first_jet base hb S hS hu A hA hsym hA0
  have hact := (hjet.clm_apply (hv.differentiableAt (by norm_num)).hasDerivAt).neg
  have hact' : HasDerivAt (fun t => -(E t (v t)))
      (-((∑ l∈Finset.range n,cgOperator (transportedFlag (metricRoot base*S 0) l)ᵀ*
        (R*(deriv (fun t => cgOperator (A t (l+1))) 0-deriv (fun t => cgOperator (A t l)) 0)*R)*
          cgOperator (transportedFlag (metricRoot base*S 0) l)) (R (g 0)))) 0 := by
    change HasDerivAt (fun t => -(E t (v t))) (-(C (R (g 0)))) 0
    change HasDerivAt (fun t => -(E t (v t))) (-(C (v 0)+E 0 (deriv v 0))) 0 at hact
    simpa only [hE0,_root_.zero_apply,add_zero,hv0] using hact
  have hunit : ∀ᶠ t in 𝓝 (0 : ℝ),IsUnit (J t).det := by
    have hu0 : IsUnit (J 0) := by
      rw [hJ0]
      exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hb.det_pos.ne')
    exact (hmodel.continuousAt.tendsto.eventually (Units.isOpen.mem_nhds hu0)).mono
      (fun t ht => (Matrix.isUnit_iff_isUnit_det _).mp ht)
  have he : (fun t => R (launchSemanticGradient (S t) (A t) (g t)))=ᶠ[𝓝 0] (fun t => -(E t (v t))) := by
    filter_upwards [hunit] with t ht
    exact launch_normal_identity base hb (S t) (A t) ht (g t)
  dsimp only
  exact hact'.congr_of_eventuallyEq he

end
end krylov.OneGradient
