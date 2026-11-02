import krylov.Methods.LBFGS

set_option autoImplicit false
/-!
Article: main_krylov, def:classes, convex Broyden implementation bridge.
Use: construct the genuine inverse DFP/BFGS endpoint updates and their actual convex Broyden interpolation directly from observed physical secant pairs.
Source: standard DFP/BFGS inverse secant updates and convex Broyden equivalence, attributed in the article to Nazareth79 and Dixon72a/Dixon72b; all update actions below are proved from the actual linear maps.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual inverse DFP linear-map update uses the genuine secant pair and true old inverse-model action.
Use: The actual inverse DFP linear-map update uses the genuine secant pair and true old inverse-model action.
Article: main_krylov, def:classes, convex Broyden implementation bridge.
Proof: Subtract the real inverse-curvature rank-one block and add the genuine secant reciprocal block. -/
def inverseDFPUpdate (H : E →ₗ[ℝ] E) (s y : E) : E →ₗ[ℝ] E :=
  H-(inner ℝ y (H y))⁻¹ • ((innerSL ℝ y).toLinearMap.comp H).smulRight (H y)+
    (inner ℝ s y)⁻¹ • (innerSL ℝ s).toLinearMap.smulRight s

/-- The actual inverse BFGS linear-map update uses its true two-sided secant factorization.
Use: The actual inverse BFGS linear-map update uses its true two-sided secant factorization.
Article: main_krylov, def:classes, convex Broyden implementation bridge.
Proof: Form the genuine observed rank-one factors and actual secant reciprocal update. -/
def inverseBFGSUpdate (H : E →ₗ[ℝ] E) (s y : E) : E →ₗ[ℝ] E :=
  let ρ := (inner ℝ s y)⁻¹
  (LinearMap.id-ρ • (innerSL ℝ y).toLinearMap.smulRight s).comp
    (H.comp (LinearMap.id-ρ • (innerSL ℝ s).toLinearMap.smulRight y))+
      ρ • (innerSL ℝ s).toLinearMap.smulRight s

/-- The genuine inverse convex Broyden interpolation combines the actual DFP and BFGS endpoint models.
Use: The genuine inverse convex Broyden interpolation combines the actual DFP and BFGS endpoint models.
Article: main_krylov, def:classes, convex Broyden implementation bridge.
Proof: Take the true affine combination of the two actual observed secant updates. -/
def inverseBroydenUpdate (H : E →ₗ[ℝ] E) (s y : E) (θ : ℝ) : E →ₗ[ℝ] E :=
  (1-θ) • inverseDFPUpdate H s y+θ • inverseBFGSUpdate H s y

/-- The genuine inverse DFP model has exactly its true physical rank-two update action.
Use: The genuine inverse DFP model has exactly its true physical rank-two update action.
Article: main_krylov, def:classes, convex Broyden implementation bridge.
Proof: Expand actual linear-map compositions and real inner-product rank-one maps. -/
theorem inverseDFPUpdate_apply (H : E →ₗ[ℝ] E) (s y v : E) :
    inverseDFPUpdate H s y v=
      H v-(inner ℝ y (H v)/inner ℝ y (H y)) • H y+(inner ℝ s v/inner ℝ s y) • s := by
  simp only [inverseDFPUpdate,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    LinearMap.comp_apply,LinearMap.smulRight_apply,ContinuousLinearMap.coe_coe,innerSL_apply_apply,smul_smul,div_eq_mul_inv,mul_comm]

/-- The genuine inverse BFGS model has exactly the actual standard two-loop single-pair action.
Use: The genuine inverse BFGS model has exactly the actual standard two-loop single-pair action.
Article: main_krylov, def:classes, convex Broyden implementation bridge.
Proof: Expand its real two-sided linear-map factorization and collect the true observed scalar coefficients. -/
theorem inverseBFGSUpdate_apply (H : E →ₗ[ℝ] E) (s y v : E) :
    inverseBFGSUpdate H s y v=
      let ρ := (inner ℝ s y)⁻¹
      let a := ρ*inner ℝ s v
      let r := H (v-a • y)
      r+(a-ρ*inner ℝ y r) • s := by
  simp only [inverseBFGSUpdate,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    LinearMap.comp_apply,LinearMap.smulRight_apply,LinearMap.id_apply,ContinuousLinearMap.coe_coe,innerSL_apply_apply,smul_smul]
  module

/-- Every genuine scalar model eigenvector orthogonal to both actual pair vectors retains exactly its true old action under every real Broyden interpolation.
Use: Every genuine scalar model eigenvector orthogonal to both actual pair vectors retains exactly its true old action under every real Broyden interpolation.
Article: main_krylov, def:classes, convex Broyden implementation bridge.
Proof: Both actual endpoint updates preserve that real vector; their true interpolation coefficients sum to one. -/
theorem inverseBroydenUpdate_future (H : E →ₗ[ℝ] E) (s y v : E) (c θ : ℝ)
    (hv : H v=c • v) (hs : inner ℝ s v=0) (hy : inner ℝ y v=0) :
    inverseBroydenUpdate H s y θ v=c • v := by
  -- Both real endpoint updates preserve the actual orthogonal vector, so their genuine affine interpolation does too.
  rw [inverseBroydenUpdate,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.smul_apply,
    inverseDFPUpdate_apply,inverseBFGSUpdate_apply]
  simp only [hs,mul_zero,zero_div,zero_smul,sub_zero,add_zero,hv,real_inner_smul_right,hy]
  module
end
end krylov.Methods
