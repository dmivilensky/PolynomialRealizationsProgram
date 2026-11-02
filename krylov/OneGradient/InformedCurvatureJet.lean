import krylov.OneGradient.InformedTrial
import krylov.Stability.C1VanishingProduct
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), informed actual-increment curvature jet.
Use: derive the unmeasured curvature leading term while retaining the actual
operator change and requiring only primitive C-one vector/operator data.
Source: the proved exact informed line-error identity and genuine vanishing
middle-operator product calculus; no desired trial-error expansion is assumed. -/

namespace krylov.OneGradient
noncomputable section
open Filter Topology Asymptotics krylov.Stability
open scoped InnerProductSpace
variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact informed curvature error read after the actual new curvature
is measured; the known-base trial itself never uses this actual operator.
Use: source relative-error identity in its genuine physical coordinates.
Article: main_krylov, thm:local(a). -/
def informedCurvatureError (known actual : E →L[ℝ] E) (d : E) : ℝ :=
  -inner ℝ d ((actual-known) d)/inner ℝ d (known d)

/-- The informed curvature error has its frozen-direction expansion in the
actual operator increment with a genuine quadratic remainder from C-one data.
Use: when the parameter is the full base/increment tuple, this is the true
last-pivot expansion; derivatives of the moving direction contribute only
second order because the actual middle increment vanishes at the reference.
Article: main_krylov, thm:local(a).
Proof: smooth positive-reference curvature gives the real reciprocal domain.
The scalar inverse-curvature-weighted inner functional and actual direction
are C-one. Apply the proved zero-middle-operator product remainder and unfold
the two genuine scalar actions; no increment is replaced by its derivative. -/
theorem informed_curvature_c1_remainder (known : E →L[ℝ] E)
    (actual : X → E →L[ℝ] E) (d : X → E)
    (hactual : ContDiffAt ℝ 1 actual 0) (hd : ContDiffAt ℝ 1 d 0)
    (hzero : actual 0=known) (hden : inner ℝ (d 0) (known (d 0))≠0) :
    (fun z => informedCurvatureError known (actual z) (d z)+
      inner ℝ (d 0) ((actual z-known) (d 0))/inner ℝ (d 0) (known (d 0)))
        =O[𝓝 0] (fun z => ‖z‖^2) := by
  let q := fun z => inner ℝ (d z) (known (d z))
  let L := fun z => (-(q z)⁻¹) • innerSL ℝ (d z)
  let D := fun z => actual z-known
  have hq : ContDiffAt ℝ 1 q 0 := hd.inner ℝ (known.contDiff.contDiffAt.comp 0 hd)
  have hL : ContDiffAt ℝ 1 L 0 :=
    (hq.inv hden).neg.smul ((innerSL ℝ).contDiff.contDiffAt.comp 0 hd)
  have hD : ContDiffAt ℝ 1 D 0 := hactual.sub contDiffAt_const
  have hD0 : D 0=0 := by simp only [D,hzero,sub_self]
  have h := c1_vanishing_middle_remainder L D d
    (hL.differentiableAt (by norm_num)) (hD.differentiableAt (by norm_num))
    (hd.differentiableAt (by norm_num)) hD0
  apply h.congr_left
  intro z
  simp only [L,D,q,informedCurvatureError,_root_.smul_apply,innerSL_apply_apply,smul_eq_mul]
  ring

end
end krylov.OneGradient
