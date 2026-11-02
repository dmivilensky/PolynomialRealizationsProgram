import krylov.Methods.DirectBroyden
import krylov.Stability.ContDiffSolve
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), native direct Broyden operator calculus.
Use: retain the literal proved direct update as a genuine bounded operator
and derive primitive joint C-r regularity at its actual curvature domains.
Source: exact forgetful linear-map dictionary, smooth real rank-one maps,
actual scalar reciprocals and the original direct-update coefficients. -/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The original direct Broyden update as its genuine bounded operator.
Use: actual operator norms and native finite perturbation bounds concern
exactly the proved direct linear update, with no alternative model formula.
Article: main_krylov, prop:classical(c), apE:broyden. -/
def directBroydenOperatorUpdate (B : E →L[ℝ] E) (s y : E) (phi : ℝ) : E →L[ℝ] E :=
  let a := inner ℝ s (B s)
  let b := inner ℝ s y
  let v := directBroydenVector B.toLinearMap s y
  B-a⁻¹ • ((innerSL ℝ s).comp B).smulRight (B s)+
    b⁻¹ • (innerSL ℝ y).smulRight y+(phi*a) • (innerSL ℝ v).smulRight v

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- Forgetting only the true bounded-operator structure gives exactly the
original direct Broyden map already proved symmetric, positive and secant.
Use: the native norm/regularity calculus inherits those genuine algebraic domains.
Article: main_krylov, prop:classical(c).
Proof: both maps have the identical literal rank-update action on every vector. -/
theorem directBroydenOperatorUpdate_toLinearMap (B : E →L[ℝ] E) (s y : E) (phi : ℝ) :
    (directBroydenOperatorUpdate B s y phi).toLinearMap=directBroydenUpdate B.toLinearMap s y phi := by
  rfl

/-- The actual original direct Broyden bounded operator is jointly C-r in
its primitive old model, observed pair and interpolation parameter at its
real two nonzero curvature domains.
Use: compact parameter control does not require interpolation schedules
along perturbations to be continuous; the actual joint update is smooth.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: true primitive products give both actual curvature scalars. Their
real reciprocals give the actual correction vector and the three bounded
rank-one terms. Compose only genuine smooth bounded-linear operations. -/
theorem directBroydenOperatorUpdate_contDiffAt {r : WithTop ℕ∞}
    (B : X → E →L[ℝ] E) (s y : X → E) (phi : X → ℝ) (x : X)
    (hB : ContDiffAt ℝ r B x) (hs : ContDiffAt ℝ r s x)
    (hy : ContDiffAt ℝ r y x) (hphi : ContDiffAt ℝ r phi x)
    (ha : inner ℝ (s x) (B x (s x))≠0) (hb : inner ℝ (s x) (y x)≠0) :
    ContDiffAt ℝ r (fun z => directBroydenOperatorUpdate (B z) (s z) (y z) (phi z)) x := by
  have hBs := hB.clm_apply hs
  have hqa := hs.inner ℝ hBs
  have hqb := hs.inner ℝ hy
  have hv : ContDiffAt ℝ r (fun z => directBroydenVector (B z).toLinearMap (s z) (y z)) x :=
    ((hqb.inv hb).smul hy).sub ((hqa.inv ha).smul hBs)
  have hS := (innerSL ℝ).contDiff.contDiffAt.comp x hs
  have hY := (innerSL ℝ).contDiff.contDiffAt.comp x hy
  have hV := (innerSL ℝ).contDiff.contDiffAt.comp x hv
  exact ((hB.sub ((hqa.inv ha).smul ((hS.clm_comp hB).smulRight hBs))).add
    ((hqb.inv hb).smul (hY.smulRight hy))).add ((hphi.mul hqa).smul (hV.smulRight hv))

end
end krylov.Methods
