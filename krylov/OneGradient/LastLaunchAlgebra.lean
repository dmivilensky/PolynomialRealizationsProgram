import krylov.Methods.VirtualSolve
import krylov.Methods.ProjectedModel
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), exact actual final-launch equations.
Use: derive the incoming-gradient leading coefficient from the real old
model solve and true observed conjugacy, before any order estimates.
Source: actual inverse-model normal equation, genuine data-only conjugacy
and the literal evaluated virtual-correction-plus-trial update.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The old coordinates of the actual evaluated virtual launch equal
the genuine model mismatch times its true correction weights, plus the
actual queried-direction curvature action. All quantities are finite
computed data, with the actual model inverse domain explicit.
Use: quadratic old-row cancellation is derived from the original solve.
Article: main_krylov, thm:local(a), exact incoming old-coordinate equation.
Proof: the actual inverse-model normal equation cancels the old incoming
coordinates. Apply linearity to the genuine evaluated step, and use the
true coordinate matrix action on its actual stored-vector combination. -/
theorem lastLaunch_old_coordinates (s : Fin p → E) (M : Matrix (Fin p) (Fin p) ℝ)
    (hM : IsUnit M.det) (G d : E) (A : E →L[ℝ] E) (tau : ℝ) :
    let w := modelCoefficients s M G
    coordinates s (G+A (combine s w+tau • d))=
      (crossGram s (fun i => A (s i))-M)*ᵥw+tau • coordinates s (A d) := by
  let w := modelCoefficients s M G
  have hnormal : M*ᵥw= -(coordinates s G) := by
    rw [show w= -(M⁻¹*ᵥcoordinates s G) from rfl,Matrix.mulVec_neg,Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hM,Matrix.one_mulVec]
  have haction := coordinates_combine s (fun i => A (s i)) w
  rw [← combine_operator A s w] at haction
  dsimp only
  ext i
  have hn := congrFun hnormal i
  have ha := congrFun haction i
  change inner ℝ (s i) (A (combine s w))=(crossGram s (fun j => A (s j))*ᵥw) i at ha
  change (M*ᵥw) i= -inner ℝ (s i) G at hn
  simp only [coordinates,map_add,map_smul,inner_add_right,real_inner_smul_right,
    Matrix.sub_mulVec,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  rw [ha]
  linarith

/-- The true conjugate queried direction's old-coordinate curvature is
exactly its actual segment drift minus its genuine replay-image error.
Use: S images have zero replay error, while D images retain the proven
quadratic native error; both give the same incoming first-order formula.
Article: main_krylov, thm:local(a), true conjugacy/drift identity.
Proof: the actual nonsingular observed conjugacy solve annihilates the
real image. Symmetry moves its actual old segment across the pairing;
subtract the real image error and collect the genuine current drift. -/
theorem lastLaunch_conjugate_curvature (s y : Fin p → E) (g : E)
    (hC : IsUnit (crossGram y s).det) (A B : E →L[ℝ] E)
    (hB : B.toLinearMap.IsSymmetric) (i : Fin p) :
    let d := conjugacyDirection s y g
    inner ℝ (s i) (A d)=inner ℝ (s i) ((A-B) d)-inner ℝ (y i-B (s i)) d := by
  let d := conjugacyDirection s y g
  have hconj : inner ℝ (y i) d=0 := congrFun (conjugacyDirection_conjugate s y g hC) i
  have hs : inner ℝ (B (s i)) d=inner ℝ (s i) (B d) := hB (s i) d
  dsimp only
  rw [_root_.sub_apply,inner_sub_right,inner_sub_left,hconj,zero_sub,sub_neg_eq_add]
  linarith

end
end krylov.OneGradient
