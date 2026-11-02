import jacobi.GelfandLevitan.KernelAction

/-!
Article: jacobi, Proposition C.2.
Continuous GL candidates live on the actual closed triangle 0<=s<=t<=1/2.
Clipping only the second coordinate extends each candidate continuously
to the physical square without imposing any extra condition on it.
This makes the pointwise uniqueness theorem apply to every original
continuous triangular candidate, including its boundary values.
Use: states existence and uniqueness for precisely the source domain, rather than assuming an arbitrary candidate has an extension to the whole square.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology

/-- The genuine closed physical triangle of the original GL equation.
Use: states existence and uniqueness for precisely the source domain, rather than assuming an arbitrary candidate has an extension to the whole square.
Article: jacobi, Proposition C.2.
-/
abbrev Triangle := {p:HalfInterval×HalfInterval // (p.2:ℝ)≤(p.1:ℝ)}

/-- The actual continuous inclusion of the original physical triangle into its half square.
Use: restricts the constructed continuous kernel to exactly the original source GL domain.
Article: jacobi, Proposition C.2.
-/
def triangleInclusion : C(Triangle,HalfInterval×HalfInterval) :=
  ⟨Subtype.val,continuous_subtype_val⟩

/-- Continuous clipping of the second physical coordinate to the original GL triangle.
Use: extends every arbitrary continuous triangular candidate for the original row uniqueness argument without adding an extension hypothesis.
Article: jacobi, Proposition C.2.
-/
def triangleClip : C(HalfInterval×HalfInterval,Triangle) where
  toFun p := ⟨(p.1,⟨min (p.1:ℝ) (p.2:ℝ),
    ⟨le_min p.1.property.1 p.2.property.1,(min_le_right _ _).trans p.2.property.2⟩⟩),min_le_left _ _⟩
  continuous_toFun :=
    (continuous_fst.prodMk
      (((continuous_subtype_val.comp continuous_fst).min
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _)).subtype_mk _

/-- The true continuous clipping extension preserves every original physical triangle point exactly.
Use: the arbitrary triangular candidate and its genuine continuous extension have identical original GL values and endpoint data.
Article: jacobi, Proposition C.2.
Proof: the original second coordinate is already below the first, so the true minimum is that original coordinate; subtype and product extensionality preserve both coordinates. -/
theorem triangleClip_inclusion (p : Triangle) : triangleClip (triangleInclusion p)=p := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact min_eq_right p.property

/-- Including a genuine half-domain coordinate in the original unit interval and clamping it back preserves it exactly.
Use: pointwise row uniqueness on the shared original interval gives equality at every actual GL triangle coordinate.
Article: jacobi, Proposition C.2.
Proof: the original coordinate is already at most one half, so its actual clamp is the coordinate itself. -/
theorem halfClamp_halfInclusion (s : HalfInterval) : halfClamp (halfInclusion s)=s := by
  apply Subtype.ext
  exact min_eq_left s.property.2

end
end jacobi.GelfandLevitan
