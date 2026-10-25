import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Article: Appendix C, one-sided slope bounds at the switching points.
Use: extend a right differentiable source by its tangent on the left. This
supplies an ordinary derivative while preserving every actual right-hand value.
-/
noncomputable section
namespace polyak.Regularity
open Set Filter
open scoped Topology

def rightExtension (f : ℝ → ℝ) (v T : ℝ) (t : ℝ) : ℝ :=
  if t<T then f T+v*(t-T) else f t

theorem rightExtension_eq {f : ℝ → ℝ} {v T t : ℝ} (ht : T≤t) :
    rightExtension f v T t=f t := by
  simp only [rightExtension,ite_eq_right (not_lt.mpr ht)]

theorem rightExtension_hasDerivAt {f : ℝ → ℝ} {v T : ℝ}
    (hd : HasDerivWithinAt f v (Ici T) T) :
    HasDerivAt (rightExtension f v T) v T := by
  have hleft : HasDerivWithinAt (rightExtension f v T) v (Iic T) T := by
    have ha : HasDerivAt (fun t : ℝ => f T+v*(t-T)) v T := by
      convert! (hasDerivAt_const T (f T)).add
        (((hasDerivAt_id T).sub_const T).const_mul v) using 1
      simp
    apply ha.hasDerivWithinAt.congr
    · intro t ht
      by_cases hlt : t<T
      · simp only [rightExtension,ite_eq_left hlt]
      · have he : t=T := le_antisymm ht (le_of_not_gt hlt)
        subst t
        simp [rightExtension]
    · simp [rightExtension]
  have hright : HasDerivWithinAt (rightExtension f v T) v (Ici T) T := by
    exact hd.congr (fun _ ht => rightExtension_eq ht) (rightExtension_eq le_rfl)
  simpa only [Iic_union_Ici,hasDerivWithinAt_univ] using hleft.union hright

theorem exists_right_derivative_extension {f : ℝ → ℝ} {v T : ℝ}
    (hd : HasDerivWithinAt f v (Ici T) T) :
    ∃ g : ℝ → ℝ,HasDerivAt g v T ∧ g T=f T ∧ g=ᶠ[𝓝[≥] T] f := by
  refine ⟨rightExtension f v T,rightExtension_hasDerivAt hd,rightExtension_eq le_rfl,?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact rightExtension_eq ht

end polyak.Regularity
