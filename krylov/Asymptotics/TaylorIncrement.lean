import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
Article: main_krylov, lower bound in thm:limit, local consistency.
Use: a quadratic increment error from a Lipschitz derivative on the actual
compact interval. The proof is a direct mean-value estimate of the genuine
Taylor remainder; it does not assume a discretization-error certificate.
Source: mathlib's vector-valued mean value inequality.
-/
namespace krylov.Asymptotics
noncomputable section
open Set

/-- A first-order Taylor increment has a quadratic error under a genuine
Lipschitz bound on the derivative. A non-sharp constant suffices for recovery. -/
theorem taylor_increment_bound_within {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f d : ℝ → E} {a b L : ℝ} (hab : a ≤ b) (hL : 0 ≤ L)
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (d x) (Icc a b) x)
    (hLip : ∀ x ∈ Icc a b, ‖d x - d a‖ ≤ L * |x - a|) :
    ‖f b - f a - (b - a) • d a‖ ≤ L * (b - a) ^ 2 := by
  let F : ℝ → E := fun x ↦ f x - f a - (x - a) • d a
  have hF (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivWithinAt F (d x - d a) (Icc a b) x := by
    convert ((hd x hx).sub_const (f a)).sub ((((hasDerivAt_id x).sub_const a).smul_const (d a)).hasDerivWithinAt) using 1
    · rfl
    · simp only [one_smul]
  have hbound (x : ℝ) (hx : x ∈ Icc a b) : ‖d x - d a‖ ≤ L * (b - a) := by
    apply (hLip x hx).trans
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 a) hL
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hF hbound (convex_Icc a b)
    (show a ∈ Icc a b from ⟨le_rfl, hab⟩) (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
  simpa only [F, sub_self, zero_smul, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hab), pow_two, mul_assoc] using h

/-- The ordinary-derivative specialization of the same genuine increment bound. -/
theorem taylor_increment_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f d : ℝ → E} {a b L : ℝ} (hab : a ≤ b) (hL : 0 ≤ L)
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (d x) x)
    (hLip : ∀ x ∈ Icc a b, ‖d x - d a‖ ≤ L * |x - a|) :
    ‖f b - f a - (b - a) • d a‖ ≤ L * (b - a) ^ 2 :=
  taylor_increment_bound_within hab hL (fun x hx ↦ (hd x hx).hasDerivWithinAt) hLip

end
end krylov.Asymptotics
