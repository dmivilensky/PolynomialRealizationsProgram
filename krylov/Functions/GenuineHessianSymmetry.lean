import krylov.Functions.ObjectiveCoordinates
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
Article: main_krylov, thm:Htransfer and thm:Fexact, actual Hessian symmetry.
Use: recover symmetric Hessians and symmetric third-derivative slices from
the original real objective and its genuine successive derivatives.
Source: Schwarz's theorem, mathlib second_derivative_symmetric_of_eventually,
and differentiation of the resulting actual symmetric bilinear identities.
-/

namespace krylov.Functions
noncomputable section
open Filter Set Metric Topology
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A true derivative of the actual objective gradient is symmetric throughout the open metric domain.
Article: main_krylov, thm:Htransfer, actual Hessian symmetry.
Proof: apply Schwarz to the original scalar objective, whose actual first
derivative is the Riesz functional of its actual gradient. -/
theorem genuine_hessian_symmetric (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) {r : ℝ}
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (z : E) (hz : ‖T z‖ < r) : (H z).toLinearMap.IsSymmetric := by
  have hnb : ∀ᶠ y in 𝓝 z, ‖T y‖ < r :=
    (isOpen_lt (T.continuous.norm) continuous_const).mem_nhds hz
  have hevent : ∀ᶠ y in 𝓝 z, HasFDerivAt f (innerSL ℝ (G y)) y :=
    hnb.mono (fun y hy => hF y hy.le)
  have hDG : HasFDerivAt (fun y => innerSL ℝ (G y)) ((innerSL ℝ).comp (H z)) z :=
    (innerSL ℝ).hasFDerivAt.comp z (hG z hz.le)
  intro a b
  have hs := second_derivative_symmetric_of_eventually hevent hDG a b
  change inner ℝ (H z a) b = inner ℝ (H z b) a at hs
  exact hs.trans (real_inner_comm _ _)

/-- Every actual third-derivative Hessian slice is symmetric, with no symmetry field postulated.
Article: main_krylov, thm:Htransfer, genuine compatible tensor slices.
Proof: the true Hessians are symmetric in a neighborhood by Schwarz.
Differentiate that actual identity along the given physical direction. -/
theorem genuine_third_slice_symmetric (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0) {r : ℝ} (hr : 0 < r)
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (v : E) : (D v).toLinearMap.IsSymmetric := by
  have hline : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hd : HasDerivAt (fun t : ℝ => H (t • v)) (D v) 0 := by
    have hd' : HasFDerivAt H D ((0 : ℝ) • v) := by simpa only [zero_smul] using hD
    exact hd'.comp_hasDerivAt 0 hline
  have hnb : ∀ᶠ t : ℝ in 𝓝 0, ‖T (t • v)‖ < r := by
    have hc : Continuous (fun t : ℝ => ‖T (t • v)‖) := by fun_prop
    have hmem : (0 : ℝ) ∈ {t : ℝ | ‖T (t • v)‖ < r} := by
      simpa only [Set.mem_ofPred_eq, zero_smul, map_zero, norm_zero] using hr
    exact (isOpen_lt hc continuous_const).mem_nhds hmem
  intro a b
  change inner ℝ (D v a) b = inner ℝ a (D v b)
  have hd₁ := (hd.clm_apply (hasDerivAt_const (0 : ℝ) a)).inner ℝ (hasDerivAt_const (0 : ℝ) b)
  have hd₂ := (hasDerivAt_const (0 : ℝ) a).inner ℝ (hd.clm_apply (hasDerivAt_const (0 : ℝ) b))
  have hzero : (fun t : ℝ => inner ℝ (H (t • v) a) b - inner ℝ a (H (t • v) b)) =ᶠ[𝓝 0]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hnb] with t ht
    exact sub_eq_zero.mpr (genuine_hessian_symmetric T f G H hF hG (t • v) ht a b)
  have hz := (hd₁.sub hd₂).unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hzero)
  simpa only [map_zero, inner_zero_right, inner_zero_left, add_zero, zero_add, sub_eq_zero] using hz

end
end krylov.Functions
