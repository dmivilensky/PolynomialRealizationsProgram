import krylov.XR.MemoryObservations
import krylov.Functions.ValueDefectSecondKernel

/-!
Article: main_krylov, cor:xrF and apH:impl, genuine value-gate estimates.
Use: bound the actual scalar endpoint defect under only a Lipschitz
Hessian. The bound retains its cubic dependence on the observed step,
including arbitrarily short steps. Source: the genuine second-derivative
Peano kernel, with the Hessian frozen at the segment start.
-/

namespace krylov.XR
noncomputable section
open Set krylov.Functions
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A Lipschitz Hessian gives a true cubic endpoint-value defect without
requiring a third derivative. The harmless factor 1/2 suffices for the
eventual exact value gates. -/
theorem segmentValueDefect_lipschitz_hessian (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (a s : E) (L : ℝ)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt f (innerSL ℝ (G (a + t • s))) (a + t • s))
    (hG : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt G (H (a + t • s)) (a + t • s))
    (hC : ContinuousOn (fun t : ℝ => H (a + t • s)) (Icc 0 1))
    (hLip : ∀ t ∈ Icc (0 : ℝ) 1, ‖H (a + t • s) - H a‖ ≤ L * ‖s‖) :
    |segmentValueDefect f (fun x => innerSL ℝ (G x)) a s| ≤ L * ‖s‖ ^ 3 / 2 := by
  let f₀ := fun t : ℝ => f (a + t • s)
  let f₁ := fun t : ℝ => inner ℝ (G (a + t • s)) s
  let f₂ := fun t : ℝ => inner ℝ (H (a + t • s) s) s
  have hd₁ t (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f₀ (f₁ t) t :=
    segment_hasDerivAt f (fun x => innerSL ℝ (G x)) a s t (hF t ht)
  have hd₂ t (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f₁ (f₂ t) t := by
    simpa only [f₁, f₂, inner_zero_right, zero_add] using
      (segment_hasDerivAt G H a s t (hG t ht)).inner ℝ (hasDerivAt_const t s)
  have hc₂ : ContinuousOn f₂ (Icc 0 1) :=
    (hC.clm_apply continuousOn_const).inner continuousOn_const
  have hh t (ht : t ∈ Icc (0 : ℝ) 1) :
      |f₂ t - (inner ℝ (H a s) s + t * 0)| ≤ L * ‖s‖ ^ 3 := by
    have he : f₂ t - (inner ℝ (H a s) s + t * 0) = inner ℝ ((H (a + t • s) - H a) s) s := by
      simp only [f₂, sub_apply, inner_sub_left, mul_zero, add_zero]
    rw [he]
    have hb := (norm_inner_le_norm (𝕜 := ℝ) ((H (a + t • s) - H a) s) s).trans
      (mul_le_mul_of_nonneg_right ((H (a + t • s) - H a).le_opNorm s) (norm_nonneg s))
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right (hLip t ht) (sq_nonneg ‖s‖)])
  have hb := trapezoid_second_affine_remainder f₀ f₁ f₂ hd₁ hd₂ hc₂
    (inner ℝ (H a s) s) 0 (L * ‖s‖ ^ 3) hh
  simpa only [trapezoidDefect, f₀, f₁, zero_smul, add_zero, one_smul, zero_div, add_zero,
    segmentValueDefect, innerSL_apply_apply] using hb

/-- A genuine stored scalar defect is exactly its endpoint trapezoid
defect; cached endpoint gradients and values supply the dictionary. -/
theorem PairFaithful.valueDefect_eq (f : E → ℝ) (G : E → E) (x : E)
    (a : PairObservation E) (ha : PairFaithful f G x a) :
    a.valueDefect = segmentValueDefect f (fun z => innerSL ℝ (G z)) a.anchor a.step := by
  rw [ha.2.1, ha.1]
  simp only [segmentValueDefect, innerSL_apply_apply, inner_sub_right]
  rw [real_inner_comm a.step (G (a.anchor + a.step)), real_inner_comm a.step (G a.anchor)]
  ring

/-- Actual local Lipschitz-Hessian source data supply the complete true
cubic defect bound on every retained segment in a convex source set. -/
theorem segmentValueDefect_on_lipschitz_set (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (S : Set E) (hS : Convex ℝ S) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H S)
    (hF : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ S, HasFDerivAt G (H z) z)
    (a s : E) (ha : a ∈ S) (hb : a + s ∈ S) :
    |segmentValueDefect f (fun z => innerSL ℝ (G z)) a s| ≤ (L : ℝ) * ‖s‖ ^ 3 / 2 := by
  have hsegment t (ht : t ∈ Icc (0 : ℝ) 1) : a + t • s ∈ S := by
    have hh := hS.segment_subset ha hb (lineMap_mem_segment ℝ a (a + s) ht)
    have he : AffineMap.lineMap a (a + s) t = a + t • s := by
      rw [AffineMap.lineMap_apply_module]
      module
    rwa [he] at hh
  apply segmentValueDefect_lipschitz_hessian f G H a s L
    (fun t ht => hF _ (hsegment t ht)) (fun t ht => hG _ (hsegment t ht))
  · exact hLip.continuousOn.comp (by fun_prop) hsegment
  · intro t ht
    have hh := hLip.norm_sub_le (hsegment t ht) ha
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hh
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right ht.2 (norm_nonneg s), L.coe_nonneg])

end
end krylov.XR
