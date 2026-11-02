import krylov.Functions.SegmentTrapezoid
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Article: main_krylov, thm:Fexact, arbitrary anchors and arbitrary splits.
Use: assemble the genuine function-value correction and its sharp remainder,
including the displacement from the observed segment to the requested anchor.
Source: Appendix G, the scalar FTC and the previously proved Peano kernels.
-/

/-!
Article: krylov, Lemma E.13 [thm:Fexact].

The true scalar-function trapezoid remainder has exactly the printed constants for every
anchor/split. The diagonal fourth-derivative version and cubic exactness use genuine
derivatives.
The diagonal spectral norm of the scalar symmetric tensor is converted to the needed mixed
bound by the proved Banach identity; the convex segment/anchor domain is retained.
-/

namespace krylov.Functions
noncomputable section
open Set MeasureTheory
open scoped NNReal

/-- Taylor's first-order remainder on the unit segment, with the exact one-half constant.
Article: main_krylov, thm:Fexact, the anchor-displacement term.
Proof: integrate the actual derivative after subtracting its initial value. -/
theorem scalar_unit_taylor_remainder (g g₁ : ℝ → ℝ)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (g₁ t) t)
    (hc : ContinuousOn g₁ (Icc 0 1)) (C : ℝ)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, |g₁ t - g₁ 0| ≤ C * t) :
    |g 1 - g 0 - g₁ 0| ≤ C / 2 := by
  have hi : IntervalIntegrable (fun t : ℝ => g₁ t - g₁ 0) volume 0 1 :=
    (hc.sub continuousOn_const).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hd' t (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => g t - t * g₁ 0) (g₁ t - g₁ 0) t := by
    convert! (hd t ht).sub ((hasDerivAt_id t).mul_const (g₁ 0)) using 1
    simp only [one_mul]
  have he : (∫ t in (0 : ℝ)..1, g₁ t - g₁ 0) = g 1 - g 0 - g₁ 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hd' t (by simpa using ht)) hi
    simp only [one_mul, zero_mul, sub_zero] at h
    linarith only [h]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun t : ℝ => g₁ t - g₁ 0) (g := fun t : ℝ => C * t)
    (Filter.Eventually.of_forall fun t ht => by
      simpa only [Real.norm_eq_abs] using hb t ⟨ht.1.le, ht.2⟩)
    ((by fun_prop : Continuous (fun t : ℝ => C * t)).intervalIntegrable 0 1)
  rw [he, Real.norm_eq_abs, intervalIntegral.integral_const_mul,
    integral_id] at hbound
  norm_num at hbound
  simpa only [div_eq_mul_inv, one_mul] using hbound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ordinary Lipschitz bound on the third variation, expressed on its actual arguments.
Article: main_krylov, thm:Fexact. This is the multilinear operator-norm condition,
written without choosing a representation of the finite-dimensional tensor norm. -/
def ThirdVariationLipschitzOn
    (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (L : ℝ≥0) (S : Set E) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ u v w,
    |T p u v w - T q u v w| ≤ (L : ℝ) * ‖p - q‖ * ‖u‖ * ‖v‖ * ‖w‖

/-- A genuine Hessian diagonal has the sharp quadratic Taylor bound between any two anchors.
Article: main_krylov, thm:Fexact, the term L3/2 times the squared anchor displacement.
Proof: differentiate the actual Hessian along the anchor segment and apply scalar FTC. -/
theorem hessian_diagonal_taylor_remainder
    (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (S : Set E) (hS : Convex ℝ S)
    (hT : ∀ z ∈ S, HasFDerivAt H (T z) z)
    (L : ℝ≥0) (hLip : ThirdVariationLipschitzOn T L S)
    (b x s : E) (hb : b ∈ S) (hx : x ∈ S) :
    |H x s s - H b s s - T b (x - b) s s| ≤
      (L : ℝ) / 2 * ‖x - b‖ ^ 2 * ‖s‖ ^ 2 := by
  let u := x - b
  have hp t (ht : t ∈ Icc (0 : ℝ) 1) : b + t • u ∈ S := by
    apply hS.add_smul_mem hb _ ht
    simpa only [u, add_sub_cancel] using hx
  let g := fun t : ℝ => H (b + t • u) s s
  let g₁ := fun t : ℝ => T (b + t • u) u s s
  have hd t (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g (g₁ t) t := by
    simpa only [map_zero, add_zero] using
      ((segment_hasDerivAt H T b u t (hT _ (hp t ht))).clm_apply
        (hasDerivAt_const t s)).clm_apply (hasDerivAt_const t s)
  let C : ℝ := (L : ℝ) * ‖u‖ ^ 2 * ‖s‖ ^ 2
  have hC : 0 ≤ C := by positivity
  have hl : LipschitzOnWith (Real.toNNReal C) g₁ (Icc 0 1) := by
    apply LipschitzOnWith.of_dist_le'
    intro t ht v hv
    have he : (b + t • u) - (b + v • u) = (t - v) • u := by rw [sub_smul]; abel
    calc
      dist (g₁ t) (g₁ v) = |g₁ t - g₁ v| := Real.dist_eq _ _
      _ ≤ (L : ℝ) * ‖(b + t • u) - (b + v • u)‖ * ‖u‖ * ‖s‖ * ‖s‖ :=
        hLip _ (hp t ht) _ (hp v hv) u s s
      _ = C * dist t v := by
        rw [he, norm_smul, Real.norm_eq_abs, Real.dist_eq]
        dsimp [C]
        ring
  have hdev t (ht : t ∈ Icc (0 : ℝ) 1) : |g₁ t - g₁ 0| ≤ C * t := by
    have h := hl.norm_sub_le ht (by simp : (0 : ℝ) ∈ Icc 0 1)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1,
      Real.coe_toNNReal _ hC] using h
  have h := scalar_unit_taylor_remainder g g₁ hd hl.continuousOn C hdev
  convert! h using 1
  · simp only [g, g₁, u, one_smul, zero_smul, add_zero, add_sub_cancel]
  · dsimp only [C, u]; ring

/-- The full function-value diagonal remainder for an arbitrary anchor and split.
Article: main_krylov, thm:Fexact, equation (trapezoid-remainder).
Proof: combine the exact 1/12 endpoint Peano kernel, the exact 1/24 defect
kernel, and the independently proved quadratic Hessian Taylor remainder. -/
theorem anchored_trapezoid_remainder (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (S : Set E) (hS : Convex ℝ S)
    (hD : ∀ z ∈ S, HasFDerivAt f (D z) z)
    (hH : ∀ z ∈ S, HasFDerivAt D (H z) z)
    (hT : ∀ z ∈ S, HasFDerivAt H (T z) z)
    (L : ℝ≥0) (hLip : ThirdVariationLipschitzOn T L S)
    (a s x : E) (ha : a ∈ S) (hb : a + s ∈ S) (hx : x ∈ S) (l : ℝ) :
    let δ := f (a + s) - f a - (D a s + D (a + s) s) / 2
    let w := x - (a + (1 / 2 : ℝ) • s) - l • s
    ∃ R : ℝ,
      (D (a + s) - D a) s - 12 * l * δ - H x s s =
        -T (a + s) w s s + R ∧
      |R| ≤ (L : ℝ) * ((1 / 12 + 1 / 2 * |l - 1 / 2|) * ‖s‖ ^ 4 +
        1 / 2 * ‖x - (a + s)‖ ^ 2 * ‖s‖ ^ 2) := by
  dsimp only
  let b := a + s
  let δ := f b - f a - (D a s + D b s) / 2
  let w := x - (a + (1 / 2 : ℝ) • s) - l • s
  have hp t (ht : t ∈ Icc (0 : ℝ) 1) : a + t • s ∈ S := hS.add_smul_mem ha hb ht
  have he := segment_trapezoid_endpoint_bounds f D H T a s
    (fun t ht => hD _ (hp t ht)) (fun t ht => hH _ (hp t ht))
    (fun t ht => hT _ (hp t ht)) L (fun t ht v hv => by
      convert! hLip _ (hp t ht) _ (hp v hv) s s s using 1
      ring)
  change |δ + T b s s s / 12| ≤ (L : ℝ) * ‖s‖ ^ 4 / 24 ∧
    |(D b - D a) s - 6 * δ - H b s s| ≤ (L : ℝ) * ‖s‖ ^ 4 / 12 at he
  have ht := hessian_diagonal_taylor_remainder H T S hS hT L hLip b x s hb hx
  let e₁ := (D b - D a) s - 6 * δ - H b s s
  let e₂ := δ + T b s s s / 12
  let e₃ := H x s s - H b s s - T b (x - b) s s
  refine ⟨e₁ - 12 * (l - 1 / 2) * e₂ - e₃, ?_, ?_⟩
  · have hw : w = (x - b) + (1 / 2 - l) • s := by
      dsimp only [w, b]
      module
    rw [show x - (a + (1 / 2 : ℝ) • s) - l • s = w from rfl, hw]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    dsimp only [e₁, e₂, e₃]
    ring
  · have hbound : |e₁ - 12 * (l - 1 / 2) * e₂ - e₃| ≤
        |e₁| + 12 * |l - 1 / 2| * |e₂| + |e₃| := by
      calc
        _ ≤ |e₁ - 12 * (l - 1 / 2) * e₂| + |e₃| := abs_sub _ _
        _ ≤ |e₁| + |12 * (l - 1 / 2) * e₂| + |e₃| :=
          add_le_add (abs_sub _ _) le_rfl
        _ = _ := by rw [abs_mul, abs_mul]; norm_num
    calc
      _ ≤ |e₁| + 12 * |l - 1 / 2| * |e₂| + |e₃| := hbound
      _ ≤ (L : ℝ) * ‖s‖ ^ 4 / 12 +
          12 * |l - 1 / 2| * ((L : ℝ) * ‖s‖ ^ 4 / 24) +
          (L : ℝ) / 2 * ‖x - b‖ ^ 2 * ‖s‖ ^ 2 := by
        exact add_le_add (add_le_add he.2
          (mul_le_mul_of_nonneg_left he.1 (by positivity))) ht
      _ = _ := by dsimp only [b]; ring

end
end krylov.Functions
