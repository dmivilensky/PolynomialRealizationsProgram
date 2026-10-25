import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.OrderClosed

/-!
Article: chebyshev1, Theorem 5.2.
A positive concave function has slope bounded by the two endpoint secants.
Use: `chebyshev1.Analysis.positive_concave_slope` feeds
`chebyshev1.SineJacobi.sineProfile_slope_bounds` (sine Profile slope bounds).
Proof chain: `chebyshev1.SineJacobi.sineEnergy_decimal` — chebyshev1, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
Source: mathlib, Mathlib.Analysis.Calculus.Deriv.MeanValue, Mathlib.Topology.Order.OrderClosed —
endpoint secant bounds for a positive concave function. The needed form is proved here.
-/
namespace chebyshev1.Analysis
noncomputable section
open Set Filter Topology

/--
A positive concave function has slope bounded by the two endpoint secants. No endpoint
regularity is required.

The stated quantitative bound `-f t/(1-t) ≤ f' t ∧ f' t ≤ f t/t`.

Use: `chebyshev1.SineJacobi.sineProfile_slope_bounds` uses this bound to establish the
stated quantitative bound `-sineProfile t/(1-t) ≤ sineProfile₁ t ∧ sineProfile₁ t ≤ sineProfile
t/t`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.sineEnergy_decimal`.

Source: mathlib, Mathlib.Analysis.Calculus.Deriv.MeanValue, Mathlib.Topology.Order.OrderClosed
— endpoint secant bounds for a positive concave function.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection.
-/
theorem positive_concave_slope {f f' f'' : ℝ → ℝ}
    (hf : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt f' (f'' x) x)
    (hp : ∀ x ∈ Ioo (0:ℝ) 1, 0 < f x)
    (hn : ∀ x ∈ Ioo (0:ℝ) 1, f'' x ≤ 0)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    -f t/(1-t) ≤ f' t ∧ f' t ≤ f t/t := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  have hm : AntitoneOn f' (Ioo (0:ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
    · exact fun x hx => (hf' x hx).continuousAt.continuousWithinAt
    · simpa only [interior_Ioo] using
        (show DifferentiableOn ℝ f' (Ioo (0:ℝ) 1) from
          fun x hx => (hf' x hx).differentiableAt.differentiableWithinAt)
    · intro x hx
      rw [(hf' x (by simpa using hx)).deriv]
      exact hn x (by simpa using hx)
  have hleft (u : ℝ) (hu : u ∈ Ioo (0:ℝ) t) : f' t*(t-u) ≤ f t := by
    have hs := (convex_Icc u t).mul_sub_le_image_sub_of_le_deriv
      (fun x hx => (hf x ⟨hu.1.trans_le hx.1, hx.2.trans_lt ht.2⟩).continuousAt.continuousWithinAt)
      (fun x hx => by
        have hx' : x ∈ Icc u t := interior_subset hx
        exact (hf x ⟨hu.1.trans_le hx'.1, hx'.2.trans_lt ht.2⟩).differentiableAt.differentiableWithinAt)
      (C := f' t)
      (fun x hx => by
        have hx' : x ∈ Icc u t := interior_subset hx
        rw [(hf x ⟨hu.1.trans_le hx'.1, hx'.2.trans_lt ht.2⟩).deriv]
        exact hm ⟨hu.1.trans_le hx'.1, hx'.2.trans_lt ht.2⟩ ht hx'.2)
      u (left_mem_Icc.mpr hu.2.le) t (right_mem_Icc.mpr hu.2.le) hu.2.le
    linarith [hp u ⟨hu.1, hu.2.trans ht.2⟩]
  have hright (u : ℝ) (hu : u ∈ Ioo t (1:ℝ)) : f' t*(u-t) ≥ -f t := by
    have hs := (convex_Icc t u).image_sub_le_mul_sub_of_deriv_le
      (fun x hx => (hf x ⟨ht.1.trans_le hx.1, hx.2.trans_lt hu.2⟩).continuousAt.continuousWithinAt)
      (fun x hx => by
        have hx' : x ∈ Icc t u := interior_subset hx
        exact (hf x ⟨ht.1.trans_le hx'.1, hx'.2.trans_lt hu.2⟩).differentiableAt.differentiableWithinAt)
      (C := f' t)
      (fun x hx => by
        have hx' : x ∈ Icc t u := interior_subset hx
        rw [(hf x ⟨ht.1.trans_le hx'.1, hx'.2.trans_lt hu.2⟩).deriv]
        exact hm ht ⟨ht.1.trans_le hx'.1, hx'.2.trans_lt hu.2⟩ hx'.1)
      t (left_mem_Icc.mpr hu.1.le) u (right_mem_Icc.mpr hu.1.le) hu.1.le
    linarith [hp u ⟨ht.1.trans hu.1, hu.2⟩]
  have hl : f' t*t ≤ f t := by
    apply le_of_tendsto (f := fun u : ℝ => f' t*(t-u)) (x := 𝓝[>] 0)
    · simpa using (tendsto_const_nhds (x := f' t)).mul
        ((tendsto_const_nhds (x := t)).sub
          (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id : Tendsto (fun u : ℝ => u) (𝓝 0) (𝓝 0))))
    · filter_upwards [Ioo_mem_nhdsGT ht.1] with u hu
      exact hleft u hu
  have hr : -f t ≤ f' t*(1-t) := by
    apply ge_of_tendsto (f := fun u : ℝ => f' t*(u-t)) (x := 𝓝[<] 1)
    · simpa using (tendsto_const_nhds (x := f' t)).mul
        ((tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id : Tendsto (fun u : ℝ => u) (𝓝 1) (𝓝 1))).sub_const t)
    · filter_upwards [Ioo_mem_nhdsLT ht.2] with u hu
      exact hright u hu
  exact ⟨(div_le_iff₀ (sub_pos.mpr ht.2)).mpr hr, (le_div_iff₀ ht.1).mpr hl⟩

end
end chebyshev1.Analysis
