import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Article: chebyshev1, Theorem E.3.
A finite right limit rules out a positive logarithmically nonintegrable derivative.
Use: `chebyshev1.Analysis.no_positive_logarithmic_derivative` feeds
`chebyshev1.Analysis.singular_sqrt_unique` (Uniqueness of the non-logarithmic branch at a
square-root singular endpoint).
Proof chain: `chebyshev1.SineJacobi.sineProfile_unique` — chebyshev1, Theorem E.3; Hard-edge
recurrence, singular ODE, uniqueness and endpoint limits.
Source: mathlib, Mathlib.Analysis.Calculus.Deriv.MeanValue,
Mathlib.Analysis.SpecialFunctions.Log.Deriv — exclusion of a logarithmically divergent derivative at
a finite boundary value. The needed form is proved here.
-/
namespace chebyshev1.Analysis
noncomputable section
open Real Set Filter Topology

/--
A finite right limit rules out a positive logarithmically nonintegrable derivative.

The precise assertion is `False`.

Use: `chebyshev1.Analysis.singular_sqrt_unique` uses this assertion to establish pointwise
equality on the specified domain: `EqOn g f (Ioo 0 1)`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.sineProfile_unique`.

Source: mathlib, Mathlib.Analysis.Calculus.Deriv.MeanValue,
Mathlib.Analysis.SpecialFunctions.Log.Deriv — exclusion of a logarithmically divergent
derivative at a finite boundary value.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem no_positive_logarithmic_derivative {u u' : ℝ → ℝ} {b A l : ℝ}
    (hb : 0 < b) (hA : 0 < A)
    (hu : ∀ t ∈ Ioo 0 b, HasDerivAt u (u' t) t)
    (hd : ∀ t ∈ Ioo 0 b, A/t ≤ u' t)
    (hl : Tendsto u (𝓝[>] 0) (𝓝 l)) : False := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let v : ℝ → ℝ := fun t => u t-A*log t
  have hv : ∀ t ∈ Ioo 0 b, HasDerivAt v (u' t-A/t) t := by
    intro t ht
    convert (hu t ht).sub ((hasDerivAt_log ht.1.ne').const_mul A) using 1 ;
      simp [div_eq_mul_inv]
  have hm : MonotoneOn v (Ioo 0 b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 b)
    · exact fun t ht => (hv t ht).continuousAt.continuousWithinAt
    · simpa only [interior_Ioo] using
        (show DifferentiableOn ℝ v (Ioo 0 b) from
          fun t ht => (hv t ht).differentiableAt.differentiableWithinAt)
    · intro t ht
      rw [(hv t (by simpa using ht)).deriv]
      exact sub_nonneg.mpr (hd t (by simpa using ht))
  have hu_lower : ∀ᶠ t in 𝓝[>] (0:ℝ), l-1 < u t :=
    hl.eventually_const_lt (by linarith)
  have hlog : ∀ᶠ t in 𝓝[>] (0:ℝ), log t < (l-1-v (b/2))/A :=
    tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot _)
  have he : ∀ᶠ t in 𝓝[>] (0:ℝ), False := by
    filter_upwards [Ioo_mem_nhdsGT (half_pos hb), hu_lower, hlog] with t ht hlu hlt
    have hmon := hm ⟨ht.1, ht.2.trans (by linarith : b/2 < b)⟩
      ⟨half_pos hb, by linarith⟩ ht.2.le
    have hlt' := (lt_div_iff₀ hA).mp hlt
    dsimp [v] at hmon hlt'
    nlinarith
  exact he.exists.choose_spec

end
end chebyshev1.Analysis
