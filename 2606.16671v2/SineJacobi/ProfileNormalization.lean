import «2606.16671v2».SineJacobi.GreenLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Article: 2606.16671v2, Theorem 5.2.
The normalization constant I_sin in Theorem 5.1 is exactly 1/π.
Use: `«2606.16671v2».SineJacobi.sineDensity_integral` feeds `«2610.05164v2».SineJacobi.phi_integral`
(phi integral).
Proof chain: `«2606.16671v2».SineJacobi.sineEnergy_ge_one` — 2606.16671v2, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Real Set Filter Topology MeasureTheory
open scoped BigOperators

/--
Defines `sineIntegral` of type `ℝ` by `∫ t in (0:ℝ)..1, profileProduct t`.

Use: `«2606.16671v2».SineJacobi.greenProfile_integral_limit` uses this definition to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ => ∫
t in (0:ℝ)..1, greenProfile N t) atTop (𝓝 sineIntegral)`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.
-/
def sineIntegral : ℝ := ∫ t in (0:ℝ)..1, profileProduct t
/--
Defines `sineDensity` of type `ℝ` by `Real.pi*profileProduct t`.

Use: `«2606.16671v2».SineJacobi.sineDensity_eq_normalized` rewrites with this definition to
establish exact identity `sineDensity t = profileProduct t/sineIntegral`.

Article: 2606.16671v2, Theorem 5.1 via
`«2606.16671v2».SineJacobi.diagonalProfile_eLpNorm_limit`.
-/
def sineDensity (t : ℝ) : ℝ := Real.pi*profileProduct t
/--
Defines `sineEnergy` of type `ℝ` by `∫ t in (0:ℝ)..1, sineDensity t^2`.

Use: `«2606.16671v2».SineJacobi.diagonalProfile_square_integral_limit` uses this definition to
establish convergence along the specified source filter to the specified limit: `Tendsto (fun N
: ℕ => ∫ t in (0:ℝ)..1, diagonalProfile N t^2) atTop (𝓝 sineEnergy)`.

Article: 2606.16671v2, Theorem 5.2.
-/
def sineEnergy : ℝ := ∫ t in (0:ℝ)..1, sineDensity t^2

/--
Exact identity `(∫ t in (0:ℝ)..1, greenProfile N t) = 1/Real.pi`.

Use: `«2606.16671v2».SineJacobi.sineIntegral_eq` uses this identity to establish the identity
`sineIntegral = 1/Real.pi`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem greenProfile_integral (N : ℕ) (hN : 0 < N) :
    (∫ t in (0:ℝ)..1, greenProfile N t) = 1/Real.pi := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : greenProfile N = fun t => (1/(Real.pi*(N:ℝ)))*
      «2606.16671v2».Analysis.uniformStep N (greenWeight N) t := by
    funext t; unfold greenProfile «2606.16671v2».Analysis.uniformStep; ring
  rw [he, intervalIntegral.integral_const_mul,
    «2606.16671v2».Analysis.uniformStep_integral N (greenWeight N) hN,
    greenWeight_sum ⟨1,2,by norm_num,by norm_num⟩ N hN]
  field_simp [hn, pi_pos.ne']

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ => ∫
t in (0:ℝ)..1, greenProfile N t) atTop (𝓝 sineIntegral)`.

Use: `«2606.16671v2».SineJacobi.sineIntegral_eq` uses this limit to establish the identity
`sineIntegral = 1/Real.pi`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.greenProfile_measurable`,
`«2606.16671v2».SineJacobi.greenProfile_uniform_bound`,
`«2606.16671v2».SineJacobi.greenProfile_limit` with the arguments shown in the proof. Intersect
the eventual or almost-everywhere hypotheses, then prove the asserted relation at an arbitrary
point in that intersection.
-/
theorem greenProfile_integral_limit :
    Tendsto (fun N : ℕ => ∫ t in (0:ℝ)..1, greenProfile N t) atTop (𝓝 sineIntegral) := by
  -- Apply the dominated-convergence/Lp transfer after supplying the domination and
  -- pointwise-limit hypotheses.
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioo (0:ℝ) 1))
    (bound := fun _ => 9*Real.pi^3/4) (F := greenProfile) (f := profileProduct)
    (Eventually.of_forall fun N => (greenProfile_measurable N).aestronglyMeasurable)
    (show ∀ᶠ N : ℕ in atTop, ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1),
      ‖greenProfile N t‖ ≤ 9*Real.pi^3/4 from by
      filter_upwards [eventually_ge_atTop 2] with N hn
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hh := greenProfile_uniform_bound N hn ⟨ht.1.le, ht.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg hh.1]; exact hh.2)
    (integrable_const _)
    (show ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1),
      Tendsto (fun N => greenProfile N t) atTop (𝓝 (profileProduct t)) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact greenProfile_limit ht)
  simpa only [sineIntegral, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    restrict_Ioo_eq_restrict_Ioc] using h

/--
The normalization constant I_sin in Theorem 5.1 is exactly 1/π.

Exact identity `sineIntegral = 1/Real.pi`.

Use: `«2606.16671v2».SineJacobi.sineDensity_eq_normalized` rewrites with this identity to
establish exact identity `sineDensity t = profileProduct t/sineIntegral`.

Article: 2606.16671v2, Theorem 5.1.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem sineIntegral_eq : sineIntegral = 1/Real.pi := by
  have hc : Tendsto (fun N : ℕ => ∫ t in (0:ℝ)..1, greenProfile N t) atTop (𝓝 (1/Real.pi)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with N hn
    exact (greenProfile_integral N hn).symm
  exact tendsto_nhds_unique greenProfile_integral_limit hc

/--
Exact identity `(∫ t in (0:ℝ)..1, sineDensity t) = 1`.

Use: `«2606.16671v2».SineJacobi.sineEnergy_ge_one` rewrites with this identity to establish the
stated quantitative bound `1 ≤ sineEnergy`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_ge_one`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem sineDensity_integral : (∫ t in (0:ℝ)..1, sineDensity t) = 1 := by
  change (∫ t in (0:ℝ)..1, Real.pi*profileProduct t) = 1
  rw [intervalIntegral.integral_const_mul]
  change Real.pi*sineIntegral = 1
  rw [sineIntegral_eq]
  field_simp

/--
Exact identity `sineDensity t = profileProduct t/sineIntegral`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem 5.2.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.sineIntegral_eq` with the
arguments shown in the proof.
-/
theorem sineDensity_eq_normalized (t : ℝ) : sineDensity t = profileProduct t/sineIntegral := by
  rw [sineIntegral_eq, sineDensity]
  simp only [one_div, div_inv_eq_mul]
  ring

end
end «2606.16671v2».SineJacobi
