import «2606.16671v2».SineJacobi.GreenLimit
import «2606.16671v2».Analysis.BoundedLpConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
Article: 2606.16671v2, Theorem E.3.
E.3: the actual Green step profiles converge in every finite Lp, including L2.
Result: `«2606.16671v2».SineJacobi.greenProfile_eLpNorm_limit` supplies the stated article
conclusion.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Real Set Filter Topology MeasureTheory
open scoped ENNReal

/--
Almost-everywhere strong measurability: `AEStronglyMeasurable profileProduct (volume.restrict
(Ioo (0:ℝ) 1))`.

Use: `«2606.16671v2».SineJacobi.greenProfile_eLpNorm_limit` uses this measurability result to
establish convergence along the specified source filter to the specified limit: `Tendsto (fun N
: ℕ => eLpNorm (fun t => greenProfile N t-profileProduct t) p (volume.restrict (Ioo (0:ℝ) 1)))
atTop (𝓝 0)`.

Article: 2606.16671v2, Theorem 5.1 via
`«2606.16671v2».SineJacobi.diagonalProfile_eLpNorm_limit`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.profileProduct_continuousOn`
with the arguments shown in the proof.
-/
theorem profileProduct_aestronglyMeasurable :
    AEStronglyMeasurable profileProduct (volume.restrict (Ioo (0:ℝ) 1)) :=
  profileProduct_continuousOn.aestronglyMeasurable measurableSet_Ioo

/--
The precise assertion is `MemLp profileProduct p (volume.restrict (Ioo (0:ℝ) 1))`.

Use: `«2606.16671v2».SineJacobi.sineDensity_memLp` uses this assertion to establish the precise
assertion is `MemLp sineDensity p (volume.restrict (Ioo (0:ℝ) 1))`.

Article: 2606.16671v2, Theorem 5.1 via
`«2606.16671v2».SineJacobi.diagonalProfile_eLpNorm_limit`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem profileProduct_memLp (p : ℝ≥0∞) :
    MemLp profileProduct p (volume.restrict (Ioo (0:ℝ) 1)) := by
  apply MemLp.of_bound profileProduct_aestronglyMeasurable (9*Real.pi^3/4)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hh := profileProduct_bound ht
  rw [Real.norm_eq_abs, abs_of_nonneg hh.1]
  exact hh.2

/--
The precise assertion is `MemLp (greenProfile N) p (volume.restrict (Ioo (0:ℝ) 1))`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem E.3.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem greenProfile_memLp (N : ℕ) (hN : 2 ≤ N) (p : ℝ≥0∞) :
    MemLp (greenProfile N) p (volume.restrict (Ioo (0:ℝ) 1)) := by
  apply MemLp.of_bound (greenProfile_measurable N).aestronglyMeasurable (9*Real.pi^3/4)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hh := greenProfile_uniform_bound N hN ⟨ht.1.le, ht.2⟩
  rw [Real.norm_eq_abs, abs_of_nonneg hh.1]
  exact hh.2

/--
E.3: the actual Green step profiles converge in every finite Lp, including L2.

Convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
eLpNorm (fun t => greenProfile N t-profileProduct t) p (volume.restrict (Ioo (0:ℝ) 1))) atTop
(𝓝 0)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Theorem E.3.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem greenProfile_eLpNorm_limit {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    Tendsto (fun N : ℕ => eLpNorm (fun t => greenProfile N t-profileProduct t)
      p (volume.restrict (Ioo (0:ℝ) 1))) atTop (𝓝 0) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply «2606.16671v2».Analysis.bounded_tendsto_eLpNorm
    (ne_of_gt (zero_lt_one.trans_le hp)) hp_top
    (C := 9*Real.pi^3/4) (by positivity)
    (fun N => (greenProfile_measurable N).aestronglyMeasurable)
    profileProduct_aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 2] with N hn
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hh := greenProfile_uniform_bound N hn ⟨ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg hh.1]
    exact hh.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hh := profileProduct_bound ht
    rw [Real.norm_eq_abs, abs_of_nonneg hh.1]
    exact hh.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact greenProfile_limit ht

end
end «2606.16671v2».SineJacobi
