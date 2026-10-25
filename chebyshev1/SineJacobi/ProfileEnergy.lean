import chebyshev1.SineJacobi.ProfileNormalization
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
Article: chebyshev1, Theorem 5.2.
Theorem 5.1 and E.4: the exact finite quadratic energy tends to c_sin.
Use: `chebyshev1.SineJacobi.sineEnergy_ge_one` feeds
`chebyshev1.SineJacobi.leading_constant_lt_prefix` (leading constant lt prefix).
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal

/--
The actual inverse-Jacobi diagonal profile D_N of Theorem 5.1.

Use: `chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit` uses this definition to
establish convergence along the specified source filter to the specified limit: `Tendsto (fun N
: ℕ => eLpNorm (fun t => diagonalProfile N t-sineDensity t) p (volume.restrict (Ioo (0:ℝ) 1)))
atTop (𝓝 0)`.

Article: chebyshev1, Theorem 5.1 via
`chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit`.
-/
def diagonalProfile (N : ℕ) (t : ℝ) : ℝ :=
  greenWeight N (Nat.floor ((N:ℝ)*t))/(N:ℝ)

/--
Exact identity `diagonalProfile N t = Real.pi*greenProfile N t`.

Use: `chebyshev1.SineJacobi.diagonalProfile_bound` rewrites with this identity to establish
the stated quantitative bound `0 ≤ diagonalProfile N t ∧ diagonalProfile N t ≤ 9*Real.pi^4/4`.

Article: chebyshev1, Theorem 5.1 via
`chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit`.

Proof: Separate `N = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity.
-/
theorem diagonalProfile_eq (N : ℕ) (t : ℝ) :
    diagonalProfile N t = Real.pi*greenProfile N t := by
  unfold diagonalProfile greenProfile
  by_cases hN : N = 0
  · simp [hN]
  · have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN
    field_simp [hn, pi_pos.ne']

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
diagonalProfile N t) atTop (𝓝 (sineDensity t))`.

Use: `chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
eLpNorm (fun t => diagonalProfile N t-sineDensity t) p (volume.restrict (Ioo (0:ℝ) 1))) atTop
(𝓝 0)`.

Article: chebyshev1, Theorem 5.1 via
`chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.greenProfile_limit` with the
arguments shown in the proof.
-/
theorem diagonalProfile_limit {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    Tendsto (fun N : ℕ => diagonalProfile N t) atTop (𝓝 (sineDensity t)) := by
  simpa only [sineDensity, ← diagonalProfile_eq] using
    (tendsto_const_nhds (x := Real.pi)).mul (greenProfile_limit ht)

/--
The stated quantitative bound `0 ≤ diagonalProfile N t ∧ diagonalProfile N t ≤ 9*Real.pi^4/4`.

Use: `chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit` uses this bound to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
eLpNorm (fun t => diagonalProfile N t-sineDensity t) p (volume.restrict (Ioo (0:ℝ) 1))) atTop
(𝓝 0)`.

Article: chebyshev1, Theorem 5.1 via
`chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.greenProfile_uniform_bound`,
`chebyshev1.SineJacobi.diagonalProfile_eq` with the arguments shown in the proof.
-/
theorem diagonalProfile_bound (N : ℕ) (hN : 2 ≤ N) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    0 ≤ diagonalProfile N t ∧ diagonalProfile N t ≤ 9*Real.pi^4/4 := by
  have hh := greenProfile_uniform_bound N hN ⟨ht.1.le, ht.2⟩
  rw [diagonalProfile_eq]
  constructor
  · exact mul_nonneg pi_pos.le hh.1
  · convert mul_le_mul_of_nonneg_left hh.2 pi_pos.le using 1 ; ring

/--
The stated quantitative bound `0 ≤ sineDensity t ∧ sineDensity t ≤ 9*Real.pi^4/4`.

Use: `chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit` uses this bound to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
eLpNorm (fun t => diagonalProfile N t-sineDensity t) p (volume.restrict (Ioo (0:ℝ) 1))) atTop
(𝓝 0)`.

Article: chebyshev1, Theorem 5.1 via
`chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.profileProduct_bound` with the
arguments shown in the proof.
-/
theorem sineDensity_bound {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    0 ≤ sineDensity t ∧ sineDensity t ≤ 9*Real.pi^4/4 := by
  have hh := profileProduct_bound ht
  unfold sineDensity
  constructor
  · exact mul_nonneg pi_pos.le hh.1
  · convert mul_le_mul_of_nonneg_left hh.2 pi_pos.le using 1 ; ring

/--
The precise assertion is `MemLp sineDensity p (volume.restrict (Ioo (0:ℝ) 1))`.

Use: `chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit` uses this assertion to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
eLpNorm (fun t => diagonalProfile N t-sineDensity t) p (volume.restrict (Ioo (0:ℝ) 1))) atTop
(𝓝 0)`.

Article: chebyshev1, Theorem 5.1 via
`chebyshev1.SineJacobi.diagonalProfile_eLpNorm_limit`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.profileProduct_memLp` with the
arguments shown in the proof.
-/
theorem sineDensity_memLp (p : ℝ≥0∞) :
    MemLp sineDensity p (volume.restrict (Ioo (0:ℝ) 1)) :=
  (profileProduct_memLp p).const_mul Real.pi

/--
Theorem 5.1: D_N converges to the normalized density in L2 (and every finite Lp).

Convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
eLpNorm (fun t => diagonalProfile N t-sineDensity t) p (volume.restrict (Ioo (0:ℝ) 1))) atTop
(𝓝 0)`.

Use: `chebyshev2.SineJacobi.diagonal_l2_limit` uses this limit to establish the stated
quantitative bound `Filter.Tendsto (fun N : ℕ => MeasureTheory.eLpNorm (fun t =>
diagonalProfile N t-phi t) 2 (MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) 1))) Filter.atTop
(nhds 0)`.

Article: chebyshev1, Theorem 5.1.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem diagonalProfile_eLpNorm_limit {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    Tendsto (fun N : ℕ => eLpNorm (fun t => diagonalProfile N t-sineDensity t)
      p (volume.restrict (Ioo (0:ℝ) 1))) atTop (𝓝 0) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply chebyshev1.Analysis.bounded_tendsto_eLpNorm
    (ne_of_gt (zero_lt_one.trans_le hp)) hp_top (C := 9*Real.pi^4/4) (by positivity)
    (fun N => by
      have hm : Measurable (diagonalProfile N) := by unfold diagonalProfile; fun_prop
      exact hm.aestronglyMeasurable)
    (sineDensity_memLp p).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 2] with N hn
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hh := diagonalProfile_bound N hn ht
    rw [Real.norm_eq_abs, abs_of_nonneg hh.1]; exact hh.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hh := sineDensity_bound ht
    rw [Real.norm_eq_abs, abs_of_nonneg hh.1]; exact hh.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact diagonalProfile_limit ht

/--
Exact identity `(∫ t in (0:ℝ)..1, diagonalProfile N t^2) = (∑ s ∈ Finset.range N, greenWeight N
s^2)/(N:ℝ)^3`.

Use: `chebyshev1.SineJacobi.greenWeight_energy_limit` uses this identity to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ => (∑
s ∈ Finset.range N, greenWeight N s^2)/(N:ℝ)^3) atTop (𝓝 sineEnergy)`.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.greenWeight_energy_limit`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem diagonalProfile_square_integral (N : ℕ) (hN : 0 < N) :
    (∫ t in (0:ℝ)..1, diagonalProfile N t^2) =
      (∑ s ∈ Finset.range N, greenWeight N s^2)/(N:ℝ)^3 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (fun t => diagonalProfile N t^2) = fun t => (1/(N:ℝ)^2)*
      chebyshev1.Analysis.uniformStep N (fun s => greenWeight N s^2) t := by
    funext t; unfold diagonalProfile chebyshev1.Analysis.uniformStep; ring
  rw [he, intervalIntegral.integral_const_mul, chebyshev1.Analysis.uniformStep_integral N _ hN]
  field_simp [hn]

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ => ∫
t in (0:ℝ)..1, diagonalProfile N t^2) atTop (𝓝 sineEnergy)`.

Use: `chebyshev1.SineJacobi.greenWeight_energy_limit` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ => (∑
s ∈ Finset.range N, greenWeight N s^2)/(N:ℝ)^3) atTop (𝓝 sineEnergy)`.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.greenWeight_energy_limit`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.diagonalProfile_bound`,
`chebyshev1.SineJacobi.diagonalProfile_limit` with the arguments shown in the proof.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection.
-/
theorem diagonalProfile_square_integral_limit :
    Tendsto (fun N : ℕ => ∫ t in (0:ℝ)..1, diagonalProfile N t^2) atTop (𝓝 sineEnergy) := by
  -- Apply the dominated-convergence/Lp transfer after supplying the domination and
  -- pointwise-limit hypotheses.
  let C := 9*Real.pi^4/4
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioo (0:ℝ) 1)) (bound := fun _ => C^2)
    (F := fun N t => diagonalProfile N t^2) (f := fun t => sineDensity t^2)
    (Eventually.of_forall fun N => by
      have hm : Measurable (fun t => diagonalProfile N t^2) := by unfold diagonalProfile; fun_prop
      exact hm.aestronglyMeasurable)
    (show ∀ᶠ N : ℕ in atTop, ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1),
      ‖diagonalProfile N t^2‖ ≤ C^2 from by
      filter_upwards [eventually_ge_atTop 2] with N hn
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hh := diagonalProfile_bound N hn ht
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ hh.1 hh.2 2)
    (integrable_const _)
    (show ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1),
      Tendsto (fun N => diagonalProfile N t^2) atTop (𝓝 (sineDensity t^2)) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact (diagonalProfile_limit ht).pow 2)
  simpa only [sineEnergy, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    restrict_Ioo_eq_restrict_Ioc] using h

/--
Theorem 5.1 and E.4: the exact finite quadratic energy tends to c_sin.

Convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ => (∑
s ∈ Finset.range N, greenWeight N s^2)/(N:ℝ)^3) atTop (𝓝 sineEnergy)`.

Use: `chebyshev1.SineJacobi.endpoint_product_square_sum_limit` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ => (∑
s ∈ Finset.range N, (endpoint N s*endpoint N (N-s-1))^2)/(Real.pi^2*(N:ℝ)^3)) atTop (𝓝 (∫ t in
(0:ℝ)..1, (sineProfile t*sineProfile (1-t))^2))`.

Article: chebyshev1, Theorem 5.1.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem greenWeight_energy_limit :
    Tendsto (fun N : ℕ => (∑ s ∈ Finset.range N, greenWeight N s^2)/(N:ℝ)^3)
      atTop (𝓝 sineEnergy) := by
  apply diagonalProfile_square_integral_limit.congr'
  filter_upwards [eventually_gt_atTop 0] with N hn
  exact diagonalProfile_square_integral N hn

/--
The stated quantitative bound `1 ≤ sineEnergy`.

Use: `chebyshev1.SineJacobi.leading_constant_lt_prefix` uses this bound to establish the
stated quantitative bound `2*sqrt sineEnergy < 4/sqrt 3`.

Article: chebyshev1, Theorem 5.2.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem sineEnergy_ge_one : 1 ≤ sineEnergy := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have h1 : IntervalIntegrable sineDensity volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact MemLp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 1) (sineDensity_memLp 1)
  have h2 : IntervalIntegrable (fun t => sineDensity t^2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)]
    change Integrable (fun t => sineDensity t^2) (volume.restrict (Ioo (0:ℝ) 1))
    convert (sineDensity_memLp 2).integrable_norm_pow (p := 2) (by norm_num) using 1
    funext t
    simp only [Real.norm_eq_abs, sq_abs]
  have he : (∫ t in (0:ℝ)..1, (sineDensity t-1)^2) = sineEnergy-1 := by
    have he : (fun t => (sineDensity t-1)^2) =
        fun t => sineDensity t^2-2*sineDensity t+1 := by funext t; ring
    rw [he, intervalIntegral.integral_add (h2.sub (h1.const_mul 2)) intervalIntegrable_const,
      intervalIntegral.integral_sub h2 (h1.const_mul 2), intervalIntegral.integral_const_mul,
      sineDensity_integral, intervalIntegral.integral_const]
    change sineEnergy-2*1+(1-0)*1 = sineEnergy-1
    ring
  have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (fun t => sq_nonneg (sineDensity t-1))
  rw [he] at hn
  linarith

end
end chebyshev1.SineJacobi
