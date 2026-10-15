import «2610.05164v2».Filters.VolterraSeries

/-!
Article: 2610.05164v2, Theorem 3.3.
The Neumann--Volterra construction for every nonnegative L1 density.
Use: `«2610.05164v2».Filters.jost_left_limit` feeds `«2610.05164v2».Filters.transmission_reflection`
(transmission reflection).
Proof chain: `«2610.05164v2».HalfLine.jostProfile_left_limit` — 2610.05164v2, Theorem 3.3; A common
compact probability measure for all scales.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
The Neumann--Volterra construction for every nonnegative L1 density.

Use: `«2610.05164v2».Filters.jost_forcing_integrable` uses this definition to establish
integrability of the displayed function: `Integrable (fun t => m t*jost s m t)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.
-/
def jost (s : ℝ) (m : ℝ → ℝ) (x : ℝ) : ℝ := ∑' n, volterraTerm s m n x

/--
The value of a convergent infinite sum: `HasSum (factorialBound s M) (exp (s*M/2))`.

Use: `«2610.05164v2».Filters.jost_bounds` uses this infinite-sum formula to establish
membership in the specified domain/enclosure: `jost s m x ∈ Icc (1:ℝ) (exp (s*cumulative m
x/2))`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem factorialBound_hasSum (s M : ℝ) : HasSum (factorialBound s M) (exp (s*M/2)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (s/2*M)
  convert h using 1
  · funext n
    simp only [factorialBound,mul_pow]
  · rw [← Real.exp_eq_exp_ℝ]
    congr 1
    ring

/--
The stated quantitative bound `‖volterraTerm s m n x‖ ≤ factorialBound s (∫ t, m t) n`.

Use: `«2610.05164v2».Filters.jost_continuous` uses this bound to establish continuity of the
displayed function: `Continuous (jost s m)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.volterraTerm_properties`,
`«2610.05164v2».Filters.factorialBound_mono`, `«2610.05164v2».Filters.cumulative_bounds` with
the arguments shown in the proof.
-/
theorem volterraTerm_global_bound {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (n : ℕ) (x : ℝ) :
    ‖volterraTerm s m n x‖ ≤ factorialBound s (∫ t, m t) n := by
  have h := (volterraTerm_properties hm hn hs n).2 x
  rw [Real.norm_eq_abs,abs_of_nonneg h.1]
  exact h.2.trans (factorialBound_mono hs (cumulative_bounds hm hn x).1 (cumulative_bounds hm hn x).2 n)

/--
Summability of the displayed sequence: `Summable (fun n => volterraTerm s m n x)`.

Use: `«2610.05164v2».Filters.jost_bounds` uses this summability result to establish membership
in the specified domain/enclosure: `jost s m x ∈ Icc (1:ℝ) (exp (s*cumulative m x/2))`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.volterraTerm_properties`,
`«2610.05164v2».Filters.factorialBound_hasSum` with the arguments shown in the proof.
-/
theorem jost_summable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : Summable (fun n => volterraTerm s m n x) :=
  (factorialBound_hasSum s (cumulative m x)).summable.of_nonneg_of_le
    (fun n => ((volterraTerm_properties hm hn hs n).2 x).1)
    (fun n => ((volterraTerm_properties hm hn hs n).2 x).2)

/--
Continuity of the displayed function: `Continuous (jost s m)`.

Use: `«2610.05164v2».Filters.jost_forcing_integrable` uses this continuity result to establish
integrability of the displayed function: `Integrable (fun t => m t*jost s m t)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.volterraTerm_properties`,
`«2610.05164v2».Filters.factorialBound_hasSum`,
`«2610.05164v2».Filters.volterraTerm_global_bound` with the arguments shown in the proof.
-/
theorem jost_continuous {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : Continuous (jost s m) :=
  continuous_tsum (fun n => (volterraTerm_properties hm hn hs n).1)
    (factorialBound_hasSum s (∫ t, m t)).summable (volterraTerm_global_bound hm hn hs)

/--
Membership in the specified domain/enclosure: `jost s m x ∈ Icc (1:ℝ) (exp (s*cumulative m
x/2))`.

Use: `«2610.05164v2».Filters.jost_left_limit` uses this assertion to establish convergence
along the specified source filter to the specified limit: `Tendsto (jost s m) atBot (𝓝 1)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_summable`,
`«2610.05164v2».Filters.volterraTerm_properties`,
`«2610.05164v2».Filters.factorialBound_hasSum` with the arguments shown in the proof.
-/
theorem jost_bounds {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : jost s m x ∈ Icc (1:ℝ) (exp (s*cumulative m x/2)) := by
  -- Use the identities/estimates `«2610.05164v2».Filters.jost_summable`,
  -- `«2610.05164v2».Filters.volterraTerm_properties`,
  -- `«2610.05164v2».Filters.factorialBound_hasSum` with the arguments shown in the proof.
  constructor
  · have h := (jost_summable hm hn hs x).le_tsum 0
      (fun n _ => ((volterraTerm_properties hm hn hs n).2 x).1)
    simpa only [volterraTerm,jost] using h
  · have h := (jost_summable hm hn hs x).tsum_le_tsum
      (fun n => ((volterraTerm_properties hm hn hs n).2 x).2)
      (factorialBound_hasSum s (cumulative m x)).summable
    exact h.trans_eq (factorialBound_hasSum s (cumulative m x)).tsum_eq

/--
The stated quantitative bound `jost s m x ≤ exp (s*(∫ t, m t)/2)`.

Use: `«2610.05164v2».Filters.jost_forcing_integrable` uses this bound to establish
integrability of the displayed function: `Integrable (fun t => m t*jost s m t)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_bounds`,
`«2610.05164v2».Filters.cumulative_bounds` with the arguments shown in the proof.
-/
theorem jost_uniform_bound {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : jost s m x ≤ exp (s*(∫ t, m t)/2) :=
  (jost_bounds hm hn hs x).2.trans (exp_le_exp.mpr (by
    have h := mul_le_mul_of_nonneg_left (cumulative_bounds hm hn x).2 hs
    linarith))

/--
The stated quantitative bound `0 < jost s m x`.

Use: `«2610.05164v2».Filters.jost_forcing_integrable` rewrites with this bound to establish
integrability of the displayed function: `Integrable (fun t => m t*jost s m t)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_bounds` with the arguments
shown in the proof.
-/
theorem jost_positive {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : 0 < jost s m x := lt_of_lt_of_le zero_lt_one (jost_bounds hm hn hs x).1

/--
Integrability of the displayed function: `Integrable (fun t => m t*jost s m t)`.

Use: `«2610.05164v2».Filters.jostSlope_continuous` uses this integrability result to establish
continuity of the displayed function: `Continuous (jostSlope s m)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.bounded_forcing_integrable`,
`«2610.05164v2».Filters.jost_continuous`, `«2610.05164v2».Filters.jost_positive` with the
arguments shown in the proof.
-/
theorem jost_forcing_integrable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : Integrable (fun t => m t*jost s m t) := by
  apply bounded_forcing_integrable hm (jost_continuous hm hn hs).aestronglyMeasurable
    (C := exp (s*(∫ t, m t)/2))
  intro t
  rw [Real.norm_eq_abs,abs_of_pos (jost_positive hm hn hs t)]
  exact jost_uniform_bound hm hn hs t

/--
Convergence along the specified source filter to the specified limit: `Tendsto (jost s m) atBot
(𝓝 1)`.

Use: `«2610.05164v2».Comparison.jostWronskian_value` uses this limit to establish exact
identity `jostWronskian s m x=2*transmission s m`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_left_limit`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.cumulative_left_limit`,
`«2610.05164v2».Filters.jost_bounds` with the arguments shown in the proof.
-/
theorem jost_left_limit {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : Tendsto (jost s m) atBot (𝓝 1) := by
  have hlim : Tendsto (fun x => exp (s*cumulative m x/2)) atBot (𝓝 1) := by
    simpa only [← Real.exp_eq_exp_ℝ,mul_zero,zero_div,exp_zero] using
      (((cumulative_left_limit m).const_mul s).div_const (2:ℝ)).exp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun x => (jost_bounds hm hn hs x).1) (fun x => (jost_bounds hm hn hs x).2)

end
end «2610.05164v2».Filters
