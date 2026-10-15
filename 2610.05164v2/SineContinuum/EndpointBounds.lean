import «2610.05164v2».SineContinuum.Wronskian
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Article: 2610.05164v2, Lemma 5.
Quantitative bounds follow from the proved no-logarithm normalization; no elliptic endpoint
expansion is assumed.
Use: `«2610.05164v2».SineContinuum.ratio_log_bounds` feeds
`«2610.05164v2».SineContinuum.ratio_left_limit` (ratio left limit).
Proof chain: `«2610.05164v2».LocalObstruction.sine_green_scale_tail` — 2610.05164v2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Set Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun t => l
t^2/t) (𝓝[>] (0:ℝ)) (𝓝 π)`.

Use: `«2610.05164v2».SineContinuum.exists_endpoint_bounds` uses this limit to establish
constructs witnesses with the exact properties `∃ b ∈ Ioo (0:ℝ) 1, ∀ t ∈ Ioc (0:ℝ) b, (π/2)*t ≤
l t^2 ∧ l t^2 ≤ 2*π*t`.

Article: 2610.05164v2, Lemma 5 via
`«2610.05164v2».SineContinuum.green_mercer_diagonal_uniform`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem l_square_boundary : Tendsto (fun t => l t^2/t) (𝓝[>] (0:ℝ)) (𝓝 π) := by
  have ht := l_boundary.pow 2
  rw [sq_sqrt pi_pos.le] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [div_pow,sq_sqrt (show 0 ≤ t from ht.le)]

/--
Quantitative bounds follow from the already proved no-logarithm normalization; no elliptic
endpoint expansion is assumed.

Constructs witnesses with the exact properties `∃ b ∈ Ioo (0:ℝ) 1, ∀ t ∈ Ioc (0:ℝ) b, (π/2)*t ≤
l t^2 ∧ l t^2 ≤ 2*π*t`.

Use: `«2610.05164v2».SineContinuum.r_left_limit` uses this bound to establish convergence along
the specified source filter to the specified limit: `Tendsto r (𝓝[>] (0:ℝ)) (𝓝 0)`.

Article: 2610.05164v2, Lemma 5 via
`«2610.05164v2».SineContinuum.green_mercer_diagonal_uniform`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.l_square_boundary` with the
arguments shown in the proof.
-/
theorem exists_endpoint_bounds : ∃ b ∈ Ioo (0:ℝ) 1,
    ∀ t ∈ Ioc (0:ℝ) b, (π/2)*t ≤ l t^2 ∧ l t^2 ≤ 2*π*t := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.l_square_boundary` with the
  -- arguments shown in the proof.
  have hlo := l_square_boundary.eventually_const_lt (by linarith [pi_pos] : π/2 < π)
  have hhi := l_square_boundary.eventually_lt_const (by linarith [pi_pos] : π < 2*π)
  obtain ⟨a,ha,hbounds⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hlo.and hhi)
  let b := min a 1/2
  have hmin : 0 < min a 1 := lt_min ha (by norm_num)
  have hb : b ∈ Ioo (0:ℝ) 1 := by dsimp [b]; constructor <;> nlinarith [min_le_right a (1:ℝ)]
  refine ⟨b,hb,?_⟩
  intro t ht
  have hta : t < a := lt_of_le_of_lt ht.2 (by dsimp [b]; nlinarith [min_le_left a (1:ℝ)])
  have h := hbounds ⟨ht.1,hta⟩
  exact ⟨((lt_div_iff₀ ht.1).mp h.1).le,((div_lt_iff₀ ht.1).mp h.2).le⟩

/--
Defines `ratio` of type `ℝ` by `r t/l t`.

Use: `«2610.05164v2».SineContinuum.correctedRatio` uses this definition in the displayed
construction of `correctedRatio`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 5 via
`«2610.05164v2».SineContinuum.green_mercer_diagonal_uniform`.
-/
def ratio (t : ℝ) : ℝ := r t/l t
/--
Defines `correctedRatio` of type `ℝ` by `ratio t+c*log t`.

Use: `«2610.05164v2».SineContinuum.ratio_log_bounds` uses this definition to establish
establishes the uniform, quantified assertion `∀ t ∈ Ioc (0:ℝ) b, correctedRatio (1/π)
b-(1/π)*log t ≤ ratio t ∧ ratio t ≤ correctedRatio (4/π) b-(4/π)*log t`.

Article: 2610.05164v2, Lemma 5 via
`«2610.05164v2».SineContinuum.green_mercer_diagonal_uniform`.
-/
def correctedRatio (c t : ℝ) : ℝ := ratio t+c*log t

/--
The actual derivative at the stated point: `HasDerivAt ratio (-2/l t^2) t`.

Use: `«2610.05164v2».SineContinuum.correctedRatio_derivative` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt (correctedRatio c) (-2/l
t^2+c/t) t`.

Article: 2610.05164v2, Lemma 5 via
`«2610.05164v2».SineContinuum.green_mercer_diagonal_uniform`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem ratio_derivative {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt ratio (-2/l t^2) t := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hd := (r_derivative ht).div (l_derivative ht) (l_positive ht).ne'
  convert hd using 1
  · funext u; rfl
  · change -2/l t^2=(r₁ t*l t-r t*l₁ t)/l t^2
    congr 1
    have hw := wronskian_eq_two ht
    dsimp [wronskian] at hw
    linear_combination hw

/--
The actual derivative at the stated point: `HasDerivAt (correctedRatio c) (-2/l t^2+c/t) t`.

Use: `«2610.05164v2».SineContinuum.ratio_log_bounds` rewrites with this derivative formula to
establish establishes the uniform, quantified assertion `∀ t ∈ Ioc (0:ℝ) b, correctedRatio
(1/π) b-(1/π)*log t ≤ ratio t ∧ ratio t ≤ correctedRatio (4/π) b-(4/π)*log t`.

Article: 2610.05164v2, Lemma 5 via
`«2610.05164v2».SineContinuum.green_mercer_diagonal_uniform`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem correctedRatio_derivative (c : ℝ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (correctedRatio c) (-2/l t^2+c/t) t := by
  have hd := (ratio_derivative ht).add ((hasDerivAt_log ht.1.ne').const_mul c)
  convert hd using 1
  · funext u; rfl
  · ring

/--
Establishes the uniform, quantified assertion `∀ t ∈ Ioc (0:ℝ) b, correctedRatio (1/π)
b-(1/π)*log t ≤ ratio t ∧ ratio t ≤ correctedRatio (4/π) b-(4/π)*log t`.

Use: `«2610.05164v2».SineContinuum.r_left_limit` uses this bound to establish convergence along
the specified source filter to the specified limit: `Tendsto r (𝓝[>] (0:ℝ)) (𝓝 0)`.

Article: 2610.05164v2, Lemma 5 via
`«2610.05164v2».SineContinuum.green_mercer_diagonal_uniform`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.correctedRatio_derivative`,
`«2610.05164v2».SineContinuum.l_positive` with the arguments shown in the proof.
-/
theorem ratio_log_bounds {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1)
    (hbound : ∀ t ∈ Ioc (0:ℝ) b, (π/2)*t ≤ l t^2 ∧ l t^2 ≤ 2*π*t) :
    ∀ t ∈ Ioc (0:ℝ) b,
      correctedRatio (1/π) b-(1/π)*log t ≤ ratio t ∧
        ratio t ≤ correctedRatio (4/π) b-(4/π)*log t := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.correctedRatio_derivative`,
  -- `«2610.05164v2».SineContinuum.l_positive` with the arguments shown in the proof.
  have hi {t : ℝ} (ht : t ∈ Ioc (0:ℝ) b) : t ∈ Ioo (0:ℝ) 1 := ⟨ht.1,ht.2.trans_lt hb.2⟩
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc (c : ℝ) : ContinuousOn (correctedRatio c) (Ioc (0:ℝ) b) :=
    fun _ ht => (correctedRatio_derivative c (hi ht)).continuousAt.continuousWithinAt
  have hd (c : ℝ) : DifferentiableOn ℝ (correctedRatio c) (interior (Ioc (0:ℝ) b)) :=
    fun _ ht => (correctedRatio_derivative c (hi (interior_subset ht))).differentiableAt.differentiableWithinAt
  have hlo : AntitoneOn (correctedRatio (1/π)) (Ioc (0:ℝ) b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc (0:ℝ) b) (hc _) (hd _)
    intro t ht
    have hm := interior_subset ht
    rw [(correctedRatio_derivative (1/π) (hi hm)).deriv]
    have hp := sq_pos_of_pos (l_positive (hi hm))
    have hv : 1/(π*t) ≤ 2/l t^2 := by
      apply (div_le_div_iff₀ (mul_pos pi_pos hm.1) hp).mpr
      nlinarith [(hbound t hm).2]
    rw [div_div,neg_div]
    linarith
  have hhi : MonotoneOn (correctedRatio (4/π)) (Ioc (0:ℝ) b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc (0:ℝ) b) (hc _) (hd _)
    intro t ht
    have hm := interior_subset ht
    rw [(correctedRatio_derivative (4/π) (hi hm)).deriv]
    have hp := sq_pos_of_pos (l_positive (hi hm))
    have hv : 2/l t^2 ≤ 4/(π*t) := by
      apply (div_le_div_iff₀ hp (mul_pos pi_pos hm.1)).mpr
      nlinarith [(hbound t hm).1]
    rw [div_div,neg_div]
    linarith
  intro t ht
  have hβ : b ∈ Ioc (0:ℝ) b := ⟨hb.1,le_refl b⟩
  have hl := hlo ht hβ ht.2
  have hu := hhi ht hβ ht.2
  dsimp [correctedRatio] at hl hu ⊢
  constructor <;> linarith

end
end «2610.05164v2».SineContinuum
