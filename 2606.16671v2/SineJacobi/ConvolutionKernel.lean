import «2606.16671v2».SineJacobi.RatioLimit
import «2606.16671v2».Analysis.MeshApproximation
import «2606.16671v2».Analysis.StepIntegral
import «2606.16671v2».Analysis.ArcsineBound
import Mathlib.MeasureTheory.Function.Floor

/-!
Article: 2606.16671v2, Theorem E.3.
One integrable bound controls both hard endpoints of the convolution.
Use: `«2606.16671v2».SineJacobi.convolutionStep_bound` feeds
`«2606.16671v2».SineJacobi.convolutionIntegral_limit` (The convolution limit includes both singular
endpoints, by dominated convergence).
Proof chain: `«2606.16671v2».SineJacobi.convolutionIntegral_limit` — 2606.16671v2, Theorem E.3;
Hard-edge recurrence, singular ODE, uniqueness and endpoint limits.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Real Set Filter Topology MeasureTheory
open scoped BigOperators

/--
Defines `convolutionStep` of type `ℝ` by `((s:ℝ)+1)*ratio N (Nat.floor (((s:ℝ)+1)*x))* ratio N
(s-Nat.floor (((s:ℝ)+1)*x))`.

Use: `«2606.16671v2».SineJacobi.convolutionStep_bound` uses this definition to establish the
stated quantitative bound `0 ≤ convolutionStep N s x ∧ convolutionStep N s x ≤ (1/sinc
(Real.pi*b))^2*«2606.16671v2».Analysis.arcsineBound x`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.
-/
def convolutionStep (N s : ℕ) (x : ℝ) : ℝ :=
  ((s:ℝ)+1)*ratio N (Nat.floor (((s:ℝ)+1)*x))*
    ratio N (s-Nat.floor (((s:ℝ)+1)*x))

/--
Defines `convolutionKernel` of type `ℝ` by `t/(sqrt (sin (Real.pi*(t*x)))*sqrt (sin
(Real.pi*(t*(1-x)))))`.

Use:
`_private.«2606.16671v2».SineJacobi.ConvolutionElliptic.0.«2606.16671v2».SineJacobi.substitution_integrand`
uses this definition to establish the identity stated in that declaration.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.
-/
def convolutionKernel (t x : ℝ) : ℝ :=
  t/(sqrt (sin (Real.pi*(t*x)))*sqrt (sin (Real.pi*(t*(1-x)))))

/--
Measurability of the displayed map: `Measurable (convolutionStep N s)`.

Use: `«2606.16671v2».SineJacobi.convolutionIntegral_limit` uses this measurability result to
establish convergence along the specified source filter to the specified limit: `Tendsto (fun a
=> ∫ x in (0:ℝ)..1, convolutionStep (N a) (s a) x) l (𝓝 (convolutionIntegral t))`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem convolutionStep_measurable (N s : ℕ) : Measurable (convolutionStep N s) := by
  unfold convolutionStep
  fun_prop

/--
Exact identity `(∫ x in (0:ℝ)..1, convolutionStep N s x) = ∑ k ∈ Finset.range (s+1), ratio N
k*ratio N (s-k)`.

Use: `«2606.16671v2».SineJacobi.endpoint_scaled_limit` rewrites with this identity to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun a =>
endpoint (N a) (s a)/sqrt (Real.pi*(N a:ℝ))) l (𝓝 (sineProfile t))`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem convolutionStep_integral (N s : ℕ) :
    (∫ x in (0:ℝ)..1, convolutionStep N s x) =
      ∑ k ∈ Finset.range (s+1), ratio N k*ratio N (s-k) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he : convolutionStep N s = fun x => ((s:ℝ)+1)*
      «2606.16671v2».Analysis.uniformStep (s+1) (fun k => ratio N k*ratio N (s-k)) x := by
    funext x
    simp only [convolutionStep, «2606.16671v2».Analysis.uniformStep, Nat.cast_add, Nat.cast_one]
    ring
  rw [he, intervalIntegral.integral_const_mul,
    «2606.16671v2».Analysis.uniformStep_integral (s+1) _ (by omega)]
  push_cast
  exact mul_div_cancel₀ _ (by positivity)

/--
The stated quantitative bound `ratio N k ≤ (1/sinc (Real.pi*b))/sqrt ((k:ℝ)+1)`.

Use: `«2606.16671v2».SineJacobi.convolutionStep_bound` uses this bound to establish the stated
quantitative bound `0 ≤ convolutionStep N s x ∧ convolutionStep N s x ≤ (1/sinc
(Real.pi*b))^2*«2606.16671v2».Analysis.arcsineBound x`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.sinc_pi_pos`,
`«2606.16671v2».SineJacobi.ratio_binomial_bounds`, `«2606.16671v2».SineJacobi.sinc_antitoneOn`
with the arguments shown in the proof.
-/
theorem ratio_bulk_bound {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (N k : ℕ) (hk : k < N) (hkb : (k:ℝ)/N ≤ b) :
    ratio N k ≤ (1/sinc (Real.pi*b))/sqrt ((k:ℝ)+1) := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.sinc_pi_pos`,
  -- `«2606.16671v2».SineJacobi.ratio_binomial_bounds`,
  -- `«2606.16671v2».SineJacobi.sinc_antitoneOn` with the arguments shown in the proof.
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hbp : 0 < sinc (Real.pi*b) := sinc_pi_pos ⟨by linarith, hb1⟩
  have hr := (ratio_binomial_bounds N k hk).2
  have hs : sinc (Real.pi*b) ≤ sinc ((k:ℝ)*h N) := by
    apply sinc_antitoneOn
    · constructor
      · unfold h; positivity
      · have := (div_lt_one hNr).mpr (show (k:ℝ) < N by exact_mod_cast hk)
        convert mul_le_mul_of_nonneg_left this.le pi_pos.le using 1 <;> (try unfold h) <;> ring
    · constructor <;> nlinarith [pi_pos]
    · convert mul_le_mul_of_nonneg_left hkb pi_pos.le using 1 ; unfold h ; ring
  have hmul := (mul_le_mul_of_nonneg_left hs (ratio_pos N k hk).le).trans hr
  have hc := hmul.trans (binomialRatio_upper k)
  calc
    _ ≤ (1/sqrt ((k:ℝ)+1))/sinc (Real.pi*b) := (le_div_iff₀ hbp).mpr hc
    _ = _ := by ring

/--
One integrable bound controls both hard endpoints of the convolution.

The stated quantitative bound `0 ≤ convolutionStep N s x ∧ convolutionStep N s x ≤ (1/sinc
(Real.pi*b))^2*«2606.16671v2».Analysis.arcsineBound x`.

Use: `«2606.16671v2».SineJacobi.convolutionIntegral_limit` uses this bound to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun a => ∫ x in
(0:ℝ)..1, convolutionStep (N a) (s a) x) l (𝓝 (convolutionIntegral t))`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Use the identities/estimates `«2606.16671v2».Analysis.floor_unit_bounds`,
`«2606.16671v2».SineJacobi.ratio_bulk_bound`, `«2606.16671v2».SineJacobi.sinc_pi_pos` with the
arguments shown in the proof.
-/
theorem convolutionStep_bound {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (N s : ℕ) (hs : s < N) (hsb : (s:ℝ)/N ≤ b)
    {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    0 ≤ convolutionStep N s x ∧
      convolutionStep N s x ≤ (1/sinc (Real.pi*b))^2*«2606.16671v2».Analysis.arcsineBound x := by
  -- Use the identities/estimates `«2606.16671v2».Analysis.floor_unit_bounds`,
  -- `«2606.16671v2».SineJacobi.ratio_bulk_bound`, `«2606.16671v2».SineJacobi.sinc_pi_pos` with
  -- the arguments shown in the proof.
  let k := Nat.floor (((s:ℝ)+1)*x)
  have hf := «2606.16671v2».Analysis.floor_unit_bounds (s+1) (by omega) hx
  simp only [Nat.cast_add, Nat.cast_one] at hf
  change k < s+1 ∧ (k:ℝ) ≤ ((s:ℝ)+1)*x ∧ ((s:ℝ)+1)*x < (k:ℝ)+1 at hf
  have hks : k ≤ s := by dsimp [k]; omega
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hkbr : (k:ℝ)/N ≤ b :=
    (div_le_div_of_nonneg_right (by exact_mod_cast hks) hNr.le).trans hsb
  have hqbr : ((s-k:ℕ):ℝ)/N ≤ b :=
    (div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le s k) hNr.le).trans hsb
  have hr := ratio_bulk_bound hb hb1 N k (by omega) hkbr
  have hq := ratio_bulk_bound hb hb1 N (s-k) (by omega) hqbr
  have hC : 0 < 1/sinc (Real.pi*b) :=
    one_div_pos.mpr (sinc_pi_pos ⟨by linarith, hb1⟩)
  have hspos : 0 < (s:ℝ)+1 := by positivity
  have hprod := mul_le_mul hr hq (ratio_pos N (s-k) (by omega)).le (by positivity)
  have hprod' := mul_le_mul_of_nonneg_left hprod hspos.le
  have hxpos := sqrt_pos.mpr hx.1
  have hypos := sqrt_pos.mpr (by linarith [hx.2] : 0 < 1-x)
  have hkroot : 0 < sqrt ((k:ℝ)+1) := by positivity
  have hqroot : 0 < sqrt (((s-k:ℕ):ℝ)+1) := by positivity
  have hleft : sqrt (((s:ℝ)+1)*x) ≤ sqrt ((k:ℝ)+1) := sqrt_le_sqrt hf.2.2.le
  have hright : sqrt (((s:ℝ)+1)*(1-x)) ≤ sqrt (((s-k:ℕ):ℝ)+1) := by
    apply sqrt_le_sqrt
    rw [Nat.cast_sub hks]
    nlinarith [hf.2.1]
  have hd := mul_le_mul hleft hright (sqrt_nonneg _) (sqrt_nonneg _)
  rw [sqrt_mul hspos.le, sqrt_mul hspos.le] at hd
  have hd' : ((s:ℝ)+1)*(sqrt x*sqrt (1-x)) ≤
      sqrt ((k:ℝ)+1)*sqrt (((s-k:ℕ):ℝ)+1) := by
    calc
      _ = sqrt ((s:ℝ)+1)^2*(sqrt x*sqrt (1-x)) := by rw [sq_sqrt hspos.le]
      _ = sqrt ((s:ℝ)+1)*sqrt x*(sqrt ((s:ℝ)+1)*sqrt (1-x)) := by ring
      _ ≤ _ := hd
  constructor
  · dsimp [convolutionStep, k]
    exact mul_nonneg (mul_nonneg hspos.le (ratio_pos N k (by omega)).le)
      (ratio_pos N (s-k) (by omega)).le
  · change ((s:ℝ)+1)*ratio N k*ratio N (s-k) ≤ _
    calc
      _ ≤ ((s:ℝ)+1)*((1/sinc (Real.pi*b))/sqrt ((k:ℝ)+1)*
          ((1/sinc (Real.pi*b))/sqrt (((s-k:ℕ):ℝ)+1))) := by
        simpa only [mul_assoc] using hprod'
      _ = (1/sinc (Real.pi*b))^2*
          (((s:ℝ)+1)/(sqrt ((k:ℝ)+1)*sqrt (((s-k:ℕ):ℝ)+1))) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        unfold «2606.16671v2».Analysis.arcsineBound
        rw [div_le_div_iff₀ (mul_pos hkroot hqroot) (mul_pos hxpos hypos)]
        simpa only [one_mul] using hd'

end
end «2606.16671v2».SineJacobi
