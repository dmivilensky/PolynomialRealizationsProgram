import «2606.16671v2».SineJacobi.LocalPotential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Article: 2606.16671v2, Theorem E.3.
The boundary condition chooses the non-logarithmic branch of the singular equation.
Use: `«2606.16671v2».SineJacobi.sineProfile_boundary` feeds
`«2606.16671v2».SineJacobi.sineProfile_unique` (The solution and boundary normalization stated in
E.3 determine the profile uniquely).
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Real Set MeasureTheory Filter Topology

/--
The complete elliptic integral of the first kind, with modulus convention as in E.3.

Use: `«2606.16671v2».SineJacobi.ellipticK_continuousAt` rewrites with this definition to
establish continuity at the stated point: `ContinuousAt ellipticK k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_pos`.
-/
def ellipticK (k : ℝ) : ℝ := ∫ theta in (0:ℝ)..(Real.pi/2),
  1/Real.sqrt (1-k^2*sin theta^2)

/--
The explicit singular ODE profile of E.3.

Use: `«2606.16671v2».SineJacobi.sineProfile_boundary` uses this definition to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun t =>
sineProfile t/Real.sqrt t) (𝓝[>] (0:ℝ)) (𝓝 1)`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_pos`.
-/
def sineProfile (t : ℝ) : ℝ :=
  (2/(Real.pi*Real.sqrt Real.pi))*Real.sqrt (sin (Real.pi*t))*
    ellipticK (sin (Real.pi*t/2))

/--
The stated quantitative bound `1-k^2 ≤ 1-k^2*sin theta^2`.

Use: `«2606.16671v2».SineJacobi.ellipticK_continuousAt` uses this bound to establish continuity
at the stated point: `ContinuousAt ellipticK k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_boundary`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem elliptic_den_lower (k theta : ℝ) :
    1-k^2 ≤ 1-k^2*sin theta^2 := by
  have hs : sin theta^2 ≤ 1 := sin_sq_le_one theta
  nlinarith [sq_nonneg k]

/--
Continuity of the displayed function: `Continuous (fun theta : ℝ => 1/Real.sqrt (1-k^2*sin
theta^2))`.

Use: `«2606.16671v2».SineJacobi.ellipticK_pos` uses this continuity result to establish the
stated quantitative bound `0 < ellipticK k`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_pos`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.elliptic_den_lower` with the
arguments shown in the proof.
-/
theorem elliptic_integrand_continuous (k : ℝ) (hk : |k| < 1) :
    Continuous (fun theta : ℝ => 1/Real.sqrt (1-k^2*sin theta^2)) := by
  have hp : 0 < 1-k^2 := by
    have := abs_lt.mp hk
    nlinarith
  apply Continuous.div continuous_const (by fun_prop)
  intro theta
  exact (Real.sqrt_pos.mpr (lt_of_lt_of_le hp (elliptic_den_lower k theta))).ne'

/--
Exact identity `ellipticK 0 = Real.pi/2`.

Use: `«2606.16671v2».SineJacobi.sineProfile_boundary` rewrites with this identity to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun t =>
sineProfile t/Real.sqrt t) (𝓝[>] (0:ℝ)) (𝓝 1)`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_boundary`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem ellipticK_zero : ellipticK 0 = Real.pi/2 := by simp [ellipticK]

/--
Continuity at the stated point: `ContinuousAt ellipticK k`.

Use: `«2606.16671v2».SineJacobi.sineProfile_boundary` uses this continuity result to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun t =>
sineProfile t/Real.sqrt t) (𝓝[>] (0:ℝ)) (𝓝 1)`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_boundary`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem ellipticK_continuousAt {k : ℝ} (hk : |k| < 1) : ContinuousAt ellipticK k := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let c := (1-k^2)/2
  have hc : 0 < c := by
    have hb := abs_lt.mp hk
    dsimp [c]
    nlinarith
  let F : ℝ → ℝ → ℝ := fun u theta => 1/Real.sqrt (max c (1-u^2*sin theta^2))
  -- Establish continuity hF before using the function at limits or in calculus arguments.
  have hF : Continuous F.uncurry := by
    apply Continuous.div continuous_const (by fun_prop)
    intro p
    exact (Real.sqrt_pos.mpr (lt_of_lt_of_le hc (le_max_left _ _))).ne'
  have hi := continuous_parametric_integral_of_continuous (μ := volume) hF
    (isCompact_Icc (a := (0:ℝ)) (b := Real.pi/2))
  apply hi.continuousAt.congr_of_eventuallyEq
  have he : ∀ᶠ u in 𝓝 k, u^2 < 1-c := by
    -- Record the convergence ht with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have ht : Tendsto (fun u : ℝ => u^2) (𝓝 k) (𝓝 (k^2)) := tendsto_id.pow 2
    exact ht.eventually_lt_const (by dsimp [c] at hc ⊢; linarith)
  filter_upwards [he] with u hu
  rw [ellipticK, intervalIntegral.integral_of_le (half_pos pi_pos).le,
    integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro theta
  have hb := elliptic_den_lower u theta
  dsimp [F]
  rw [max_eq_right (by linarith : c ≤ 1-u^2*sin theta^2)]

/--
The stated quantitative bound `0 < ellipticK k`.

Use: `«2606.16671v2».SineJacobi.sineProfile_pos` uses this bound to establish the stated
quantitative bound `0 < sineProfile t`.

Article: 2606.16671v2, Theorem E.3 via `«2606.16671v2».SineJacobi.sineProfile_pos`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.elliptic_integrand_continuous`
with the arguments shown in the proof.
-/
theorem ellipticK_pos (k : ℝ) (hk : |k| < 1) : 0 < ellipticK k := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.elliptic_integrand_continuous`
  -- with the arguments shown in the proof.
  have hp : 0 < 1-k^2 := by
    have := abs_lt.mp hk
    nlinarith
  apply intervalIntegral.integral_pos (half_pos pi_pos)
    (elliptic_integrand_continuous k hk).continuousOn
  · intro theta _
    positivity
  · refine ⟨0, ⟨le_rfl, (half_pos pi_pos).le⟩, ?_⟩
    norm_num

/--
The stated quantitative bound `0 < sineProfile t`.

Use: `«2606.16671v2».SineJacobi.sineProfile_slope_bounds` uses this bound to establish the
stated quantitative bound `-sineProfile t/(1-t) ≤ sineProfile₁ t ∧ sineProfile₁ t ≤ sineProfile
t/t`.

Article: 2606.16671v2, Theorem E.3.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.ellipticK_pos` with the
arguments shown in the proof.
-/
theorem sineProfile_pos {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : 0 < sineProfile t := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.ellipticK_pos` with the arguments
  -- shown in the proof.
  have ha : Real.pi*t ∈ Ioo (0:ℝ) Real.pi :=
    ⟨mul_pos pi_pos ht.1, by nlinarith [pi_pos, ht.2]⟩
  have hh : Real.pi*t/2 ∈ Ioo (0:ℝ) (Real.pi/2) :=
    ⟨half_pos ha.1, by linarith [ha.2]⟩
  have hk : |sin (Real.pi*t/2)| < 1 := by
    rw [abs_of_pos (sin_pos_of_mem_Ioo
      ⟨hh.1, hh.2.trans (by linarith [pi_pos] : Real.pi/2 < Real.pi)⟩)]
    have hb := strictMonoOn_sin
      (show Real.pi*t/2 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [pi_pos, hh.1, hh.2])
      (show Real.pi/2 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [pi_pos]) hh.2
    simpa using hb
  unfold sineProfile
  exact mul_pos (mul_pos (by positivity) (Real.sqrt_pos.mpr (sin_pos_of_mem_Ioo ha)))
    (ellipticK_pos _ hk)

/--
The boundary condition chooses the non-logarithmic branch of the singular equation.

Convergence along the specified source filter to the specified limit: `Tendsto (fun t =>
sineProfile t/Real.sqrt t) (𝓝[>] (0:ℝ)) (𝓝 1)`.

Use: `«2606.16671v2».SineJacobi.sineProfile_unique` uses this limit to establish pointwise
equality on the specified domain: `EqOn g sineProfile (Ioo 0 1)`.

Article: 2606.16671v2, Theorem E.3.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem sineProfile_boundary :
    Tendsto (fun t => sineProfile t/Real.sqrt t) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  -- Record the convergence ht0 with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  -- Record the convergence ht with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have ht : Tendsto (fun t : ℝ => Real.pi*t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := Real.pi)).mul ht0
  have hs := Real.continuous_sinc.continuousAt.tendsto.comp ht
  have hhalf := ht.div_const 2
  have hsin := Real.continuous_sin.continuousAt.tendsto.comp hhalf
  have hK := (ellipticK_continuousAt (k := 0) (by norm_num)).tendsto.comp
    (by simpa using hsin)
  have hb := ((tendsto_const_nhds (x := (2/(Real.pi*Real.sqrt Real.pi))*Real.sqrt Real.pi)).mul
    (Real.continuous_sqrt.continuousAt.tendsto.comp hs)).mul hK
  have hl : (2/(Real.pi*Real.sqrt Real.pi))*Real.sqrt Real.pi*Real.sqrt (sinc 0)*ellipticK 0 = 1 := by
    simp only [sinc_zero, Real.sqrt_one, mul_one, ellipticK_zero]
    field_simp
  rw [hl] at hb
  simp only [Function.comp_def] at hb
  apply hb.congr'
  have he : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ t < 1 := by
    exact (Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1))
  filter_upwards [he] with t ht
  have hangle : 0 < Real.pi*t := mul_pos pi_pos ht.1
  have hsinid : sin (Real.pi*t) = Real.pi*t*sinc (Real.pi*t) := by
    rw [sinc_of_ne_zero hangle.ne']
    field_simp [ht.1.ne']
  unfold sineProfile
  rw [hsinid, Real.sqrt_mul hangle.le, Real.sqrt_mul pi_pos.le]
  field_simp [(Real.sqrt_pos.mpr ht.1).ne']

end
end «2606.16671v2».SineJacobi
