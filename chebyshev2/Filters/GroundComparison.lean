import chebyshev2.Filters.LinearLimits
import chebyshev2.GroundState.Article

/-!
Article: chebyshev2, Proposition 8.
Proposition 3(i): the actual linear filter and the ground coordinate.
Use: `chebyshev2.Filters.defect_bounds` feeds `chebyshev2.Residual.state_mem_box` (state mem
box).
Proof chain: `chebyshev2.Residual.statePotential_null` — chebyshev2, Theorem 3.5; Pointwise
cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.Filters
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Continuum chebyshev2.Sobolev chebyshev2.GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Defines `linear` of type `ℝ` by `groundParameter hm hn*causal 2 m x`.

Use: `chebyshev2.Filters.defect` uses this definition in the displayed construction of
`defect`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_linear_filter`.
-/
def linear {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (x : ℝ) : ℝ :=
  groundParameter hm hn*causal 2 m x

/--
Defines `defect` of type `ℝ` by `G.q x-linear hm hn x`.

Use: `chebyshev2.Filters.defect_derivative_ae` uses this definition to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (defect G)
((G.q x)^2-2*defect G x) x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_defect`.
-/
def defect {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x}
    (G : GroundState.GroundWitness hm hn) (x : ℝ) : ℝ := G.q x-linear hm hn x

variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x}
variable (G : GroundState.GroundWitness hm hn)

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (linear hm hn) a
b`.

Use: `chebyshev2.Filters.defect_locallyAC` uses this assertion to establish absolute
continuity on the specified interval: `AbsolutelyContinuousOnInterval (defect G) a b`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Use the identities/estimates `chebyshev2.Filters.causal_locallyAC` with the
arguments shown in the proof.
-/
theorem linear_locallyAC (a b : ℝ) : AbsolutelyContinuousOnInterval (linear hm hn) a b :=
  (causal_locallyAC (by norm_num : (0:ℝ) ≤ 2) hm a b).const_mul _

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (linear hm hn)
(groundParameter hm hn*m x-2*linear hm hn x) x`.

Use: `chebyshev2.Filters.defect_derivative_ae` uses this assertion to establish establishes
the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (defect G) ((G.q
x)^2-2*defect G x) x`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem linear_derivative_ae : ∀ᵐ x, HasDerivAt (linear hm hn)
    (groundParameter hm hn*m x-2*linear hm hn x) x := by
  filter_upwards [causal_derivative_ae (by norm_num : (0:ℝ) ≤ 2) hm] with x hx
  have hd := hx.const_mul (groundParameter hm hn)
  change HasDerivAt (linear hm hn) (groundParameter hm hn*(m x-2*causal 2 m x)) x at hd
  convert hd using 1
  dsimp [linear]
  ring

/--
Integrability of the displayed function: `Integrable (linear hm hn)`.

Use: `chebyshev2.Filters.linear_derivative_integrable` uses this integrability result to
establish integrability of the displayed function: `Integrable (fun x => groundParameter hm
hn*m x-2*linear hm hn x)`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Use the identities/estimates `chebyshev2.Filters.causal_integrable` with the
arguments shown in the proof.
-/
theorem linear_integrable : Integrable (linear hm hn) :=
  (causal_integrable (by norm_num : (0:ℝ) < 2) hm).const_mul _

/--
Exact identity `(∫ x, linear hm hn x) = groundParameter hm hn*(∫ x, m x)/2`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 8.

Proof: Use the identities/estimates `chebyshev2.Filters.causal_mass` with the arguments
shown in the proof.
-/
theorem linear_mass : (∫ x, linear hm hn x) = groundParameter hm hn*(∫ x, m x)/2 := by
  change (∫ x, groundParameter hm hn*causal 2 m x) = _
  rw [integral_const_mul,causal_mass (by norm_num : (0:ℝ) < 2) hm]
  ring

/--
Convergence along the specified source filter to the specified limit: `Tendsto (linear hm hn)
atBot (𝓝 0) ∧ Tendsto (linear hm hn) atTop (𝓝 0)`.

Use: `chebyshev2.Filters.defect_limits` uses this limit to establish convergence along the
specified source filter to the specified limit: `Tendsto (defect G) atBot (𝓝 0) ∧ Tendsto
(defect G) atTop (𝓝 2)`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Use the identities/estimates `chebyshev2.Filters.causal_tendsto_atBot`,
`chebyshev2.Filters.causal_tendsto_atTop` with the arguments shown in the proof.
-/
theorem linear_limits : Tendsto (linear hm hn) atBot (𝓝 0) ∧
    Tendsto (linear hm hn) atTop (𝓝 0) := by
  -- Use the identities/estimates `chebyshev2.Filters.causal_tendsto_atBot`,
  -- `chebyshev2.Filters.causal_tendsto_atTop` with the arguments shown in the proof.
  constructor
  · change Tendsto (fun x => groundParameter hm hn*causal 2 m x) atBot (𝓝 0)
    simpa only [mul_zero] using
      (causal_tendsto_atBot (by norm_num : (0:ℝ) ≤ 2) hm).const_mul (groundParameter hm hn)
  · change Tendsto (fun x => groundParameter hm hn*causal 2 m x) atTop (𝓝 0)
    simpa only [mul_zero] using
      (causal_tendsto_atTop (by norm_num : (0:ℝ) < 2) hm).const_mul (groundParameter hm hn)

include G in
/--
The stated quantitative bound `0 ≤ linear hm hn x`.

Use: `chebyshev2.Filters.defect_bounds` uses this bound to establish membership in the
specified domain/enclosure: `defect G x ∈ Icc (0:ℝ) (G.q x)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.GroundWitness.coupling_positive`,
`chebyshev2.Filters.causal_nonneg` with the arguments shown in the proof.
-/
theorem linear_nonneg (x : ℝ) : 0 ≤ linear hm hn x :=
  mul_nonneg G.coupling_positive.le (causal_nonneg (Eventually.of_forall hn) x)

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (defect G) a b`.

Use: `chebyshev2.Filters.defect_nonneg` uses this assertion to establish the stated
quantitative bound `0 ≤ defect G x`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.GroundWitness.coordinate_locallyAC`,
`chebyshev2.Filters.linear_locallyAC` with the arguments shown in the proof.
-/
theorem defect_locallyAC (a b : ℝ) : AbsolutelyContinuousOnInterval (defect G) a b :=
  (G.coordinate_locallyAC a b).sub (linear_locallyAC a b)

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (defect G)
((G.q x)^2-2*defect G x) x`.

Use: `chebyshev2.Filters.defect_nonneg` uses this assertion to establish the stated
quantitative bound `0 ≤ defect G x`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem defect_derivative_ae : ∀ᵐ x, HasDerivAt (defect G) ((G.q x)^2-2*defect G x) x := by
  filter_upwards [G.coordinate_derivative,linear_derivative_ae (hm := hm) (hn := hn)] with x hq hr
  have hd := hq.sub hr
  change HasDerivAt (defect G)
    ((groundParameter hm hn*m x-G.q x*(2-G.q x))-(groundParameter hm hn*m x-2*linear hm hn x)) x at hd
  convert hd using 1
  dsimp [defect]
  ring

/--
Convergence along the specified source filter to the specified limit: `Tendsto (defect G) atBot
(𝓝 0) ∧ Tendsto (defect G) atTop (𝓝 2)`.

Use: `chebyshev2.Filters.defect_nonneg` uses this limit to establish the stated
quantitative bound `0 ≤ defect G x`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.GroundWitness.coordinate_limits`,
`chebyshev2.Filters.linear_limits` with the arguments shown in the proof.
-/
theorem defect_limits : Tendsto (defect G) atBot (𝓝 0) ∧ Tendsto (defect G) atTop (𝓝 2) := by
  constructor
  · change Tendsto (fun x => G.q x-linear hm hn x) atBot (𝓝 0)
    simpa only [sub_zero] using G.coordinate_limits.1.sub (linear_limits (hm := hm) (hn := hn)).1
  · change Tendsto (fun x => G.q x-linear hm hn x) atTop (𝓝 2)
    simpa only [sub_zero] using G.coordinate_limits.2.sub (linear_limits (hm := hm) (hn := hn)).2

/--
Integrating-factor comparison with the actual ground coordinate. The forcing q² is only locally
integrable; no false global L1 hypothesis is used.

The stated quantitative bound `0 ≤ defect G x`.

Use: `chebyshev2.Filters.defect_bounds` uses this bound to establish membership in the
specified domain/enclosure: `defect G x ∈ Icc (0:ℝ) (G.q x)`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection.
-/
theorem defect_nonneg (x : ℝ) : 0 ≤ defect G x := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  let F : ℝ → ℝ := fun x => exp (2*x)*defect G x
  have hac (a b : ℝ) : AbsolutelyContinuousOnInterval F a b := by
    apply (((contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffOn :
      ContDiffOn ℝ 1 (fun x : ℝ => exp (2*x)) (uIcc a b)).absolutelyContinuousOnInterval).mul
      (defect_locallyAC G a b)
  have hd : ∀ᵐ x, HasDerivAt F (exp (2*x)*(G.q x)^2) x := by
    filter_upwards [defect_derivative_ae G] with x hx
    have he := (hasDerivAt_exp (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
    have hp := he.mul hx
    change HasDerivAt F
      ((exp (2*x)*(2*1))*defect G x+exp (2*x)*((G.q x)^2-2*defect G x)) x at hp
    convert hp using 1
    ring
  have hmono : Monotone F := by
    intro a b hab
    have he := locallyAC_integral_eq_sub hac hd a b
    have hp : 0 ≤ ∫ t in a..b, exp (2*t)*(G.q t)^2 :=
      intervalIntegral.integral_nonneg hab (fun _ _ => mul_nonneg (exp_pos _).le (sq_nonneg _))
    linarith
  -- Record the convergence he with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have he : Tendsto (fun x : ℝ => exp (2*x)) atBot (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_const_nhds.pos_mul_atBot (by norm_num) tendsto_id)
  -- Record the convergence hlim with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hlim : Tendsto F atBot (𝓝 0) := by simpa only [mul_zero] using he.mul (defect_limits G).1
  have hF : 0 ≤ F x := le_of_tendsto hlim
    ((eventually_le_atBot x).mono (fun a ha => hmono ha))
  exact nonneg_of_mul_nonneg_right hF (exp_pos _)

/--
The stated quantitative bound `linear hm hn x ≤ G.q x`.

Use: `chebyshev2.Calibration.Data.comparisonA0_integrable` uses this bound to establish
integrability of the displayed function: `Integrable (fun x => C.comparisonA0
G.coupling_positive (G.q x) (linear hm hn x)* (m x-(C.amplitude (groundParameter hm hn) (G.q
x))^2))`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Filters.defect_nonneg` with the arguments
shown in the proof.
-/
theorem linear_le_coordinate (x : ℝ) : linear hm hn x ≤ G.q x :=
  sub_nonneg.mp (defect_nonneg G x)

/--
Membership in the specified domain/enclosure: `defect G x ∈ Icc (0:ℝ) (G.q x)`.

Use: `chebyshev2.Residual.state_mem_box` uses this assertion to establish membership in the
specified domain/enclosure: `state G x ∈ stateBox (groundParameter hm hn)`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Use the identities/estimates `chebyshev2.Filters.defect_nonneg`,
`chebyshev2.Filters.linear_nonneg` with the arguments shown in the proof.
-/
theorem defect_bounds (x : ℝ) : defect G x ∈ Icc (0:ℝ) (G.q x) :=
  ⟨defect_nonneg G x,sub_le_self _ (linear_nonneg G x)⟩

include G in
/--
The stated quantitative bound `(∫ x, ‖groundParameter hm hn*m x-2*linear hm hn x‖) ≤
2*groundParameter hm hn*(∫ x, m x)`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 8.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem linear_derivative_L1 :
    (∫ x, ‖groundParameter hm hn*m x-2*linear hm hn x‖) ≤
      2*groundParameter hm hn*(∫ x, m x) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hc := G.coupling_positive
  have he : (fun x => ‖groundParameter hm hn*m x-2*linear hm hn x‖)=
      fun x => groundParameter hm hn*‖m x-2*causal 2 m x‖ := by
    funext x
    rw [show groundParameter hm hn*m x-2*linear hm hn x =
      groundParameter hm hn*(m x-2*causal 2 m x) by dsimp [linear]; ring,
      norm_mul,Real.norm_eq_abs,abs_of_pos hc]
  rw [he,integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (causal_derivative_norm (by norm_num : (0:ℝ) < 2) hm (Eventually.of_forall hn)) hc.le
  convert h using 1
  ring

end
end chebyshev2.Filters
