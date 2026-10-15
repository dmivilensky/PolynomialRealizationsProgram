import «2610.05164v2».Filters.LinearLimits
import «2610.05164v2».Sobolev.Energy

/-!
Article: 2610.05164v2, Lemma 11.
Ordered-simplex integral, the factorial estimate behind the general L1 Volterra series in equation
(43).
Use: `«2610.05164v2».Filters.cumulative_power_integral` feeds
`«2610.05164v2».Filters.volterra_fixedPoint_zero` (Factorial decay forces every bounded solution of
the homogeneous Volterra equation to vanish).
Proof chain: `«2610.05164v2».HalfLine.jostProfile_boundary` — 2610.05164v2, Theorem 3.3; A common
compact probability measure for all scales.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Sobolev «2610.05164v2».GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Defines `cumulative` of type `ℝ` by `∫ t in Iic x, m t`.

Use: `«2610.05164v2».Filters.cumulative_bounds` uses this definition to establish membership in
the specified domain/enclosure: `cumulative m x ∈ Icc (0:ℝ) (∫ t, m t)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.
-/
def cumulative (m : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in Iic x, m t

/--
Exact identity `cumulative m=causal 0 m`.

Use: `«2610.05164v2».Filters.cumulative_derivative` rewrites with this identity to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (cumulative m)
(m x) x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem cumulative_eq_causal (m : ℝ → ℝ) : cumulative m=causal 0 m := by
  funext x
  simp [cumulative,causal]

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (cumulative m) a
b`.

Use: `«2610.05164v2».Filters.cumulative_continuous` uses this assertion to establish continuity
of the displayed function: `Continuous (cumulative m)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.cumulative_eq_causal`,
`«2610.05164v2».Filters.causal_locallyAC` with the arguments shown in the proof.
-/
theorem cumulative_locallyAC {m : ℝ → ℝ} (hm : Integrable m) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (cumulative m) a b := by
  rw [cumulative_eq_causal]
  exact causal_locallyAC le_rfl hm a b

/--
Continuity of the displayed function: `Continuous (cumulative m)`.

Use: `«2610.05164v2».Filters.cumulative_power_integrable` uses this continuity result to
establish integrability of the displayed function: `Integrable (fun x => m x*(cumulative m
x)^n)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.locallyAC_continuous`,
`«2610.05164v2».Filters.cumulative_locallyAC` with the arguments shown in the proof.
-/
theorem cumulative_continuous {m : ℝ → ℝ} (hm : Integrable m) : Continuous (cumulative m) :=
  locallyAC_continuous (cumulative_locallyAC hm)

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (cumulative m)
(m x) x`.

Use: `«2610.05164v2».Filters.cumulative_power_integral` uses this assertion to establish exact
identity `(∫ t in Iic x, m t*(cumulative m t)^n)=(cumulative m x)^(n+1)/(n+1)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.cumulative_eq_causal`,
`«2610.05164v2».Filters.causal_derivative_ae` with the arguments shown in the proof.
-/
theorem cumulative_derivative {m : ℝ → ℝ} (hm : Integrable m) :
    ∀ᵐ x, HasDerivAt (cumulative m) (m x) x := by
  rw [cumulative_eq_causal]
  simpa only [zero_mul,sub_zero] using causal_derivative_ae (c := 0) le_rfl hm

/--
Membership in the specified domain/enclosure: `cumulative m x ∈ Icc (0:ℝ) (∫ t, m t)`.

Use: `«2610.05164v2».Filters.cumulative_power_integrable` rewrites with this assertion to
establish integrability of the displayed function: `Integrable (fun x => m x*(cumulative m
x)^n)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem cumulative_bounds {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) (x : ℝ) :
    cumulative m x ∈ Icc (0:ℝ) (∫ t, m t) :=
  ⟨integral_nonneg (fun t => hn t),setIntegral_le_integral hm (Eventually.of_forall hn)⟩

/--
Monotonicity in increasing order: `Monotone (cumulative m)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 11.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem cumulative_monotone {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) :
    Monotone (cumulative m) := by
  intro x y hxy
  exact setIntegral_mono_set hm.integrableOn (Eventually.of_forall hn) (Eventually.of_forall (fun _ hx => hx.trans hxy))

/--
Convergence along the specified source filter to the specified limit: `Tendsto (cumulative m)
atBot (𝓝 0)`.

Use: `«2610.05164v2».Filters.cumulative_power_integral` uses this limit to establish exact
identity `(∫ t in Iic x, m t*(cumulative m t)^n)=(cumulative m x)^(n+1)/(n+1)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_left_limit`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem cumulative_left_limit (m : ℝ → ℝ) : Tendsto (cumulative m) atBot (𝓝 0) :=
  tendsto_integral_Iic_zero tendsto_id

/--
Convergence along the specified source filter to the specified limit: `Tendsto (cumulative m)
atTop (𝓝 (∫ t, m t))`.

Use: `«2610.05164v2».Filters.jost_right_limit` uses this limit to establish convergence along
the specified source filter to the specified limit: `Tendsto (jost s m) atTop (𝓝 (transmission
s m))`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem cumulative_right_limit {m : ℝ → ℝ} (hm : Integrable m) :
    Tendsto (cumulative m) atTop (𝓝 (∫ t, m t)) := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  have hlim := (intervalIntegral_tendsto_integral_Ioi (0:ℝ) hm.integrableOn tendsto_id).const_add
    (∫ t in Iic (0:ℝ), m t)
  have he : (fun x : ℝ => (∫ t in Iic (0:ℝ), m t)+∫ t in (0:ℝ)..x, m t)=cumulative m := by
    funext x
    have h := intervalIntegral.integral_Iic_sub_Iic (hm.integrableOn (s := Iic 0))
      (hm.integrableOn (s := Iic x))
    dsimp [cumulative]
    linarith
  change Tendsto (fun x : ℝ => (∫ t in Iic (0:ℝ), m t)+∫ t in (0:ℝ)..x, m t)
    atTop (𝓝 ((∫ t in Iic (0:ℝ), m t)+(∫ t in Ioi (0:ℝ), m t))) at hlim
  rw [he,intervalIntegral.integral_Iic_add_Ioi hm.integrableOn hm.integrableOn] at hlim
  exact hlim

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (fun x => (f
x)^n) a b`.

Use: `«2610.05164v2».Filters.cumulative_power_integral` uses this identity to establish exact
identity `(∫ t in Iic x, m t*(cumulative m t)^n)=(cumulative m x)^(n+1)/(n+1)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem locallyAC_pow {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (n : ℕ) :
    AbsolutelyContinuousOnInterval (fun x => (f x)^n) a b := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => simpa only [pow_zero] using
      (contDiff_const.contDiffOn : ContDiffOn ℝ 1 (fun _ : ℝ => (1:ℝ)) (uIcc a b)).absolutelyContinuousOnInterval
  | succ n ih =>
    apply (ih.mul hf).congr
    intro x _
    change (f x)^n*f x=(f x)^(n+1)
    exact (pow_succ _ _).symm

/--
Fundamental theorem on a left half-line with an AE derivative and an actual endpoint limit; no
classical differentiability of the density is needed.

Exact identity `(∫ t in Iic x, d t)=f x`.

Use: `«2610.05164v2».Filters.cumulative_power_integral` uses this identity to establish exact
identity `(∫ t in Iic x, m t*(cumulative m t)^n)=(cumulative m x)^(n+1)/(n+1)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem locallyAC_integral_Iic {f d : ℝ → ℝ} (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x, HasDerivAt f (d x) x) (hi : Integrable d)
    (hl : Tendsto f atBot (𝓝 0)) (x : ℝ) : (∫ t in Iic x, d t)=f x := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hlim := intervalIntegral_tendsto_integral_Iic x hi.integrableOn tendsto_id
  have he : (fun a : ℝ => ∫ t in a..x, d t)=fun a => f x-f a :=
    funext (fun a => locallyAC_integral_eq_sub hac hd a x)
  change Tendsto (fun a : ℝ => ∫ t in a..x, d t) atBot (𝓝 (∫ t in Iic x, d t)) at hlim
  rw [he] at hlim
  -- Record the convergence hlim with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hlim' : Tendsto (fun a => f x-f a) atBot (𝓝 (f x)) := by
    simpa only [sub_zero] using hl.const_sub (f x)
  exact tendsto_nhds_unique hlim hlim'

/--
Integrability of the displayed function: `Integrable (fun x => m x*(cumulative m x)^n)`.

Use: `«2610.05164v2».Filters.cumulative_power_integral` uses this integrability result to
establish exact identity `(∫ t in Iic x, m t*(cumulative m t)^n)=(cumulative m x)^(n+1)/(n+1)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.cumulative_continuous`,
`«2610.05164v2».Filters.cumulative_bounds` with the arguments shown in the proof.
-/
theorem cumulative_power_integrable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) (n : ℕ) :
    Integrable (fun x => m x*(cumulative m x)^n) := by
  apply (hm.norm.mul_const ((∫ t, m t)^n)).mono'
  · exact hm.aestronglyMeasurable.mul ((cumulative_continuous hm).pow n).aestronglyMeasurable
  · exact Eventually.of_forall (fun x => by
      simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (cumulative_bounds hm hn x).1 n)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (cumulative_bounds hm hn x).1
        (cumulative_bounds hm hn x).2 n) (abs_nonneg _))

/--
Ordered-simplex integral, the factorial estimate behind the general L1 Volterra series in
equation (43).

Exact identity `(∫ t in Iic x, m t*(cumulative m t)^n)=(cumulative m x)^(n+1)/(n+1)`.

Use: `«2610.05164v2».Filters.volterraTerm_properties` rewrites with this identity to establish
continuity of the displayed function: `Continuous (volterraTerm s m n) ∧ ∀ x, volterraTerm s m
n x ∈ Icc (0:ℝ) (factorialBound s (cumulative m x) n)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.jostProfile_boundary`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem cumulative_power_integral {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    (n : ℕ) (x : ℝ) :
    (∫ t in Iic x, m t*(cumulative m t)^n)=(cumulative m x)^(n+1)/(n+1) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let F : ℝ → ℝ := fun t => (cumulative m t)^(n+1)/(n+1)
  have hn' : (n:ℝ)+1 ≠ 0 := by positivity
  have hac (a b : ℝ) : AbsolutelyContinuousOnInterval F a b := by
    apply ((locallyAC_pow (cumulative_locallyAC hm a b) (n+1)).mul
      (contDiff_const.contDiffOn : ContDiffOn ℝ 1 (fun _ : ℝ => ((n:ℝ)+1)⁻¹) (uIcc a b)).absolutelyContinuousOnInterval).congr
    intro t _
    change (cumulative m t)^(n+1)*((n:ℝ)+1)⁻¹=(cumulative m t)^(n+1)/((n:ℝ)+1)
    exact (div_eq_mul_inv _ _).symm
  have hd : ∀ᵐ t, HasDerivAt F (m t*(cumulative m t)^n) t := by
    filter_upwards [cumulative_derivative hm] with t ht
    have he := (ht.pow (n+1)).div_const ((n:ℝ)+1)
    convert he using 1
    simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
    field_simp
  -- Record the convergence hl with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hl : Tendsto F atBot (𝓝 0) := by
    have h := ((cumulative_left_limit m).pow (n+1)).div_const ((n:ℝ)+1)
    simpa only [zero_pow (by omega : n+1 ≠ 0),zero_div] using h
  exact locallyAC_integral_Iic hac hd (cumulative_power_integrable hm hn n) hl x

end
end «2610.05164v2».Filters
