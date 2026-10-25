import chebyshev2.Sobolev.CausalRegularity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
Article: chebyshev2, Theorem 3.3.
The boundary terms vanish, so the integrating factor preserves the exact H1 energy.
Use: `chebyshev2.Sobolev.causalValue_energy` feeds
`chebyshev2.Sobolev.causalValue_energy_Lp` (Exact energy of the continuous representative, with
its actual AE derivative).
Proof chain: `chebyshev2.HalfLine.greenSolution_energy` — chebyshev2, Theorem 3.3; A common
compact probability measure for all scales.
Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel. The needed form is proved here.
-/
namespace chebyshev2.Sobolev
noncomputable section
open chebyshev2.Continuum Set MeasureTheory Real Filter
open scoped InnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false

/--
The literal one-dimensional Sobolev conditions, with an actual locally absolutely continuous
representative and its almost everywhere derivative.

Use: `chebyshev2.Sobolev.SobolevRegular.energy_identity` uses this record of data and proof
obligations to establish the identity `(∫ x, (f x+d x)^2) = (∫ x, f x^2)+(∫ x, d x^2)`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.
-/
structure SobolevRegular (f d : ℝ → ℝ) : Prop where
  /-- The function belongs to L². -/
  value_memLp : MemLp f 2 volume
  /-- Its proposed weak/actual almost-everywhere derivative belongs to L². -/
  derivative_memLp : MemLp d 2 volume
  /-- Local absolute continuity identifies the derivative of the canonical representative. -/
  locally_ac : ∀ a b, AbsolutelyContinuousOnInterval f a b
  /-- The declared derivative agrees with the actual derivative almost everywhere. -/
  derivative_ae : ∀ᵐ x, HasDerivAt f (d x) x

/--
Integrability of the displayed function: `Integrable (fun x => f x*g x)`.

Use: `chebyshev2.Sobolev.SobolevRegular.energy_identity` rewrites with this integrability
result to establish the identity `(∫ x, (f x+d x)^2) = (∫ x, f x^2)+(∫ x, d x^2)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.unique_solution`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem l2_product_integrable {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) : Integrable (fun x => f x*g x) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, mul_comm]

/--
FTC for a locally absolutely continuous representative and its AE derivative.

Exact identity `(∫ x in a..b, d x) = f b-f a`.

Use: `chebyshev2.Sobolev.locallyAC_integral_derivative_zero` uses this identity to
establish exact identity `(∫ x, d x) = 0`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.RiccatiData.q_lipschitz`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection. Identify the summands/integrands
on their required domain before replacing the sum or integral.
-/
theorem locallyAC_integral_eq_sub {f d : ℝ → ℝ}
    (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x, HasDerivAt f (d x) x) (a b : ℝ) :
    (∫ x in a..b, d x) = f b-f a := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  rw [← (hac a b).integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hd] with x hx
  exact fun _ => hx.deriv.symm

/--
Integrable locally AC functions with an integrable AE derivative vanish at both ends. No
pointwise differentiability assumption is imposed.

Convergence along the specified source filter to the specified limit: `Tendsto f atTop (𝓝 0) ∧
Tendsto f atBot (𝓝 0)`.

Use: `chebyshev2.Sobolev.SobolevRegular.square_tendsto_zero` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun x => f x^2)
atTop (𝓝 0) ∧ Tendsto (fun x => f x^2) atBot (𝓝 0)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.unique_solution`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.locallyAC_integral_eq_sub` with the
arguments shown in the proof.
-/
theorem locallyAC_tendsto_zero {f d : ℝ → ℝ}
    (hf : Integrable f) (hd : Integrable d)
    (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hder : ∀ᵐ x, HasDerivAt f (d x) x) :
    Tendsto f atTop (𝓝 0) ∧ Tendsto f atBot (𝓝 0) := by
  -- Use the identities/estimates `chebyshev2.Sobolev.locallyAC_integral_eq_sub` with the
  -- arguments shown in the proof.
  have he (x : ℝ) : f x = f 0+∫ t in (0:ℝ)..x, d t := by
    rw [locallyAC_integral_eq_sub hac hder]
    ring
  -- Record the convergence ht with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have ht : Tendsto f atTop (𝓝 (f 0+∫ t in Ioi (0:ℝ), d t)) := by
    simpa only [id_eq, ← he] using
      (intervalIntegral_tendsto_integral_Ioi 0 hd.integrableOn tendsto_id).const_add (f 0)
  -- Record the convergence hb with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hb : Tendsto f atBot (𝓝 (f 0-∫ t in Iic (0:ℝ), d t)) := by
    have he' (x : ℝ) : f 0-(∫ t in x..(0:ℝ), d t) = f x := by
      rw [locallyAC_integral_eq_sub hac hder]
      ring
    simpa only [id_eq, he'] using
      (intervalIntegral_tendsto_integral_Iic 0 hd.integrableOn tendsto_id).const_sub (f 0)
  have htz : f 0+(∫ t in Ioi (0:ℝ), d t) = 0 := by
    apply IntegrableAtFilter.eq_zero_of_tendsto (μ := volume)
      ⟨univ, univ_mem, by simpa using hf⟩ ?_ ht
    intro s hs
    obtain ⟨b, hb⟩ := mem_atTop_sets.mp hs
    rw [← top_le_iff, ← volume_Ici (a := b)]
    exact measure_mono hb
  have hbz : f 0-(∫ t in Iic (0:ℝ), d t) = 0 := by
    apply IntegrableAtFilter.eq_zero_of_tendsto (μ := volume)
      ⟨univ, univ_mem, by simpa using hf⟩ ?_ hb
    intro s hs
    obtain ⟨b, hb⟩ := mem_atBot_sets.mp hs
    apply le_antisymm le_top
    rw [← volume_Iic (a := b)]
    exact measure_mono hb
  exact ⟨htz ▸ ht, hbz ▸ hb⟩

/--
Exact identity `(∫ x, d x) = 0`.

Use: `chebyshev2.Sobolev.SobolevRegular.integral_cross_zero` uses this identity to
establish exact identity `(∫ x, f x*d x) = 0`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.unique_solution`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.locallyAC_tendsto_zero`,
`chebyshev2.Sobolev.locallyAC_integral_eq_sub` with the arguments shown in the proof.
-/
theorem locallyAC_integral_derivative_zero {f d : ℝ → ℝ}
    (hf : Integrable f) (hd : Integrable d)
    (hac : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hder : ∀ᵐ x, HasDerivAt f (d x) x) : (∫ x, d x) = 0 := by
  -- Use the identities/estimates `chebyshev2.Sobolev.locallyAC_tendsto_zero`,
  -- `chebyshev2.Sobolev.locallyAC_integral_eq_sub` with the arguments shown in the proof.
  have hz := locallyAC_tendsto_zero hf hd hac hder
  have ht := intervalIntegral_tendsto_integral_Ioi 0 hd.integrableOn tendsto_id
  have hb := intervalIntegral_tendsto_integral_Iic 0 hd.integrableOn tendsto_id
  have et : (∫ t in Ioi (0:ℝ), d t) = -f 0 := by
    -- Record the convergence h with its source filter and target limit before taking limits in
    -- the subsequent identities/bounds.
    have h : Tendsto (fun x => ∫ t in (0:ℝ)..x, d t) atTop (𝓝 (0-f 0)) := by
      simpa only [locallyAC_integral_eq_sub hac hder] using hz.1.sub_const (f 0)
    simpa using tendsto_nhds_unique ht h
  have eb : (∫ t in Iic (0:ℝ), d t) = f 0 := by
    -- Record the convergence h with its source filter and target limit before taking limits in
    -- the subsequent identities/bounds.
    have h : Tendsto (fun x => ∫ t in x..(0:ℝ), d t) atBot (𝓝 (f 0-0)) := by
      simpa only [locallyAC_integral_eq_sub hac hder] using hz.2.const_sub (f 0)
    simpa using tendsto_nhds_unique hb h
  rw [← intervalIntegral.integral_Iic_add_Ioi hd.integrableOn hd.integrableOn (b := 0), et, eb]
  ring

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (fun x => f x^2)
a b`.

Use: `chebyshev2.Sobolev.SobolevRegular.integral_cross_zero` uses this identity to
establish exact identity `(∫ x, f x*d x) = 0`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem SobolevRegular.square_locallyAC {f d : ℝ → ℝ} (h : SobolevRegular f d) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => f x^2) a b := by
  apply ((h.locally_ac a b).mul (h.locally_ac a b)).congr
  intro x _
  change f x*f x = f x^2
  ring

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun x => f
x^2) (2*(f x*d x)) x`.

Use: `chebyshev2.Sobolev.SobolevRegular.integral_cross_zero` uses this identity to
establish exact identity `(∫ x, f x*d x) = 0`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem SobolevRegular.square_derivative_ae {f d : ℝ → ℝ} (h : SobolevRegular f d) :
    ∀ᵐ x, HasDerivAt (fun x => f x^2) (2*(f x*d x)) x := by
  filter_upwards [h.derivative_ae] with x hx
  convert hx.pow 2 using 1
  simp [mul_assoc]

/--
Exact identity `(∫ x, f x*d x) = 0`.

Use: `chebyshev2.Sobolev.SobolevRegular.energy_identity` uses this identity to establish
exact identity `(∫ x, (f x+d x)^2) = (∫ x, f x^2)+(∫ x, d x^2)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem SobolevRegular.integral_cross_zero {f d : ℝ → ℝ} (h : SobolevRegular f d) :
    (∫ x, f x*d x) = 0 := by
  have hz := locallyAC_integral_derivative_zero h.value_memLp.integrable_sq
    ((l2_product_integrable h.value_memLp h.derivative_memLp).const_mul 2)
    h.square_locallyAC h.square_derivative_ae
  simp only [integral_const_mul] at hz
  linarith

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun x => f x^2)
atTop (𝓝 0) ∧ Tendsto (fun x => f x^2) atBot (𝓝 0)`.

Use: `chebyshev2.Sobolev.SobolevRegular.tendsto_zero` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto f atTop (𝓝 0) ∧
Tendsto f atBot (𝓝 0)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.groundProfile_left_limit`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.locallyAC_tendsto_zero`,
`chebyshev2.Sobolev.l2_product_integrable`,
`chebyshev2.Sobolev.SobolevRegular.square_locallyAC` with the arguments shown in the proof.
-/
theorem SobolevRegular.square_tendsto_zero {f d : ℝ → ℝ} (h : SobolevRegular f d) :
    Tendsto (fun x => f x^2) atTop (𝓝 0) ∧ Tendsto (fun x => f x^2) atBot (𝓝 0) :=
  locallyAC_tendsto_zero h.value_memLp.integrable_sq
    ((l2_product_integrable h.value_memLp h.derivative_memLp).const_mul 2)
    h.square_locallyAC h.square_derivative_ae

/--
The boundary terms vanish, so the integrating factor preserves the exact H1 energy.

Exact identity `(∫ x, (f x+d x)^2) = (∫ x, f x^2)+(∫ x, d x^2)`.

Use: `chebyshev2.Sobolev.causalValue_energy` uses this identity to establish the identity
`(∫ x, causalValue g x^2)+(∫ x, (g x-causalValue g x)^2) = ‖g‖^2`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.l2_product_integrable`,
`chebyshev2.Sobolev.SobolevRegular.integral_cross_zero` with the arguments shown in the
proof.
-/
theorem SobolevRegular.energy_identity {f d : ℝ → ℝ} (h : SobolevRegular f d) :
    (∫ x, (f x+d x)^2) = (∫ x, f x^2)+(∫ x, d x^2) := by
  -- Use the identities/estimates `chebyshev2.Sobolev.l2_product_integrable`,
  -- `chebyshev2.Sobolev.SobolevRegular.integral_cross_zero` with the arguments shown in
  -- the proof.
  have he (x : ℝ) : (f x+d x)^2 = (f x^2+d x^2)+2*(f x*d x) := by ring
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable (fun x => f x^2+d x^2) :=
    h.value_memLp.integrable_sq.add h.derivative_memLp.integrable_sq
  simp_rw [he]
  rw [integral_add hi
    ((l2_product_integrable h.value_memLp h.derivative_memLp).const_mul 2),
    integral_add h.value_memLp.integrable_sq h.derivative_memLp.integrable_sq,
    integral_const_mul, h.integral_cross_zero]
  ring

/--
The stated quantitative bound `SobolevRegular (causalValue g) (fun x => g x-causalValue g x)`.

Use: `chebyshev2.Sobolev.causalValue_energy` rewrites with this identity to establish exact
identity `(∫ x, causalValue g x^2)+(∫ x, (g x-causalValue g x)^2) = ‖g‖^2`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `chebyshev2.Sobolev.causalValue_memLp`,
`chebyshev2.Sobolev.causalValue_absolutelyContinuous`,
`chebyshev2.Sobolev.causalValue_hasDerivAt_ae` with the arguments shown in the proof.
-/
theorem causalValue_sobolev (g : FeatureSpace) :
    SobolevRegular (causalValue g) (fun x => g x-causalValue g x) :=
  ⟨causalValue_memLp g, (Lp.memLp g).sub (causalValue_memLp g),
    causalValue_absolutelyContinuous g, causalValue_hasDerivAt_ae g⟩

/--
Exact identity `(∫ x, causalValue g x^2)+(∫ x, (g x-causalValue g x)^2) = ‖g‖^2`.

Use: `chebyshev2.Sobolev.H1.norm_sq_energy` uses this identity to establish the identity
`‖u‖^2=(∫ x, slope u x^2)+(∫ x, rep u x^2)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.greenSolution_energy`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem causalValue_energy (g : FeatureSpace) :
    (∫ x, causalValue g x^2)+(∫ x, (g x-causalValue g x)^2) = ‖g‖^2 := by
  rw [← (causalValue_sobolev g).energy_identity, l2_norm_sq]
  congr 1
  funext x
  congr 1
  ring

end
end chebyshev2.Sobolev
