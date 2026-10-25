import chebyshev2.PrescribedSpeed.Inverse
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Article: chebyshev2, Theorem 5.1.
Nonnegative measurable integrands, including extended-valued ones.
Use: `chebyshev2.PrescribedSpeed.SpeedData.integrable_q_iff` feeds
`chebyshev2.PrescribedSpeed.SpeedData.density_moment_rhs_integrable` (density moment rhs
integrable).
Proof chain: `chebyshev2.Primal.density_moment_cubic` — chebyshev2, Theorem 5.1; General
measurable speed gives a density with the prescribed ground parameter.
-/
namespace chebyshev2.PrescribedSpeed
noncomputable section
open Set MeasureTheory Real
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency false

namespace SpeedData
variable (S : SpeedData)

/--
Continuity of the displayed function: `Continuous S.q`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.integrable_q_iff` uses this continuity result to
establish integrability of the displayed function: `Integrable (fun x => f (S.q x))
(volume.restrict (Icc (S.X 0) (S.X 2))) ↔ Integrable (fun t => S.reciprocal t*f t)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.PrescribedSpeed.SpeedData.integral_q`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_lipschitz` with
the arguments shown in the proof.
-/
theorem q_continuous : Continuous S.q := S.q_lipschitz.continuous

/--
Measurability of the displayed map: `Measurable S.reciprocal`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.integrable_q_iff` rewrites with this
measurability result to establish integrability of the displayed function: `Integrable (fun x
=> f (S.q x)) (volume.restrict (Icc (S.X 0) (S.X 2))) ↔ Integrable (fun t => S.reciprocal t*f
t)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.PrescribedSpeed.SpeedData.integral_q`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem reciprocal_measurable : Measurable S.reciprocal :=
  S.measurable.inv.indicator measurableSet_Ioo

/--
Exact identity `S.X (S.q x)=x`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.q_le_iff` rewrites with this identity to
establish equivalence of the displayed criteria: `S.q x ≤ t ↔ x ≤ S.X t`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_inverse` with
the arguments shown in the proof.
-/
theorem X_q {x : ℝ} (hx : x ∈ Icc (S.X 0) (S.X 2)) : S.X (S.q x)=x := by
  rw [SpeedData.q,projIcc_of_mem _ hx]
  exact S.X_inverse ⟨x,hx⟩

/--
Equivalence of the displayed criteria: `S.q x ≤ t ↔ x ≤ S.X t`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.q_map_volume` uses this bound to establish exact
identity `(volume.restrict (Icc (S.X 0) (S.X 2))).map S.q=S.coordinateMeasure`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.PrescribedSpeed.SpeedData.integral_q`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem q_le_iff {x t : ℝ} (hx : x ∈ Icc (S.X 0) (S.X 2))
    (ht : t ∈ Icc (0:ℝ) 2) : S.q x ≤ t ↔ x ≤ S.X t := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  constructor
  · intro h
    have hX := S.X_strictMono.monotoneOn (S.q_mem x) ht h
    rwa [S.X_q hx] at hX
  · intro h
    by_contra hn
    have hX := S.X_strictMono ht (S.q_mem x) (lt_of_not_ge hn)
    rw [S.X_q hx] at hX
    exact (not_lt_of_ge h) hX

/--
The reference coordinate measure for the exact measurable change of variables.

Use: `chebyshev2.PrescribedSpeed.SpeedData.coordinateMeasure_apply` rewrites with this
definition to establish the identity `S.coordinateMeasure A=ENNReal.ofReal (∫ t in A,
S.reciprocal t)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.PrescribedSpeed.SpeedData.integral_q`.
-/
def coordinateMeasure : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (S.reciprocal t))

/--
Exact identity `S.coordinateMeasure A=ENNReal.ofReal (∫ t in A, S.reciprocal t)`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.coordinateMeasure_univ` rewrites with this
identity to establish the identity `S.coordinateMeasure univ=ENNReal.ofReal (S.X 2-S.X 0)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.PrescribedSpeed.SpeedData.integral_q`.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.reciprocal_integrable_global`,
`chebyshev2.PrescribedSpeed.SpeedData.reciprocal_nonneg` with the arguments shown in the
proof.
-/
theorem coordinateMeasure_apply (A : Set ℝ) (hA : MeasurableSet A) :
    S.coordinateMeasure A=ENNReal.ofReal (∫ t in A, S.reciprocal t) := by
  rw [coordinateMeasure,withDensity_apply _ hA]
  exact (ofReal_integral_eq_lintegral_ofReal S.reciprocal_integrable_global.restrict
    (Filter.Eventually.of_forall S.reciprocal_nonneg)).symm

/--
Exact identity `(∫ p in Iic t, S.reciprocal p)=S.X t-S.X 0`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.q_map_volume` rewrites with this identity to
establish exact identity `(volume.restrict (Icc (S.X 0) (S.X 2))).map S.q=S.coordinateMeasure`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.PrescribedSpeed.SpeedData.integral_q`.

Proof: Separate `p ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Identify the summands/integrands on their required domain before
replacing the sum or integral.
-/
theorem reciprocal_integral_Iic {t : ℝ} (ht : t ∈ Icc (0:ℝ) 2) :
    (∫ p in Iic t, S.reciprocal p)=S.X t-S.X 0 := by
  -- Separate `p ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  rw [S.X_difference,intervalIntegral.integral_of_le ht.1]
  rw [← integral_indicator measurableSet_Iic,← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by
    by_cases hp : p ∈ Ioo (0:ℝ) 2
    · have he : p ∈ Iic t ↔ p ∈ Ioc (0:ℝ) t := by simp only [mem_Iic,mem_Ioc,hp.1,true_and]
      simp only [indicator_apply]
      split_ifs <;> tauto
    · have hz : S.reciprocal p=0 := by simp only [reciprocal,indicator_of_notMem hp]
      simp only [indicator_apply]
      split_ifs <;> simp only [hz])

/--
Exact identity `(∫ p, S.reciprocal p)=S.X 2-S.X 0`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.coordinateMeasure_univ` rewrites with this
identity to establish the identity `S.coordinateMeasure univ=ENNReal.ofReal (S.X 2-S.X 0)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.PrescribedSpeed.SpeedData.integral_q`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem reciprocal_integral : (∫ p, S.reciprocal p)=S.X 2-S.X 0 := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  rw [S.X_difference]
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro p hp
  have hi : p ∈ Ioo (0:ℝ) 2 := by
    by_contra hn
    exact hp (by simp [reciprocal,hn])
  exact ⟨hi.1,hi.2.le⟩

/--
Exact identity `S.coordinateMeasure univ=ENNReal.ofReal (S.X 2-S.X 0)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 5.1.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.coordinateMeasure_apply`,
`chebyshev2.PrescribedSpeed.SpeedData.reciprocal_integral` with the arguments shown in the
proof.
-/
theorem coordinateMeasure_univ : S.coordinateMeasure univ=ENNReal.ofReal (S.X 2-S.X 0) := by rw [S.coordinateMeasure_apply _ MeasurableSet.univ,setIntegral_univ,S.reciprocal_integral]

/--
Supplies the typeclass structure specified by `IsFiniteMeasure S.coordinateMeasure`. This lets
subsequent generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: chebyshev2, Theorem 5.1.
-/
instance : IsFiniteMeasure S.coordinateMeasure := ⟨by rw [S.coordinateMeasure_univ]; finiteness⟩

/--
Exact pushforward identity. This simultaneously supplies the change of variables and the
transfer of almost-everywhere derivative statements.

Exact identity `(volume.restrict (Icc (S.X 0) (S.X 2))).map S.q=S.coordinateMeasure`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.integrable_q_iff` rewrites with this identity to
establish integrability of the displayed function: `Integrable (fun x => f (S.q x))
(volume.restrict (Icc (S.X 0) (S.X 2))) ↔ Integrable (fun t => S.reciprocal t*f t)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.PrescribedSpeed.SpeedData.integral_q`.

Proof: Separate `t < 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Identify the summands/integrands on their required domain before
replacing the sum or integral.
-/
theorem q_map_volume :
    (volume.restrict (Icc (S.X 0) (S.X 2))).map S.q=S.coordinateMeasure := by
  -- Separate `t < 0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply S.q_continuous.measurable measurableSet_Iic,
    Measure.restrict_apply (S.q_continuous.measurable measurableSet_Iic),
    S.coordinateMeasure_apply _ measurableSet_Iic]
  by_cases h0 : t < 0
  · have he : S.q ⁻¹' Iic t ∩ Icc (S.X 0) (S.X 2)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_le_of_gt (h0.trans_le (S.q_mem x).1)) hx.1
    rw [he,measure_empty]
    have hz : (∫ p in Iic t, S.reciprocal p)=0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun p hp => by
        have hn : p ∉ Ioo (0:ℝ) 2 := fun h => (not_lt_of_ge (hp.trans h0.le)) h.1
        simp only [reciprocal,indicator_of_notMem hn])
    rw [hz,ENNReal.ofReal_zero]
  · by_cases h2 : 2 ≤ t
    · have he : S.q ⁻¹' Iic t ∩ Icc (S.X 0) (S.X 2)=Icc (S.X 0) (S.X 2) := by
        ext x
        exact ⟨fun hx => hx.2,fun hx => ⟨(S.q_mem x).2.trans h2,hx⟩⟩
      have hi : (∫ p in Iic t, S.reciprocal p)=∫ p, S.reciprocal p := by
        rw [← integral_indicator measurableSet_Iic]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun p => by
          by_cases hp : p ∈ Iic t
          · exact indicator_of_mem hp _
          · have hn : p ∉ Ioo (0:ℝ) 2 := fun h => hp (h.2.le.trans h2)
            simp only [indicator_of_notMem hp,reciprocal,indicator_of_notMem hn])
      rw [he,Real.volume_Icc,hi,S.reciprocal_integral]
    · have ht : t ∈ Icc (0:ℝ) 2 := ⟨le_of_not_gt h0,(lt_of_not_ge h2).le⟩
      have he : S.q ⁻¹' Iic t ∩ Icc (S.X 0) (S.X 2)=Icc (S.X 0) (S.X t) := by
        ext x
        constructor
        · intro hx
          exact ⟨hx.2.1,(S.q_le_iff hx.2 ht).mp hx.1⟩
        · intro hx
          have hx' : x ∈ Icc (S.X 0) (S.X 2) :=
            ⟨hx.1,hx.2.trans (S.X_strictMono.monotoneOn ht (by norm_num) ht.2)⟩
          exact ⟨(S.q_le_iff hx' ht).mpr hx.2,hx'⟩
      rw [he,Real.volume_Icc,S.reciprocal_integral_Iic ht]

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x ∂volume.restrict (Icc (S.X
0) (S.X 2)), P (S.q x)`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.q_derivative_inside` uses this assertion to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x ∂volume.restrict
(Ioo (S.X 0) (S.X 2)), HasDerivAt S.q (S.D (S.q x)) x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.q_map_volume` with the arguments shown in the proof.
-/
theorem q_ae_transfer {P : ℝ → Prop} (hP : ∀ᵐ t ∂volume, P t) :
    ∀ᵐ x ∂volume.restrict (Icc (S.X 0) (S.X 2)), P (S.q x) := by
  have h : ∀ᵐ t ∂S.coordinateMeasure, P t :=
    (withDensity_absolutelyContinuous volume _).ae_le hP
  rw [← S.q_map_volume] at h
  exact ae_of_ae_map S.q_continuous.measurable.aemeasurable h

/--
Theorem 5.1's change of variables, without a continuity assumption on the integrand.

Exact identity `(∫ x in Icc (S.X 0) (S.X 2), f (S.q x))=∫ t, S.reciprocal t*f t`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.density_moment` rewrites with this identity to
establish the precise assertion is `(∫ x, S.density κ x^r)= ∫ t in Ioo (0:ℝ) 2, ((S.D
t+t*(2-t))/κ)^r/S.D t`.

Article: chebyshev2, Theorem 5.1.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.q_map_volume`,
`chebyshev2.PrescribedSpeed.SpeedData.reciprocal_measurable` with the arguments shown in
the proof.
-/
theorem integral_q (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x in Icc (S.X 0) (S.X 2), f (S.q x))=∫ t, S.reciprocal t*f t := by
  rw [← integral_map S.q_continuous.measurable.aemeasurable hf.aestronglyMeasurable,
    S.q_map_volume,coordinateMeasure,
    integral_withDensity_eq_integral_toReal_smul S.reciprocal_measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (S.reciprocal_nonneg _),smul_eq_mul]

/--
Integrability of the displayed function: `Integrable (fun x => f (S.q x)) (volume.restrict (Icc
(S.X 0) (S.X 2))) ↔ Integrable (fun t => S.reciprocal t*f t)`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.density_moment_rhs_integrable` uses this
integrability result to establish integrability on the stated domain: `IntegrableOn (fun t =>
((S.D t+t*(2-t))/κ)^r/S.D t) (Ioo (0:ℝ) 2)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.density_moment_cubic`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.reciprocal_nonneg`,
`chebyshev2.PrescribedSpeed.SpeedData.reciprocal_measurable` with the arguments shown in
the proof.
-/
theorem integrable_q_iff (f : ℝ → ℝ) (hf : Measurable f) :
    Integrable (fun x => f (S.q x)) (volume.restrict (Icc (S.X 0) (S.X 2))) ↔
      Integrable (fun t => S.reciprocal t*f t) := by
  -- Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_continuous`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.reciprocal_nonneg`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.reciprocal_measurable` with the arguments shown
  -- in the proof.
  have hm := integrable_map_measure hf.aestronglyMeasurable S.q_continuous.measurable.aemeasurable
    (μ := volume.restrict (Icc (S.X 0) (S.X 2)))
  rw [S.q_map_volume,coordinateMeasure,
    integrable_withDensity_iff_integrable_smul' S.reciprocal_measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))] at hm
  simpa only [Function.comp_def,ENNReal.toReal_ofReal (S.reciprocal_nonneg _),smul_eq_mul] using hm.symm

/--
Nonnegative measurable integrands, including extended-valued ones.

The precise assertion is `(∫⁻ x in Icc (S.X 0) (S.X 2), f (S.q x))= ∫⁻ t, ENNReal.ofReal
(S.reciprocal t)*f t`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 5.1.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.q_map_volume`,
`chebyshev2.PrescribedSpeed.SpeedData.reciprocal_measurable` with the arguments shown in
the proof.
-/
theorem lintegral_q (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in Icc (S.X 0) (S.X 2), f (S.q x))=
      ∫⁻ t, ENNReal.ofReal (S.reciprocal t)*f t := by
  rw [← lintegral_map hf S.q_continuous.measurable,S.q_map_volume,coordinateMeasure,
    lintegral_withDensity_eq_lintegral_mul₀ S.reciprocal_measurable.ennreal_ofReal.aemeasurable
      hf.aemeasurable]
  simp only [Pi.mul_apply,mul_comm]

end SpeedData
end
end chebyshev2.PrescribedSpeed
