import chebyshev2.PrescribedSpeed.Density
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
Article: chebyshev2, Theorem 5.1.
Equation (35), proved for every positive exponent, hence in particular for the printed exponents
1/2, 1 and 3/2.
Use: `chebyshev2.PrescribedSpeed.SpeedData.density_moment_rhs_integrable` feeds
`chebyshev2.Calibration.Data.amplitude_square_div_speed_integrable` (amplitude square div speed
integrable).
Proof chain: `chebyshev2.Primal.density_moment_cubic` — chebyshev2, Theorem 5.1; General
measurable speed gives a density with the prescribed ground parameter.
-/
namespace chebyshev2.PrescribedSpeed
noncomputable section
open Set MeasureTheory Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace SpeedData
variable (S : SpeedData)

/--
Integrability of the displayed function: `Integrable (fun x => S.density κ x^r)`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.density_moment_rhs_integrable` uses this
integrability result to establish integrability on the stated domain: `IntegrableOn (fun t =>
((S.D t+t*(2-t))/κ)^r/S.D t) (Ioo (0:ℝ) 2)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.density_moment_cubic`.

Proof: Separate `x ∈ Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then
prove the asserted relation at an arbitrary point in that intersection. Prove equality of
functions by evaluating both sides at an arbitrary argument.
-/
theorem density_rpow_integrable {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r) :
    Integrable (fun x => S.density κ x^r) := by
  -- Separate `x ∈ Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  have hm : Measurable (fun x => S.density κ x^r) :=
    (continuous_rpow_const hr.le).measurable.comp (S.density_measurable κ)
  -- Establish hc as the integrability justification for the later integral estimates or
  -- changes of order.
  have hc : IntegrableOn (fun _ : ℝ => ((S.B+1)/κ)^r) (Ioo (S.X 0) (S.X 2)) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : IntegrableOn (fun x => S.density κ x^r) (Ioo (S.X 0) (S.X 2)) := by
    apply hc.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_of_ae (S.density_bound hκ)] with x hx
    rw [Real.norm_of_nonneg (rpow_nonneg (S.density_nonneg hκ x) r)]
    exact rpow_le_rpow (S.density_nonneg hκ x) hx hr.le
  have he : (Ioo (S.X 0) (S.X 2)).indicator (fun x => S.density κ x^r)=
      (fun x => S.density κ x^r) := by
    funext x
    by_cases hx : x ∈ Ioo (S.X 0) (S.X 2)
    · exact indicator_of_mem hx _
    · simp only [indicator_of_notMem hx,S.density_zero_outside κ hx,zero_rpow hr.ne']
  rw [← he]
  exact hi.integrable_indicator measurableSet_Ioo

/--
Equation (35), proved for every positive exponent, hence in particular for the printed
exponents 1/2, 1 and 3/2.

The precise assertion is `(∫ x, S.density κ x^r)= ∫ t in Ioo (0:ℝ) 2, ((S.D t+t*(2-t))/κ)^r/S.D
t`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.density_moments_35` uses this identity to
establish the precise assertion is `(∫ x, S.density κ x^((j:ℝ)/2))= ∫ t in Ioo (0:ℝ) 2, ((S.D
t+t*(2-t))/κ)^((j:ℝ)/2)/S.D t`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.density_moment_cubic`.

Proof: Separate `t ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then
prove the asserted relation at an arbitrary point in that intersection. Identify the
summands/integrands on their required domain before replacing the sum or integral.
-/
theorem density_moment {κ r : ℝ} (hr : 0 < r) :
    (∫ x, S.density κ x^r)=
      ∫ t in Ioo (0:ℝ) 2, ((S.D t+t*(2-t))/κ)^r/S.D t := by
  -- Separate `t ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  have hs : (∫ x in Icc (S.X 0) (S.X 2), S.density κ x^r)=∫ x, S.density κ x^r :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hn : x ∉ Ioo (S.X 0) (S.X 2) := fun h => hx ⟨h.1.le,h.2.le⟩
      rw [S.density_zero_outside κ hn,zero_rpow hr.ne'])
  rw [← hs]
  have he : (∫ x in Icc (S.X 0) (S.X 2), S.density κ x^r)=
      ∫ x in Icc (S.X 0) (S.X 2), ((S.D (S.q x)+S.q x*(2-S.q x))/κ)^r := by
    apply integral_congr_ae
    filter_upwards [S.density_formula_ae κ] with x hx
    rw [hx]
  rw [he,S.integral_q (fun t => ((S.D t+t*(2-t))/κ)^r)
    ((continuous_rpow_const hr.le).measurable.comp
      ((S.measurable.add (measurable_id.mul (measurable_const.sub measurable_id))).div_const κ))]
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    by_cases ht : t ∈ Ioo (0:ℝ) 2
    · simp only [reciprocal,indicator_of_mem ht,div_eq_mul_inv,mul_comm]
    · simp only [reciprocal,indicator_of_notMem ht,zero_mul])

/--
Integrability on the stated domain: `IntegrableOn (fun t => ((S.D t+t*(2-t))/κ)^r/S.D t) (Ioo
(0:ℝ) 2)`.

Use: `chebyshev2.Calibration.Data.amplitude_square_div_speed_integrable` uses this
integrability result to establish integrability on the stated domain: `IntegrableOn (fun q =>
(C.amplitude κ q)^2/C.speed κ q) (Ioo (0:ℝ) 2)`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.density_moment_cubic`.

Proof: Separate `t ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then
prove the asserted relation at an arbitrary point in that intersection. Prove equality of
functions by evaluating both sides at an arbitrary argument.
-/
theorem density_moment_rhs_integrable {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r) :
    IntegrableOn (fun t => ((S.D t+t*(2-t))/κ)^r/S.D t) (Ioo (0:ℝ) 2) := by
  -- Separate `t ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  have hm : Measurable (fun t => ((S.D t+t*(2-t))/κ)^r) :=
    (continuous_rpow_const hr.le).measurable.comp
      ((S.measurable.add (measurable_id.mul (measurable_const.sub measurable_id))).div_const κ)
  -- Establish hc as the integrability justification for the later integral estimates or
  -- changes of order.
  have hc : Integrable (fun x => ((S.D (S.q x)+S.q x*(2-S.q x))/κ)^r)
      (volume.restrict (Icc (S.X 0) (S.X 2))) := by
    apply (S.density_rpow_integrable hκ hr).restrict.congr
    filter_upwards [S.density_formula_ae κ] with x hx
    rw [hx]
  have hw := (S.integrable_q_iff _ hm).mp hc
  have he : (fun t => S.reciprocal t*((S.D t+t*(2-t))/κ)^r)=
      (Ioo (0:ℝ) 2).indicator (fun t => ((S.D t+t*(2-t))/κ)^r/S.D t) := by
    funext t
    by_cases ht : t ∈ Ioo (0:ℝ) 2
    · simp only [reciprocal,indicator_of_mem ht,div_eq_mul_inv,mul_comm]
    · simp only [reciprocal,indicator_of_notMem ht,zero_mul]
  rw [he] at hw
  exact (integrable_indicator_iff measurableSet_Ioo).mp hw

/--
The precise assertion is `(∫ x, S.density κ x^((j:ℝ)/2))= ∫ t in Ioo (0:ℝ) 2, ((S.D
t+t*(2-t))/κ)^((j:ℝ)/2)/S.D t`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 5.1.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.density_moment`
with the arguments shown in the proof.
-/
theorem density_moments_35 (κ : ℝ) (j : ℕ) (hj : j ∈ ({1,2,3} : Finset ℕ)) :
    (∫ x, S.density κ x^((j:ℝ)/2))=
      ∫ t in Ioo (0:ℝ) 2, ((S.D t+t*(2-t))/κ)^((j:ℝ)/2)/S.D t := by
  apply S.density_moment
  simp only [Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl <;> norm_num

end SpeedData
end
end chebyshev2.PrescribedSpeed
