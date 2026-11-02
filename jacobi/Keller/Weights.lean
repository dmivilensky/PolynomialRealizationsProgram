import jacobi.Elliptic.Quadratures
import Mathlib.Topology.Order.IntermediateValue

/-!
Article: jacobi, Theorem D.6.
The inverse parameter e=1/c puts the entire Keller family on [0,1].
The literal unit-interval integrands have the uniform majorant one for
every integer moment k>=1. Dominated continuity includes both endpoints;
strict pointwise comparison proves strict monotonicity of the actual integrals.
Source: Lebesgue dominated convergence and positivity of the printed polynomial factors.
Use: all signs and endpoint primitives refer to this same printed polynomial.
-/
namespace jacobi.Keller
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The quartic factor of the Keller denominator.
Use: all signs and endpoint primitives refer to this same printed polynomial.
Article: jacobi, Theorem D.6.
-/
def A (v : ℝ) : ℝ := 3-3*v^2+v^4

/-- The denominator polynomial after the exact inverse-shape substitution e=1/c.
Use: one compact parameter interval controls continuity, strict monotonicity and the infinite-c limit.
Article: jacobi, Theorem D.6.
-/
def P (e v : ℝ) : ℝ := (1-e*v^2)*(A v-e)

/-- The actual rescaled Keller integrand.
Use: its unit majorant supplies every convergence and parameter-continuity assertion.
Article: jacobi, Theorem D.6.
-/
def weight (k : ℕ) (e v : ℝ) : ℝ := (1-v^2)^k/sqrt (P e v)

/-- The actual compact-parameter Keller quadrature.
Use: its endpoint values and monotonicity determine the mass parameter uniquely.
Article: jacobi, Theorem D.6.
-/
def J (k : ℕ) (e : ℝ) : ℝ := ∫ v in (0:ℝ)..1,weight k e v

/-- The literal quadrature in the theorem's original parameter.
Use: the final minimum and root-mass formulas retain exactly the printed j_k(c).
Article: jacobi, Theorem D.6.
-/
def j (k : ℕ) (c : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..1,(1-v^2)^k/sqrt ((1-v^2/c)*(c*A v-1))

/-- Both Keller polynomial factors are positive throughout the open integration interval.
Use: licenses every division, square root and strict comparison in the Keller quadratures.
Article: jacobi, Theorem D.6.
Proof: compare with the endpoint factors 1-v² and (1-v²)*(2-v²). -/
theorem factors_pos {e v : ℝ} (he : e∈Icc (0:ℝ) 1) (hv : v∈Ioo (0:ℝ) 1) :
    0<1-e*v^2 ∧ 0<A v-e ∧ (1-v^2)^2≤P e v := by
  have hv2 : v^2<1 := by nlinarith [hv.1,hv.2,sq_nonneg (1-v)]
  have ha : 0<1-v^2 := sub_pos.mpr hv2
  have hleft : 1-v^2≤1-e*v^2 := by nlinarith [he.2,sq_nonneg v]
  have hright : 1-v^2≤A v-e := by unfold A; nlinarith [he.2,sq_nonneg (1-v^2)]
  refine ⟨ha.trans_le hleft,ha.trans_le hright,?_⟩
  unfold P
  nlinarith [mul_le_mul hleft hright ha.le (ha.trans_le hleft).le]

/-- Every positive-order rescaled Keller weight is positive and at most one.
Use: proves finiteness and dominates all parameters, including the transition endpoint.
Article: jacobi, Theorem D.6.
Proof: sqrt(P)>=1-v², and (1-v²)^k<=1-v² when k>=1. -/
theorem weight_bounds {k : ℕ} (hk : 1≤k) {e v : ℝ}
    (he : e∈Icc (0:ℝ) 1) (hv : v∈Ioo (0:ℝ) 1) : 0<weight k e v ∧ weight k e v≤1 := by
  -- The same positive lower square-root bound controls every positive integer order.
  obtain ⟨hL,hR,hP⟩ := factors_pos he hv
  have hp : 0<P e v := mul_pos hL hR
  have hv2 : v^2<1 := by nlinarith [hv.1,hv.2,sq_nonneg (1-v)]
  have ha : 0<1-v^2 := sub_pos.mpr hv2
  have hs : 1-v^2≤sqrt (P e v) := (le_sqrt ha.le hp.le).mpr hP
  have hpow : (1-v^2)^k≤1-v^2 := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add,pow_one]
    exact mul_le_of_le_one_right ha.le (pow_le_one₀ ha.le (by nlinarith [he.2,sq_nonneg v]))
  exact ⟨div_pos (pow_pos ha _) (sqrt_pos.mpr hp),
    (div_le_one (sqrt_pos.mpr hp)).mpr (hpow.trans hs)⟩

/-- Every rescaled Keller quadrature is genuinely interval integrable.
Use: rules out Bochner junk values in the parameter and endpoint calculations.
Article: jacobi, Theorem D.6.
Proof: measurable weights are dominated by the integrable constant one on (0,1). -/
theorem weight_integrable {k : ℕ} (hk : 1≤k) {e : ℝ} (he : e∈Icc (0:ℝ) 1) :
    IntervalIntegrable (weight k e) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mpr
  have hi : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioo (0:ℝ) 1) := integrableOn_const (by simp)
  apply hi.mono'
    (show AEStronglyMeasurable (weight k e) (volume.restrict (Ioo (0:ℝ) 1)) from by
      exact (show Measurable (weight k e) from by unfold weight P A; fun_prop).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  rw [Real.norm_eq_abs,abs_of_pos (weight_bounds hk he hv).1]
  exact (weight_bounds hk he hv).2

/-- The actual rescaled Keller quadratures are continuous on the complete inverse-parameter interval.
Use: includes the c=1 endpoint and the limit c=infinity without extra convergence assumptions.
Article: jacobi, Theorem D.6.
Proof: the parameter dependence is continuous at every interior integration point;
the proved common majorant one permits dominated continuity. -/
theorem J_continuous {k : ℕ} (hk : 1≤k) : ContinuousOn (J k) (Icc (0:ℝ) 1) := by
  -- Endpoint representatives have measure zero; the same finite bound controls the whole parameter interval.
  have h := MeasureTheory.continuousOn_of_dominated
    (μ := volume.restrict (Ioo (0:ℝ) 1)) (s := Icc (0:ℝ) 1)
    (F := fun e v => weight k e v) (bound := fun _ => (1:ℝ))
    (fun e _ => (show Measurable (weight k e) from by unfold weight P A; fun_prop).aestronglyMeasurable)
    (fun e he => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      rw [Real.norm_eq_abs,abs_of_pos (weight_bounds hk he hv).1]
      exact (weight_bounds hk he hv).2)
    (integrableOn_const (by simp)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      intro e he
      have hp := factors_pos he hv
      have hpoly : Continuous (fun u : ℝ => P u v) := by unfold P A; fun_prop
      exact (continuousAt_const.div (continuous_sqrt.comp hpoly).continuousAt
        (sqrt_pos.mpr (mul_pos hp.1 hp.2.1)).ne').continuousWithinAt)
  change ContinuousOn (fun e => ∫ v in (0:ℝ)..1,weight k e v) (Icc (0:ℝ) 1)
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo] using h

/-- Each interior Keller weight strictly increases in the inverse parameter.
Use: supplies strict rather than weak mass-parameter monotonicity.
Article: jacobi, Theorem D.6.
Proof: both denominator factors decrease; the second decreases strictly and the first stays positive. -/
theorem weight_strict {k : ℕ} {e d v : ℝ} (he : e∈Icc (0:ℝ) 1)
    (hd : d∈Icc (0:ℝ) 1) (hed : e<d) (hv : v∈Ioo (0:ℝ) 1) : weight k e v<weight k d v := by
  obtain ⟨heL,heR,_⟩ := factors_pos he hv
  obtain ⟨hdL,hdR,_⟩ := factors_pos hd hv
  have hfac : 1-d*v^2≤1-e*v^2 := by nlinarith [he.2,sq_nonneg v]
  have hP : P d v<P e v := (mul_le_mul_of_nonneg_right hfac hdR.le).trans_lt
    (mul_lt_mul_of_pos_left (by linarith : A v-d<A v-e) heL)
  have hv2 : v^2<1 := by nlinarith [hv.1,hv.2,sq_nonneg (1-v)]
  exact div_lt_div_of_pos_left (pow_pos (sub_pos.mpr hv2) _)
    (sqrt_pos.mpr (mul_pos hdL hdR)) (sqrt_lt_sqrt (mul_nonneg hdL.le hdR.le) hP)

/-- Every positive-order actual Keller quadrature strictly increases in the inverse parameter.
Use: determines the unique mass-constrained parameter in the complete Keller theorem.
Article: jacobi, Theorem D.6.
Proof: integrate the strict comparison on (0,1), a set of positive measure,
using the already proved absolute integrability of both weights. -/
theorem J_strictMono {k : ℕ} (hk : 1≤k) : StrictMonoOn (J k) (Icc (0:ℝ) 1) := by
  -- The two harmless endpoints do not weaken strictness on the positive-measure open interval.
  intro e he d hd hed
  apply intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero
    (by norm_num) (weight_integrable hk he) (weight_integrable hk hd)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (show ∀ᵐ v : ℝ,v≠1 by simp [ae_iff])] with v hv hv1
    exact (weight_strict he hd hed ⟨hv.1,lt_of_le_of_ne hv.2 hv1⟩).le
  · have hvol : 0<(volume.restrict (Ioc (0:ℝ) 1)) (Ioo (0:ℝ) 1) := by
      rw [Measure.restrict_apply measurableSet_Ioo,inter_eq_self_of_subset_left Ioo_subset_Ioc_self]
      norm_num
    exact ne_of_gt (hvol.trans_le (measure_mono (fun v hv => weight_strict he hd hed hv)))

end
end jacobi.Keller
