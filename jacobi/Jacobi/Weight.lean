import jacobi.Jacobi.Degree
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
The genuine Jacobi weight and its vanishing flux have their full
integrability, endpoint continuity and ordinary derivative properties
for alpha,beta>-1, including both singular-weight endpoint regimes.
Source: the classical Jacobi Sturm--Liouville weight t^alpha*(1-t)^beta.
Use: the genuine weighted orthogonality and positivity arguments on (0,1).
-/
namespace jacobi.Jacobi
noncomputable section
open Set Real MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- The literal Jacobi weight in the shifted coordinate.
Use: the genuine weighted orthogonality and positivity arguments on (0,1).
Article: jacobi, Lemma C.1.
-/
def weight (a b t : ℝ) : ℝ := t^a*(1-t)^b

/-- The actual Sturm flux coefficient for the shifted Jacobi equation.
Use: the Green boundary term vanishes at both regular singular endpoints.
Article: jacobi, Lemma C.1.
-/
def fluxWeight (a b t : ℝ) : ℝ := t^(a+1)*(1-t)^(b+1)

/-- The original Jacobi weight is positive at every interior point.
Use: converts a nontrivial nonnegative weighted polynomial into a strictly positive integral.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: both positive bases have strictly positive real powers. -/
theorem weight_pos (a b : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) : 0<weight a b t :=
  mul_pos (Real.rpow_pos_of_pos ht.1 _) (Real.rpow_pos_of_pos (sub_pos.mpr ht.2) _)

/-- The Jacobi weight is nonnegative throughout the closed shifted interval.
Use: nonnegative weighted polynomial comparisons include the totalized endpoint values.
Article: jacobi, Lemma C.1.
Proof: real powers of nonnegative bases are nonnegative, including both endpoints. -/
theorem weight_nonneg (a b : ℝ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : 0≤weight a b t :=
  mul_nonneg (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _)

/-- The original Jacobi weight is continuous on the interior even when it is singular at the endpoints.
Use: the local strict-positivity integral argument and the actual weighted Wronskian derivative.
Article: jacobi, Lemma C.1.
Proof: the positive interior bases avoid every singular real-power point. -/
theorem weight_continuousOn (a b : ℝ) : ContinuousOn (weight a b) (Ioo (0:ℝ) 1) := by
  intro t ht
  exact (((Real.continuousAt_rpow_const _ _ (Or.inl ht.1.ne')).mul
    ((continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (sub_pos.mpr ht.2).ne')))).continuousWithinAt

/-- The genuine Jacobi weight is integrable on the first half interval throughout alpha>-1.
Use: establishes full endpoint integrability by reflection rather than assuming a finite Beta integral.
Article: jacobi, Lemma C.1.
Proof: t^alpha is genuinely integrable at zero and the other factor
is continuous and bounded away from its singular base on [0,1/2]. -/
theorem weight_integrable_left {a : ℝ} (ha : -1<a) (b : ℝ) :
    IntervalIntegrable (weight a b) volume 0 (1/2) := by
  -- The second endpoint singularity is absent on this half interval.
  apply (intervalIntegral.intervalIntegrable_rpow' ha).mul_continuousOn
  intro t ht
  have ht : t∈Icc (0:ℝ) (1/2) := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1/2)] using ht
  have hp : 0<1-t := by linarith [ht.2]
  exact ((continuousAt_const.sub continuousAt_id).rpow_const (Or.inl hp.ne')).continuousWithinAt

/-- The original Jacobi weight is genuinely integrable on the whole shifted interval for alpha,beta>-1.
Use: every polynomial-weight integral and Green identity has its convergence premise discharged.
Article: jacobi, Lemma C.1.
Proof: reflect the first-half convergence theorem with swapped
parameters to obtain second-half convergence, then join the intervals. -/
theorem weight_integrable {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    IntervalIntegrable (weight a b) volume 0 1 := by
  -- Reflect the integrable opposite-endpoint weight and join the actual half-interval integrals.
  have h := (weight_integrable_left hb a).comp_sub_left 1
  have hr : IntervalIntegrable (weight a b) volume (1/2) 1 := by
    convert h.symm using 1
    · funext t
      dsimp only [weight]
      rw [show 1-(1-t)=t by ring,mul_comm]
    · norm_num
    · norm_num
  exact (weight_integrable_left ha b).trans hr

/-- Every continuous multiplier of the literal Jacobi weight is integrable on the full interval.
Use: supplies all weighted polynomial products and derivative products in the Sturm Green argument.
Article: jacobi, Lemma C.1.
Proof: multiply the genuine integrable weight by a continuous function on the compact interval. -/
theorem weight_mul_integrable {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable (fun t => weight a b t*f t) volume 0 1 :=
  (weight_integrable ha hb).mul_continuousOn hf.continuousOn

/-- The actual Jacobi flux is continuous everywhere and vanishes at both endpoints.
Use: discharges all Green boundary terms in the full singular parameter range.
Article: jacobi, Lemma C.1.
Proof: both shifted exponents are positive, so their actual real-power
functions are continuous and the corresponding zero-base endpoint powers vanish. -/
theorem fluxWeight_properties {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    Continuous (fluxWeight a b) ∧ fluxWeight a b 0=0 ∧ fluxWeight a b 1=0 := by
  have ha1 : 0<a+1 := by linarith
  have hb1 : 0<b+1 := by linarith
  refine ⟨(Real.continuous_rpow_const ha1.le).mul
    ((Real.continuous_rpow_const hb1.le).comp (continuous_const.sub continuous_id)),?_,?_⟩
  · simp only [fluxWeight,Real.zero_rpow ha1.ne',zero_mul]
  · simp only [fluxWeight,sub_self,Real.zero_rpow hb1.ne',mul_zero]

/-- The literal Jacobi flux is t*(1-t) times the original weight on the interior.
Use: replaces the multiplied Jacobi differential equation by its exact divergence form.
Article: jacobi, Lemma C.1.
Proof: each shifted exponent uses the genuine positive-base real-power add-one identity. -/
theorem fluxWeight_eq (a b : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    fluxWeight a b t=t*(1-t)*weight a b t := by
  rw [fluxWeight,weight,Real.rpow_add_one ht.1.ne',Real.rpow_add_one (sub_pos.mpr ht.2).ne']
  ring

/-- The actual Jacobi flux has its genuine ordinary derivative on the interior.
Use: the weighted Wronskian differentiates to the true Jacobi spectral residual.
Article: jacobi, Lemma C.1.
Proof: differentiate both positive real powers by the actual chain and
product rules, then use the two add-one identities to collect the affine factor. -/
theorem fluxWeight_hasDerivAt (a b : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (fluxWeight a b) ((a+1-(a+b+2)*t)*weight a b t) t := by
  -- Only positive bases are differentiated, so no endpoint differentiability is asserted.
  have h1 := Real.hasDerivAt_rpow_const (p := a+1) (Or.inl ht.1.ne')
  have h2 := (Real.hasDerivAt_rpow_const (p := b+1) (Or.inl (sub_pos.mpr ht.2).ne')).comp t
    ((hasDerivAt_const t 1).sub (hasDerivAt_id t))
  convert h1.mul h2 using 1
  · rfl
  · simp only [add_sub_cancel_right,zero_sub,mul_neg_one,Function.comp_apply]
    rw [Real.rpow_add_one ht.1.ne',Real.rpow_add_one (sub_pos.mpr ht.2).ne']
    unfold weight
    ring

end
end jacobi.Jacobi
