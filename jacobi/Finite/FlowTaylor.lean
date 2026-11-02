import jacobi.Finite.FlowBounds
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Taylor

/-!
Global exponential energy growth and the explicit second-order remainder.
The input derivatives and their bounds are the proved derivatives of the
globally reconstructed matrix flow. Gronwall controls the energy on the
whole interval, and the ordinary real Taylor theorem supplies the factor
one half in the second-order remainder.
Use: StandardDescent combines this uniform finite-dimensional estimate
with the initial standard-matrix limits and the exact descent constants.
Article: jacobi, Proposition 5.5, Equation (5.13); Theorem 5.6.
Article role: the global Taylor remainder used for the fixed-time strict descent.
-/
namespace jacobi.Finite
noncomputable section
open Real Matrix Set
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} (S : Nodes (n+1))

/-- The actual energy is nonnegative at every real time.
Article: jacobi, Proposition 5.5, Equation (5.13); Theorem 5.6.
-/
theorem flowEnergy_nonneg (w : WeightSimplex (n+1)) (t : ℝ) : 0≤flowEnergy S w t :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Analyticity of the original reconstructed energy transfers to the
literal Green-diagonal sum used in the differential estimates.
Article: jacobi, Proposition 5.5, Equation (5.13); Theorem 5.6.
-/
theorem flowEnergy_analytic (w : WeightSimplex (n+1)) (t : ℝ) :
    AnalyticAt ℝ (flowEnergy S w) t := by
  simpa only [resolventFlow,spectralWeights_reconstruct,← flowEnergy_eq] using
    resolventFlow_energy_analytic S (reconstructFiber S w) t

/-- The energy bound holds along either orientation of the real time
axis. This single estimate handles positive and negative flow times.
Article: jacobi, Proposition 5.5, Equation (5.13); Theorem 5.6.
-/
theorem flowEnergy_growth_unit (w : WeightSimplex (n+1)) (c T : ℝ)
    (hc : |c|=1) (hT : 0≤T) :
    flowEnergy S w (c*T)≤flowEnergy S w 0*exp (4*flowMass S*T) := by
  have hd (x : ℝ) : HasDerivAt (fun y => flowEnergy S w (c*y))
      (flowEnergyVelocity S w (c*x)*c) x := by
    simpa only [Function.comp_def,id_eq,mul_one] using
      (flowEnergy_hasDerivAt S w (c*x)).comp x ((hasDerivAt_id x).const_mul c)
  have hcont : Continuous (fun x => flowEnergy S w (c*x)) :=
    continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun x => flowEnergy S w (c*x))
    (f' := fun x => flowEnergyVelocity S w (c*x)*c)
    (a := 0) (b := T) (δ := flowEnergy S w 0) (K := 4*flowMass S) (ε := 0)
    hcont.continuousOn (fun x _ => (hd x).hasDerivWithinAt)
    (by simpa only [mul_zero,Real.norm_eq_abs,abs_of_nonneg (flowEnergy_nonneg S w 0)] using
      (le_rfl : flowEnergy S w 0≤flowEnergy S w 0))
    (fun x _ => by
      simpa only [Real.norm_eq_abs,abs_mul,hc,mul_one,
        abs_of_nonneg (flowEnergy_nonneg S w (c*x)),add_zero] using
        flowEnergyVelocity_abs_le S w (c*x)) T ⟨hT,le_rfl⟩
  simpa only [Real.norm_eq_abs,abs_of_nonneg (flowEnergy_nonneg S w (c*T)),
    sub_zero,gronwallBound_ε0] using h

/-- The actual finite energy grows by at most exp(4 s |t|) in either
time direction, with the same conserved scaled trace s.
Article: jacobi, Proposition 5.5, Equation (5.13); Theorem 5.6.
-/
theorem flowEnergy_growth (w : WeightSimplex (n+1)) (t : ℝ) :
    flowEnergy S w t≤flowEnergy S w 0*exp (4*flowMass S*|t|) := by
  rcases le_total 0 t with ht | ht
  · simpa only [one_mul,abs_of_nonneg ht] using
      flowEnergy_growth_unit S w 1 t (by norm_num) ht
  · have h := flowEnergy_growth_unit S w (-1) (-t) (by norm_num) (by linarith)
    simpa only [neg_mul,one_mul,neg_neg,abs_of_nonpos ht] using h

/-- The second iterated derivative is exactly the already differentiated
finite energy pairing. This identifies the derivative in the library's
Taylor theorem with the derivative controlled by the matrix estimates.
Article: jacobi, Proposition 5.5, Equation (5.13); Theorem 5.6.
-/
theorem flowEnergy_iteratedDeriv_two (w : WeightSimplex (n+1)) :
    iteratedDeriv 2 (flowEnergy S w)=flowEnergyAcceleration S w := by
  have h1 : deriv (flowEnergy S w)=flowEnergyVelocity S w :=
    funext (fun t => (flowEnergy_hasDerivAt S w t).deriv)
  rw [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,h1]
  exact funext (fun t => (flowEnergyVelocity_hasDerivAt S w t).deriv)

/-- The finite resolvent flow has the full stated second-order estimate
for every real time, including negative times and time zero.
Article: jacobi, Proposition 5.5, Equation (5.13); Theorem 5.6.
-/
theorem flowEnergy_taylor (w : WeightSimplex (n+1)) (t : ℝ) :
    flowEnergy S w t≤flowEnergy S w 0+t*flowEnergyVelocity S w 0+
      12*(flowMass S)^2*exp (4*flowMass S*|t|)*t^2*flowEnergy S w 0 := by
  by_cases ht : t=0
  · subst t
    simp
  have hne : (0:ℝ)≠t := Ne.symm ht
  have hcont : ContDiff ℝ 2 (flowEnergy S w) :=
    contDiff_iff_contDiffAt.mpr (fun x => (flowEnergy_analytic S w x).contDiffAt)
  obtain ⟨x,hx,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := flowEnergy S w) (n := 1) hne hcont.contDiffOn
  have hu : UniqueDiffWithinAt ℝ (uIcc 0 t) 0 :=
    (uniqueDiffOn_uIcc hne) 0 left_mem_uIcc
  have hwd : derivWithin (flowEnergy S w) (uIcc 0 t) 0=flowEnergyVelocity S w 0 :=
    (flowEnergy_hasDerivAt S w 0).hasDerivWithinAt.derivWithin hu
  have hpoly : taylorWithinEval (flowEnergy S w) 1 (uIcc 0 t) 0 t=
      flowEnergy S w 0+t*flowEnergyVelocity S w 0 := by
    rw [taylorWithinEval_succ,taylor_within_zero_eval,iteratedDerivWithin_one,hwd]
    norm_num

  rw [hpoly,show (1+1:ℕ)=2 by rfl,flowEnergy_iteratedDeriv_two] at he
  norm_num only [sub_zero,Nat.factorial_two,Nat.cast_ofNat] at he
  have hxabs : |x|≤|t| := by
    change min 0 t<x ∧ x<max 0 t at hx
    apply abs_le.mpr
    exact ⟨(le_min (neg_nonpos.mpr (abs_nonneg t)) (neg_abs_le t)).trans hx.1.le,
      hx.2.le.trans (max_le (abs_nonneg t) (le_abs_self t))⟩
  have hmpos := flowMass_pos S
  have hE : flowEnergy S w x≤flowEnergy S w 0*exp (4*flowMass S*|t|) :=
    (flowEnergy_growth S w x).trans
      (mul_le_mul_of_nonneg_left (exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hxabs (by positivity)))
          (flowEnergy_nonneg S w 0))
  have hA : flowEnergyAcceleration S w x≤
      24*(flowMass S)^2*(flowEnergy S w 0*exp (4*flowMass S*|t|)) :=
    (le_abs_self _).trans ((flowEnergyAcceleration_abs_le S w x).trans
      (mul_le_mul_of_nonneg_left hE (by positivity)))
  have hm := mul_le_mul_of_nonneg_right hA (sq_nonneg t)
  nlinarith

end
end jacobi.Finite
