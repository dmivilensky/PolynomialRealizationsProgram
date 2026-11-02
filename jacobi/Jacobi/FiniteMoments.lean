import jacobi.Jacobi.FiniteTrace
import jacobi.Jacobi.FiniteSpectrum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Article: jacobi, Lemma 1.3.
Both actual finite scaled Jacobi spectral sums are evaluated exactly.
Their limits are the printed M and T_2 expressions. Identification with
the infinite Bessel sums is a separate limiting step, not assumed here.
Source: the actual polynomial logarithmic derivative and its genuine derivative.
Use: evaluates the real finite spectral trace directly from the actual Jacobi root sums.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual finite resolvent value equals its literal shifted inverse-root scaling.
Use: evaluates the real finite spectral trace directly from the actual Jacobi root sums.
Article: jacobi, Lemma 1.3.
Proof: substitute finiteSigma=4*n^2*t and cancel the constant factor two, retaining totalized division even at zero degree. -/
theorem finiteLambda_shifted {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (i : Fin n) :
    finiteLambda a b ha hb n i=(1/(2*(n:ℝ)^2))*(1/shiftedRoots a b ha hb n i) := by
  unfold finiteLambda finiteSigma
  rw [show (4:ℝ)*(n:ℝ)^2*shiftedRoots a b ha hb n i=
    2*(2*(n:ℝ)^2*shiftedRoots a b ha hb n i) by ring,div_mul_eq_div_div]
  norm_num only [div_self (by norm_num : (2:ℝ)≠0)]
  ring

/-- The genuine finite scaled Jacobi resolvent trace has the exact printed formula.
Use: proves mu_n tends to M and supplies a bounded finite first trace for spectral tails.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: factor out 1/(2*n^2), apply the already proved actual inverse-root sum and cancel only positive degree and alpha+1. -/
theorem finiteLambda_sum {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (hn : 0<n) :
    (∑ i:Fin n,finiteLambda a b ha hb n i)=
      (1+(a+b+1)/(n:ℝ))/(2*(a+1)) := by
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  simp_rw [finiteLambda_shifted ha hb]
  rw [← Finset.mul_sum,shifted_inverse_root_sum ha hb]
  field_simp [hnR,show a+1≠0 by linarith]
  ring

/-- The genuine finite second scaled Jacobi spectral trace has its exact closed expression.
Use: gives the printed limiting second moment without assuming convergence of an infinite Bessel sum.
Article: jacobi, Lemma 1.3.
Proof: square the actual inverse-root scaling, factor its constant
coefficient, and use the genuine differentiated logarithmic derivative.
The two actual endpoint derivatives reduce the result to a rational formula in inverse degree. -/
theorem finiteLambda_square_sum {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (hn : 0<n) :
    (∑ i:Fin n,(finiteLambda a b ha hb n i)^2)=
      ((1+(a+b+1)/(n:ℝ))^2/(a+1)^2-
        (1-1/(n:ℝ))*(1+(a+b+1)/(n:ℝ))*(1+(a+b+2)/(n:ℝ))/((a+1)*(a+2)))/4 := by
  -- The cancellation uses actual positive degrees and the full admissible real order range.
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have ha1 : a+1≠0 := by linarith
  have ha2 : a+2≠0 := by linarith
  simp_rw [finiteLambda_shifted ha hb,mul_pow]
  rw [← Finset.mul_sum,shifted_inverse_root_square_sum ha hb,
    shiftedPolynomial_derivative_zero ha,shiftedPolynomial_second_derivative_zero ha]
  field_simp [hnR,ha1,ha2]
  ring

/-- The actual finite scaled Jacobi mass tends to the printed Bessel-edge mass expression.
Use: discharges the finite trace limit in the full source spectral transfer theorem.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: the exact finite mass is a continuous rational function of inverse degree, which tends to zero. -/
theorem finiteLambda_sum_tendsto {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    Tendsto (fun n : ℕ => ∑ i:Fin n,finiteLambda a b ha hb n i) atTop (𝓝 (1/(2*(a+1)))) := by
  let G := fun x : ℝ => (1+(a+b+1)*x)/(2*(a+1))
  have hG : ContinuousAt G 0 := by unfold G; fun_prop
  have h := hG.tendsto.comp (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h0 : G 0=1/(2*(a+1)) := by simp only [G,mul_zero,add_zero]
  rw [h0] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  simpa only [G,div_eq_mul_inv,Function.comp_apply] using finiteLambda_sum ha hb hn

/-- The actual finite second Jacobi spectral trace tends to the printed T_2 expression.
Use: supplies the finite second-moment limit in the Bessel Rayleigh-sum identification.
Article: jacobi, Lemma 1.3.
Proof: the exact genuine finite second trace is a continuous rational
function of inverse degree. At zero its two terms simplify to the
printed positive expression throughout alpha>-1. -/
theorem finiteLambda_square_sum_tendsto {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    Tendsto (fun n : ℕ => ∑ i:Fin n,(finiteLambda a b ha hb n i)^2) atTop
      (𝓝 (1/(4*(a+1)^2*(a+2)))) := by
  -- This is a limit of actual finite sums, with no infinite Rayleigh-sum premise.
  let G := fun x : ℝ => ((1+(a+b+1)*x)^2/(a+1)^2-
    (1-x)*(1+(a+b+1)*x)*(1+(a+b+2)*x)/((a+1)*(a+2)))/4
  have hG : ContinuousAt G 0 := by unfold G; fun_prop
  have h := hG.tendsto.comp (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h0 : G 0=1/(4*(a+1)^2*(a+2)) := by
    dsimp [G]
    field_simp [show a+1≠0 by linarith,show a+2≠0 by linarith]
    ring
  rw [h0] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  simpa only [G,div_eq_mul_inv,one_mul,Function.comp_apply] using finiteLambda_square_sum ha hb hn

end
end jacobi.Jacobi
