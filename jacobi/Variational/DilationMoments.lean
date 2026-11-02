import jacobi.Variational.Dilation
import jacobi.Continuum.MultipleIntegrals
import jacobi.Continuum.MomentBounds
import jacobi.Variational.FredholmRelaxation

/-!
Article: jacobi, Appendix D.1 (strict concentration gain).
Mass-preserving concentration increases every actual cyclic spectral moment,
the actual top eigenvalue and the extended Fredholm functional, including poles.
The change of variables is performed on the genuine finite product integral.
Source: the cyclic trace formula and Lebesgue dilation on finite-dimensional space.
Use: combines all exponential links into the scalar exponent used in the dilation comparison.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter chebyshev2.Continuum
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

/-- Total length of the closed cycle through n+1 points on the line.
Use: combines all exponential links into the scalar exponent used in the dilation comparison.
Article: jacobi, Appendix D.1 (strict concentration gain).
-/
def cycleLength (n : ℕ) (z : Fin (n+1) → ℝ) : ℝ :=
  (∑ i : Fin n, |z i.castSucc-z i.succ|)+|z (Fin.last n)-z 0|

/-- The closed cycle has nonnegative length.
Use: concentration makes the negative exponential exponent less negative.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: each summand is an absolute distance. -/
theorem cycleLength_nonneg (n : ℕ) (z : Fin (n+1) → ℝ) : 0≤cycleLength n z :=
  add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _)

/-- Positive scalar multiplication rescales the entire cyclic length.
Use: cancels the spatial scale in the product-integral change of variables.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: absolute values and the finite sum are homogeneous for a positive scalar. -/
theorem cycleLength_smul (n : ℕ) (z : Fin (n+1) → ℝ) {t : ℝ} (ht : 0≤t) :
    cycleLength n (t • z)=t*cycleLength n z := by
  simp only [cycleLength,Pi.smul_apply,smul_eq_mul,← mul_sub,abs_mul,abs_of_nonneg ht]
  rw [← Finset.mul_sum]
  ring

/-- The cyclic integrand in fixed physical coordinates and with concentration scale t.
Use: one common integrand compares the actual moments before and after dilation.
Article: jacobi, Appendix D.1 (strict concentration gain).
-/
def dilationCycle (m : ℝ → ℝ) (n : ℕ) (t : ℝ) (z : Fin (n+1) → ℝ) : ℝ :=
  (∏ i,m (z i))*exp (-cycleLength n z/t)

/-- Combining exponential links gives exactly the ordinary cyclic integrand at unit scale.
Use: identifies the comparison integrals with the established actual operator trace formula.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: the product of exponentials is the exponential of the sum of their exponents. -/
theorem dilationCycle_one (m : ℝ → ℝ) (n : ℕ) :
    dilationCycle m n 1= jacobi.Continuum.cycleIntegrand m n := by
  funext z
  rw [jacobi.Continuum.cycleIntegrand_product,dilationCycle,div_one,← Real.exp_sum,
    mul_assoc,← Real.exp_add]
  congr 2
  simp only [cycleLength,Finset.sum_neg_distrib]
  ring

/-- The rescaled cyclic integrand is measurable for every positive scale.
Use: absolute integrability and every subsequent product-integral comparison.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: finite products and sums preserve measurability, as does the exponential. -/
theorem dilationCycle_measurable {m : ℝ → ℝ} (hm : Measurable m) (n : ℕ) (t : ℝ) :
    Measurable (dilationCycle m n t) := by
  unfold dilationCycle cycleLength
  fun_prop

/-- Absolute convergence of the cyclic integral at every positive concentration scale.
Use: licenses the moment comparison after the exact change of variables.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: the exponential is at most one, leaving the independent product of density norms. -/
theorem dilationCycle_integrable (m : L1Source) (n : ℕ) {t : ℝ} (ht : 0<t) :
    Integrable (dilationCycle m.value n t) := by
  have hi : Integrable (fun z : Fin (n+1) → ℝ => ∏ i, |m.value (z i)|) :=
    Integrable.fintype_prod fun _ => m.integrable.abs
  apply hi.mono' (dilationCycle_measurable m.measurable n t).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs,dilationCycle,abs_mul,Finset.abs_prod,abs_of_pos (exp_pos _)]
    exact mul_le_of_le_one_right (Finset.prod_nonneg fun _ _ => abs_nonneg _)
      (exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (cycleLength_nonneg n z)) ht.le))

/-- The density amplitude factors cancel exactly the finite-dimensional Lebesgue Jacobian.
Use: all moment monotonicity statements apply to the actual mass-preserving density dilation.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: factor t from each of the n+1 density values, then change variables
by scalar multiplication on R^(n+1). -/
theorem dilate_moment_integral (m : L1Source) (n : ℕ) {t : ℝ} (ht : 0<t) :
    (∑' j,(m.dilate t ht).spectrum j^(n+1))=
      ∫ z : Fin (n+1) → ℝ,dilationCycle m.value n t z := by
  -- The same n+1 amplitude factors and Jacobian occur in the literal trace integral.
  rw [L1Source.spectrum,jacobi.Continuum.moment_multiple_integral
    (m.dilate t ht).integrable (m.dilate t ht).measurable (m.dilate t ht).nonneg n,
    ← dilationCycle_one]
  have he : dilationCycle (m.dilate t ht).value n 1=
      fun z => t^(n+1)*dilationCycle m.value n t (t • z) := by
    funext z
    simp only [dilationCycle,L1Source.dilate,Finset.prod_mul_distrib,Finset.prod_const,
      Finset.card_univ,Fintype.card_fin,Pi.smul_apply,smul_eq_mul,div_one,
      cycleLength_smul n z ht.le]
    have hc : -(t*cycleLength n z)/t= -cycleLength n z := by field_simp
    rw [hc]
    ring
  rw [he,integral_const_mul,Measure.integral_comp_smul_of_nonneg volume _ t (hR := ht.le)]
  simp only [Module.finrank_pi,Fintype.card_fin,smul_eq_mul]
  rw [← mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ ht.ne'),one_mul]

/-- Every actual positive integer spectral moment increases under mass-preserving concentration.
Use: supplies all moment comparisons required for Fredholm dilation and multiplier regularity.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: after the exact change of variables, every nonnegative cyclic integrand
increases because its total distance is divided by t≥1. -/
theorem dilate_moment_mono (m : L1Source) (n : ℕ) {t : ℝ} (ht : 1≤t) :
    (∑' j,m.spectrum j^(n+1))≤∑' j,(m.dilate t (by linarith)).spectrum j^(n+1) := by
  -- Compare integrable functions in the unchanged coordinates, not spectra term by term.
  have ht0 : 0<t := by linarith
  rw [dilate_moment_integral m n ht0]
  change (∑' j,kernelEigenvalue m.integrable m.nonneg j^(n+1))≤_
  rw [jacobi.Continuum.moment_multiple_integral m.integrable m.measurable m.nonneg n,
    ← dilationCycle_one]
  apply integral_mono (dilationCycle_integrable m n zero_lt_one) (dilationCycle_integrable m n ht0)
  intro z
  apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (Finset.prod_nonneg fun _ _ => m.nonneg _)
  rw [div_one,le_div_iff₀ ht0]
  nlinarith [cycleLength_nonneg n z]

/-- The actual top eigenvalue also increases under spatial concentration.
Use: preserves the top constraint while deriving its stronger strict dilation estimate.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: take roots of all proved moment comparisons and pass to their actual top-eigenvalue limits. -/
theorem dilate_top_mono (m : L1Source) {t : ℝ} (ht : 1≤t) :
    observe m .top≤observe (m.dilate t (by linarith)) .top := by
  apply le_of_tendsto_of_tendsto
    (jacobi.Continuum.kernel_moment_root_limit m.integrable m.nonneg)
    (jacobi.Continuum.kernel_moment_root_limit (m.dilate t (by linarith)).integrable
      (m.dilate t (by linarith)).nonneg)
  exact Eventually.of_forall fun n => Real.rpow_le_rpow
    (tsum_nonneg fun j => pow_nonneg ((kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg j) _)
    (dilate_moment_mono m n ht) (by positivity)

/-- The extended Fredholm functional increases under concentration, with its poles retained.
Use: separates the qualitative moment comparison from the subsequent strictly positive gain.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: apply the proved nonnegative Fredholm moment expansion to all cyclic moment comparisons. -/
theorem dilate_fredholm_mono (m : L1Source) {s t : ℝ} (hs : 0≤s) (ht : 1≤t) :
    m.fredholm s≤(m.dilate t (by linarith)).fredholm s := by
  apply fredholm_mono_of_moments m (m.dilate t (by linarith)) hs
  intro n
  simpa only [Nat.add_assoc] using dilate_moment_mono m (n+1) ht

end
end jacobi.Variational
