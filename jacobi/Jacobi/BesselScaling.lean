import jacobi.Jacobi.Polynomial
import jacobi.Bessel.Pochhammer
import Mathlib.Analysis.Normed.Group.Tannery

/-!
Article: jacobi, Proposition A.1.
The exact finite Jacobi coefficients are compared with the actual Bessel
coefficients. Their correction product tends to one at each degree and
has a common exponential bound, including all terminated coefficients.
Source: the classical hypergeometric proof of the Mehler--Heine limit.
Use: separates the genuine entire Bessel coefficient from the degree-dependent finite product.
-/
namespace jacobi.Jacobi
noncomputable section
open Complex Set Polynomial Filter
open scoped Nat Topology
set_option backward.isDefEq.respectTransparency false

/-- The exact finite-degree correction in the Jacobi-to-Bessel coefficient comparison.
Use: separates the genuine entire Bessel coefficient from the degree-dependent finite product.
Article: jacobi, Proposition A.1.
-/
def correction (q : ℂ) (n k : ℕ) : ℂ :=
  ∏ j∈Finset.range k,(1-(j:ℂ)/n)*(1+(q+j)/n)

/-- The correction product has its exact rising-factorial expression at every degree.
Use: identifies the actual Jacobi coefficients with the actual normalized Bessel coefficients.
Article: jacobi, Proposition A.1.
Proof: both sides start at one. Their next-degree factors agree by
the actual Pochhammer evaluation recurrence and ordinary nonzero-degree field algebra. -/
theorem correction_pochhammer (q : ℂ) {n : ℕ} (hn : 0<n) (k : ℕ) :
    correction q n k=(-1:ℂ)^k*(ascPochhammer ℂ k).eval (-(n:ℂ))*
      (ascPochhammer ℂ k).eval (n+q)/(n:ℂ)^(2*k) := by
  -- The finite product retains the actual terminating factor when k>n.
  have hn0 : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
  induction k with
  | zero => simp [correction]
  | succ k ih =>
    simp only [correction,Finset.prod_range_succ] at ih ⊢
    rw [ih,ascPochhammer_succ_eval,ascPochhammer_succ_eval,pow_succ]
    field_simp [hn0]
    ring

/-- Every finite Jacobi term at its exact squared-edge scaling is the corresponding Bessel term times the correction product.
Use: transfers the proved infinite Bessel convergence to the genuine finite Jacobi family.
Article: jacobi, Proposition A.1.
Proof: substitute the literal rising-factorial formulas on both sides.
The two powers of minus one cancel, and the exact degree powers give
the factor 1/(4*n^2). Only the proved nonzero normalization factors are cancelled. -/
theorem scaled_coefficient {a b : ℂ} (ha : -1<a.re) {n : ℕ} (hn : 0<n) (k : ℕ) (z : ℂ) :
    coefficient a b n k*(z/(4*(n:ℂ)^2))^k=
      jacobi.Bessel.coefficient a k*z^k*correction (a+b+1) n k := by
  -- This is an exact identity of the two actual special-function coefficient formulas.
  rw [correction_pochhammer _ hn,jacobi.Bessel.coefficient_pochhammer ha]
  have hsign : (-1/4:ℂ)^k*(-1:ℂ)^k=(1/4:ℂ)^k := by rw [← mul_pow]; congr 1; ring
  have harg : (n:ℂ)+a+b+1=n+(a+b+1) := by ring
  unfold coefficient ordinaryHypergeometricCoefficient
  rw [harg]
  rw [show (-1/4:ℂ)^k/((k.factorial:ℂ)*(ascPochhammer ℂ k).eval (a+1))*z^k*
      ((-1:ℂ)^k*(ascPochhammer ℂ k).eval (-(n:ℂ))*
        (ascPochhammer ℂ k).eval (n+(a+b+1))/(n:ℂ)^(2*k))=
      ((-1/4:ℂ)^k*(-1:ℂ)^k)*z^k*(ascPochhammer ℂ k).eval (-(n:ℂ))*
        (ascPochhammer ℂ k).eval (n+(a+b+1))/
        (((k.factorial:ℂ)*(ascPochhammer ℂ k).eval (a+1))*(n:ℂ)^(2*k)) by ring,
    hsign,div_pow,div_pow,mul_pow,pow_mul]
  ring

/-- Every fixed correction degree tends to one as the Jacobi degree tends to infinity.
Use: proves the actual coefficient limits in Mehler--Heine.
Article: jacobi, Proposition A.1.
Proof: reciprocal natural degree tends to zero in the complex field.
Each fixed product factor therefore tends to one, and finite products preserve limits. -/
theorem correction_limit (q : ℂ) (k : ℕ) :
    Tendsto (fun n : ℕ => correction q n k) atTop (𝓝 1) := by
  -- Each factor is fixed before taking the degree limit.
  have hinv : Tendsto (fun n : ℕ => (n:ℂ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have hf (j : ℕ) : Tendsto (fun n : ℕ => (1-(j:ℂ)/n)*(1+(q+j)/n)) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (1:ℂ))).sub (hinv.const_mul (j:ℂ))).mul
      ((tendsto_const_nhds (x := (1:ℂ))).add (hinv.const_mul (q+j)))
    simpa only [mul_zero,sub_zero,add_zero,one_mul,div_eq_mul_inv] using h
  simpa only [correction,Finset.prod_const_one] using tendsto_finsetProd _ (fun j _ => hf j)

/-- The genuine correction product terminates beyond the Jacobi degree.
Use: finite sums and infinite sums coincide in the actual scaled Jacobi family.
Article: jacobi, Proposition A.1.
Proof: the finite product contains j=n, whose first factor is 1-n/n=0 at positive degree. -/
theorem correction_terminates (q : ℂ) {n k : ℕ} (hn : 0<n) (hk : n<k) :
    correction q n k=0 := by
  unfold correction
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hk)
  have hn0 : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
  simp [hn0]

/-- A single exponential bound controls every actual Jacobi correction coefficient at every positive degree.
Use: gives the summable Bessel majorant required for the full Mehler--Heine limit.
Article: jacobi, Proposition A.1.
Proof: below the terminating degree each normalized natural j/n is at
most one. The two complex factors have norms at most two and 2+norm(q).
Multiply the finite bounds. Beyond the degree the actual correction is zero. -/
theorem correction_bound (q : ℂ) {n : ℕ} (hn : 0<n) (k : ℕ) :
    ‖correction q n k‖≤(2*(2+‖q‖))^k := by
  -- Termination is used rather than incorrectly bounding arbitrarily large j/n.
  by_cases hk : k≤n
  · have hfactor (j : ℕ) (hj : j∈Finset.range k) :
        ‖(1-(j:ℂ)/n)*(1+(q+j)/n)‖≤2*(2+‖q‖) := by
      have hjn : j≤n := (Finset.mem_range.mp hj).le.trans hk
      have hnr : (0:ℝ)<n := by exact_mod_cast hn
      have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
      have hjdiv : ‖(j:ℂ)/n‖≤1 := by
        rw [norm_div,Complex.norm_natCast,Complex.norm_natCast]
        exact (div_le_one hnr).mpr (by exact_mod_cast hjn)
      have hqdiv : ‖q/(n:ℂ)‖≤‖q‖ := by
        rw [norm_div,Complex.norm_natCast]
        exact div_le_self (norm_nonneg q) hn1
      have hfirst : ‖1-(j:ℂ)/n‖≤2 := by
        have h := norm_sub_le (1:ℂ) ((j:ℂ)/n)
        norm_num only [norm_one] at h
        linarith
      have hsecond : ‖1+(q+j)/n‖≤2+‖q‖ := by
        rw [add_div]
        have h1 := norm_add_le (q/(n:ℂ)) ((j:ℂ)/n)
        have h2 := norm_add_le (1:ℂ) (q/(n:ℂ)+(j:ℂ)/n)
        norm_num only [norm_one] at h2
        linarith
      rw [norm_mul]
      exact mul_le_mul hfirst hsecond (norm_nonneg _) (by norm_num)
    have hprod := Finset.prod_le_prod₀ (fun j (_ : j∈Finset.range k) => norm_nonneg
      ((1-(j:ℂ)/n)*(1+(q+j)/n))) hfactor
    simpa only [correction,norm_prod,Finset.prod_const,Finset.card_range] using hprod
  · rw [correction_terminates q hn (lt_of_not_ge hk),norm_zero]
    positivity

/-- The actual scaled Jacobi function equals the corrected entire Bessel series at every positive finite degree.
Use: dominated convergence is applied to the original polynomial, not an auxiliary approximation.
Article: jacobi, Proposition A.1.
Proof: use the genuine finite Jacobi expansion at the scaled argument,
substitute the exact coefficient comparison and restore the infinite sum.
Every restored term past degree n is zero by the proved correction termination. -/
theorem normalized_scaled_eq_tsum {a b : ℂ} (ha : -1<a.re)
    {n : ℕ} (hn : 0<n) (z : ℂ) :
    normalized a b n (1-z/(2*(n:ℂ)^2))=
      ∑' k,jacobi.Bessel.coefficient a k*z^k*correction (a+b+1) n k := by
  -- Both sides are the same actual finite polynomial at this finite degree.
  rw [normalized_eq_sum]
  have harg : (1-(1-z/(2*(n:ℂ)^2)))/2=z/(4*(n:ℂ)^2) := by ring
  simp only [harg]
  rw [tsum_eq_sum (s := Finset.range (n+1)) (fun k hk => by
    have hnk : n<k := by
      have hh : n+1≤k := by simpa only [Finset.mem_range,not_lt] using hk
      omega
    rw [correction_terminates _ hn hnk,mul_zero])]
  exact Finset.sum_congr rfl (fun k _ => scaled_coefficient ha hn k z)

end
end jacobi.Jacobi
