import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Tactic

/-!
Article: jacobi, Proposition A.1.
The normalized Bessel function is defined in its spectral variable z, so
its positive zeros will be j_(alpha,k)^2. The existing regularized 0F1
series supplies genuine convergence and complex analyticity everywhere.
Source: the Bessel power series, DLMF 10.2.2, realized by mathlib's regularized hypergeometric function.
Use: its zeros supply the edge data, and its product supplies Fredholm spectral sums.
-/
namespace jacobi.Bessel
noncomputable section
open Complex Set Filter
open scoped Nat Topology
set_option backward.isDefEq.respectTransparency false

/-- The entire normalized Bessel function in the spectral variable.
Use: its zeros supply the edge data, and its product supplies Fredholm spectral sums.
Article: jacobi, Theorem 2.1.
-/
def normalized (a z : ℂ) : ℂ :=
  Gamma (a+1)*regularizedHGFun 0 {a+1} (-z/4)

/-- The literal coefficients of the normalized Bessel spectral power series.
Use: computes the initial moments and gives the exact differential-equation recurrence.
Article: jacobi, Proposition A.1.
-/
def coefficient (a : ℂ) (n : ℕ) : ℂ :=
  Gamma (a+1)*(-1/4:ℂ)^n*regularizedHGFunCoeff 0 {a+1} n

/-- The community 0F1 series used here has infinite convergence radius for every order.
Use: rules out a formal or divergent-series interpretation of the normalized Bessel function.
Article: jacobi, Proposition A.1.
Proof: the numerator parameter multiset is empty and the denominator has one parameter; apply mathlib's proved radius theorem. -/
theorem radius (a : ℂ) : (regularizedHGFunSeries 0 {a+1}).radius=⊤ := by
  apply radius_regularizedHGFunSeries_eq_top
  simp

/-- The actual normalized Bessel function is analytic at every complex spectral argument.
Use: its real zeros can later be identified with the entire canonical product and differentiated.
Article: jacobi, Theorem 2.1.
Proof: the existing 0F1 sum is analytic throughout its infinite convergence
ball. Compose with the actual linear argument -z/4 and multiply by the constant Gamma normalization. -/
theorem normalized_analytic (a z : ℂ) : AnalyticAt ℂ (normalized a) z := by
  -- Infinite radius supplies analyticity of the actual sum, rather than an assumed analytic solution.
  have h : AnalyticAt ℂ (regularizedHGFun 0 {a+1}) (-z/4) := by
    apply (regularizedHGFunSeries (0:Multiset ℂ) {a+1}).analyticOnNhd
    rw [radius]
    simp
  exact analyticAt_const.mul (h.comp (f := fun w : ℂ => -w/4)
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => -w/4) z))

/-- Every normalized Bessel coefficient has the exact Gamma and factorial formula.
Use: checks all signs and factors of four in the differential equation and Rayleigh moments.
Article: jacobi, Theorem 2.1.
Proof: the numerator parameter product is empty and the denominator parameter product is a singleton. -/
theorem coefficient_formula (a : ℂ) (n : ℕ) :
    coefficient a n=Gamma (a+1)*(-1/4:ℂ)^n/((n.factorial:ℂ)*Gamma (a+1+n)) := by
  simp [coefficient,regularizedHGFunCoeff,div_eq_mul_inv]

/-- The normalized Bessel function is the sum of its literal spectral power series at every complex point.
Use: connects the analytic function with coefficient comparisons and the later canonical product.
Article: jacobi, Theorem 2.1.
Proof: unfold the proved hypergeometric series sum, move the constant
Gamma factor inside the sum, and collect the power (-z/4)^n into its coefficient. -/
theorem normalized_eq_tsum (a z : ℂ) : normalized a z=∑' n,coefficient a n*z^n := by
  -- The actual infinite radius established above ensures that this original series converges everywhere.
  unfold normalized regularizedHGFun regularizedHGFunSeries FormalMultilinearSeries.sum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [FormalMultilinearSeries.ofScalars_apply_eq]
  simp only [smul_eq_mul,coefficient]
  rw [show -z/4=(-1/4:ℂ)*z by ring,mul_pow]
  ring

/-- The admissible real-order range gives a nonzero Gamma normalization and nonzero recurrence denominators.
Use: the normalized entire function has value one at zero and a genuine nonsingular coefficient recurrence.
Article: jacobi, Theorem 2.1.
Proof: every shifted order has positive real part, so the proved Gamma nonvanishing theorem applies. -/
theorem order_nonzero {a : ℂ} (ha : -1<a.re) (n : ℕ) :
    a+1+n≠0 ∧ Gamma (a+1+n)≠0 := by
  have hp : 0<(a+1+n).re := by
    simp only [add_re,one_re,natCast_re]
    have hn : (0:ℝ)≤n := Nat.cast_nonneg n
    linarith
  exact ⟨fun h => by rw [h,zero_re] at hp; exact lt_irrefl _ hp,Gamma_ne_zero_of_re_pos hp⟩

/-- The actual normalized function has its required nonzero central value throughout the stated order range.
Use: excludes a spurious zero at the origin before positive-zero enumeration and canonical product arguments.
Article: jacobi, Lemma 1.3.
Proof: only the zeroth coefficient survives and its two Gamma factors cancel. -/
theorem normalized_zero {a : ℂ} (ha : -1<a.re) : normalized a 0=1 := by
  rw [normalized_eq_tsum]
  have hg : Gamma (a+1)≠0 := by simpa only [Nat.cast_zero,add_zero] using (order_nonzero ha 0).2
  rw [tsum_eq_single 0 (fun n hn => by rw [zero_pow hn,mul_zero])]
  simp [coefficient_formula,hg]

/-- Every actual normalized coefficient satisfies the precise Bessel differential-equation recurrence.
Use: termwise differentiation gives 4*z*F''+4*(alpha+1)*F'+F=0 and its first Rayleigh coefficients.
Article: jacobi, Theorem 2.1.
Proof: apply the existing hypergeometric coefficient recurrence at the
positive shifted order and collect the exact factorial, order and scaling factors. -/
theorem coefficient_succ {a : ℂ} (ha : -1<a.re) (n : ℕ) :
    coefficient a (n+1)=-coefficient a n/(4*(n+1)*(a+1+n)) := by
  -- The actual order range, rather than a formal division convention, excludes every denominator zero.
  have hshift := (order_nonzero ha n).1
  have hneq : a+1≠-(n:ℂ) := by intro hz; apply hshift; rw [hz,neg_add_cancel]
  have h := regularizedHGFunCoeff_add_one (a := (0:Multiset ℂ)) (b := {a+1}) (n := n)
    (by simpa only [Multiset.mem_singleton] using fun k hk => hk ▸ hneq)
  simp only [Multiset.map_zero,Multiset.prod_zero,Multiset.map_singleton,Multiset.prod_singleton] at h
  unfold coefficient
  rw [h,pow_succ]
  field_simp

end
end jacobi.Bessel
