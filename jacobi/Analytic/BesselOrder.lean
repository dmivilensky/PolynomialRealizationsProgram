import jacobi.Bessel.Convergence
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
Article: jacobi, Lemma E.1.
The actual normalized Bessel function is holomorphic in its original
complex order throughout Re(alpha)>-1. A genuine exponential/factorial
majorant is uniform on every order half-plane with a positive margin.
This supplies order analyticity for the later implicit continuation of
simple zeros; uniform continuation of the entire numbered zero list
additionally requires the separate complex Hankel estimates.
Use: coefficient_order_analytic and normalized_order_holomorphic use genuine neighborhoods of every admissible source order.
-/
namespace jacobi.Bessel
noncomputable section
open Complex Real Set Filter
open scoped Topology

/-- The original admissible complex order half-plane is open.
Use: coefficient_order_analytic and normalized_order_holomorphic use genuine neighborhoods of every admissible source order.
Article: jacobi, Lemma E.1.
Proof: it is the inverse image of an open real ray under the continuous real-part map. -/
theorem order_halfPlane_open : IsOpen {a:ℂ | -1<a.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- Every actual normalized Bessel coefficient is analytic in the original order half-plane.
Use: normalized_order_holomorphic sums the actual parameter-dependent series, rather than assuming order analyticity of a replacement special function.
Article: jacobi, Lemma E.1.
Source: the Bessel coefficient recurrence, DLMF 10.2.2.
Proof: the zeroth coefficient is identically one locally. The actual
coefficient recurrence divides the preceding analytic coefficient by
an affine factor with positive real part throughout the original range. -/
theorem coefficient_order_analytic {a:ℂ} (ha:-1<a.re) (n:ℕ) :
    AnalyticAt ℂ (fun b => coefficient b n) a := by
  -- The recurrence and normalization are identities of the original Gamma-normalized 0F1 coefficients.
  have hU : {b:ℂ | -1<b.re}∈𝓝 a := order_halfPlane_open.mem_nhds ha
  induction n with
  | zero =>
    apply (analyticAt_const (v:=(1:ℂ))).congr
    filter_upwards [hU] with b hb
    exact (coefficient_zero hb).symm
  | succ n ih =>
    have hn : (4:ℂ)*(n+1)*(a+1+n)≠0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast (Nat.succ_ne_zero n)))
        (order_nonzero ha n).1
    have h : AnalyticAt ℂ (fun b:ℂ => -coefficient b n/(4*(n+1)*(b+1+n))) a := by
      fun_prop
    apply h.congr
    filter_upwards [hU] with b hb
    exact (coefficient_succ hb n).symm

/-- The actual normalized coefficients have a factorial majorant uniform in every complex order with a fixed positive real-part margin.
Use: normalized_order_holomorphic has a genuine summable bound on each entire order neighborhood.
Article: jacobi, Lemma E.1.
Proof: the actual shifted recurrence factor has norm at least delta.
Induction therefore bounds each coefficient by (1/(4delta))^n/n!;
every division uses a strictly positive real denominator. -/
theorem coefficient_order_bound {δ:ℝ} (hδ:0<δ) {a:ℂ} (ha:δ≤a.re+1) (n:ℕ) :
    ‖coefficient a n‖≤(1/(4*δ))^n/(n.factorial:ℝ) := by
  -- A bound independent of the imaginary order is enough for the original local holomorphic series.
  have ha' : -1<a.re := by linarith
  induction n with
  | zero => simp only [coefficient_zero ha',norm_one,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,le_refl]
  | succ n ih =>
    have hn : δ≤‖a+1+n‖ := by
      have hr := Complex.re_le_norm (a+1+n)
      simp only [Complex.add_re,Complex.one_re,Complex.natCast_re] at hr
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    have hq : 0<4*(n+1:ℝ)*δ := by positivity
    have hnorm : ‖(4:ℂ)*(n+1)*(a+1+n)‖=4*(n+1:ℝ)*‖a+1+n‖ := by
      rw [norm_mul,norm_mul]
      norm_cast
    calc
      ‖coefficient a (n+1)‖=‖coefficient a n‖/(4*(n+1:ℝ)*‖a+1+n‖) := by
        rw [coefficient_succ ha',norm_div,norm_neg,hnorm]
      _≤‖coefficient a n‖/(4*(n+1:ℝ)*δ) := div_le_div_of_nonneg_left (norm_nonneg _) hq
        (mul_le_mul_of_nonneg_left hn (by positivity))
      _≤((1/(4*δ))^n/(n.factorial:ℝ))/(4*(n+1:ℝ)*δ) := div_le_div_of_nonneg_right ih hq.le
      _=(1/(4*δ))^(n+1)/((n+1).factorial:ℝ) := by
        rw [Nat.factorial_succ,pow_succ]
        push_cast
        field_simp [hδ.ne']

/-- The actual normalized Bessel function is holomorphic in its order on the complete original complex half-plane.
Use:, 's simple-zero implicit continuation starts from this proved order dependence of the same original Bessel function.
Article: jacobi, Lemma E.1.
Source: Weierstrass' theorem for locally uniformly convergent holomorphic series.
Proof: near each source order keep half its positive real-part margin.
The proved actual coefficient bound times |z|^n is a summable exponential
series independent of the order in that neighborhood. Apply the community
holomorphic-series theorem and identify its sum with the actual normalized Bessel function. -/
theorem normalized_order_holomorphic (z:ℂ) :
    DifferentiableOn ℂ (fun a => normalized a z) {a:ℂ | -1<a.re} := by
  -- The spectral argument is arbitrary and fixed; the entire original coefficient series is retained.
  intro a ha
  change -1<a.re at ha
  let δ : ℝ := (a.re+1)/2
  have hδ : 0<δ := by dsimp [δ]; linarith
  let U : Set ℂ := {b | δ<b.re+1}
  have hU : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.add_const 1)
  have haU : a∈U := by dsimp [U,δ]; linarith
  have hterms (n:ℕ) : DifferentiableOn ℂ (fun b:ℂ => coefficient b n*z^n) U := by
    intro b hb
    have hb' : -1<b.re := by dsimp [U] at hb; linarith
    exact ((coefficient_order_analytic hb' n).differentiableAt.mul_const _).differentiableWithinAt
  have hbnd (n:ℕ) (b:ℂ) (hb:b∈U) :
      ‖coefficient b n*z^n‖≤(‖z‖/(4*δ))^n/(n.factorial:ℝ) := by
    rw [norm_mul,norm_pow]
    calc
      _≤((1/(4*δ))^n/(n.factorial:ℝ))*‖z‖^n :=
        mul_le_mul_of_nonneg_right (coefficient_order_bound hδ (show δ≤b.re+1 from hb.le) n) (by positivity)
      _=_ := by rw [div_mul_eq_mul_div,← mul_pow]; congr 2; ring
  have h := Complex.differentiableOn_tsum_of_summable_norm
    (Real.summable_pow_div_factorial (‖z‖/(4*δ))) hterms hU hbnd
  have he : (fun b:ℂ => ∑'n,coefficient b n*z^n)=(fun b => normalized b z) := by
    ext b
    exact (normalized_eq_tsum b z).symm
  rw [he] at h
  exact (h.differentiableAt (hU.mem_nhds haU)).differentiableWithinAt

end
end jacobi.Bessel
