import jacobi.Elliptic.Quadratures
import Mathlib.Tactic

/-!
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
The printed two-parameter weights reuse the common elliptic polynomial and
its verified endpoint estimates. Exact algebra identifies both presentations
of P and all turning, cutoff and amplitude parameters.
Source: literal rational polynomial identities; no numerical certificates.
Use: expresses the actual Green diagonal and the determinant quadrature.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Elliptic
set_option backward.isDefEq.respectTransparency false

/-- The printed affine Green normalization N_chi.
Use: expresses the actual Green diagonal and the determinant quadrature.
Article: jacobi, Theorem D.7.
-/
def nu (t c v : ℝ) : ℝ := 1-c*t*(1-v)

/-- The upper Green turning level corresponding to chi.
Use: parameterizes every nonzero Fredholm optimizing profile.
Article: jacobi, Theorem D.7.
-/
def peak (c : ℝ) : ℝ := 1/(2*(1-c))

/-- The distance from the switching level to the upper turning level.
Use: the profile coordinate is v=(g-g_e)/delta.
Article: jacobi, Theorem D.7.
-/
def delta (t c : ℝ) : ℝ := t*c/(2*(1-c))

/-- The Green switching level of the two-parameter Fredholm profile.
Use: tau=1 gives the full-support branch; tau<1 gives a compact core.
Article: jacobi, Theorem D.7.
-/
def edge (t c : ℝ) : ℝ := (1-t*c)/(2*(1-c))

/-- The positive amplitude of the normalized Fredholm Euler profile.
Use: gives the scalar first integral and the envelope coefficient.
Article: jacobi, Appendix D.4 (state quadratures and realized profiles).
-/
def amplitude (t c : ℝ) : ℝ := sqrt (3*c/t)/delta t c

/-- The Fredholm polynomial is exactly the common previously verified elliptic weight polynomial.
Use: all positivity, domination, derivative and weighted-mean estimates are reused unchanged.
Article: jacobi, Appendix D.4 (parameter derivatives and shape order).
Proof: expand both literal polynomial expressions and compare coefficients. -/
theorem P_identity (t c v : ℝ) : P t c v=(L t v)^2-v^3*nu t c v := by
  unfold P r q L nu
  ring

/-- The actual parameter domain makes the affine Green denominator positive uniformly on the integration interval.
Use: ensures convergence and dominated differentiation of the determinant quadrature.
Article: jacobi, Theorem D.7.
Proof: tau*(1-v) lies between zero and one, and chi is nonnegative. -/
theorem nu_bounds {t c v : ℝ} (ht : t∈Icc (0:ℝ) 1) (hc : c∈Ico (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) :
    0<1-c ∧ 1-c≤nu t c v ∧ nu t c v≤1 := by
  have hr : 0≤t*(1-v) := mul_nonneg ht.1 (by linarith [hv.2])
  have hr1 : t*(1-v)≤1 := (mul_le_mul ht.2 (by linarith [hv.1] : 1-v≤1) (by linarith [hv.2]) (by norm_num)).trans_eq (one_mul 1)
  unfold nu
  exact ⟨by linarith [hc.2],by nlinarith [mul_le_mul_of_nonneg_left hr1 hc.1],by nlinarith [mul_nonneg hc.1 hr]⟩

/-- The literal inverse turning and switching parameters lie in their asserted full geometric range.
Use: initializes the candidate Green profile and the optimizer-to-parameter identification.
Article: jacobi, Theorem D.7.
Proof: all rational denominators and the square-root amplitude are positive;
the difference g_0-g_e is exactly delta and the excess g_e-1/2 has factor 1-tau. -/
theorem parameter_bounds {t c : ℝ} (ht : t∈Ioc (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    0<delta t c ∧ (1/2:ℝ)≤edge t c ∧ edge t c<peak c ∧ 0<amplitude t c := by
  -- The cutoff includes equality precisely at the free-support endpoint tau=1.
  have hden : 0<2*(1-c) := by linarith [hc.2]
  have hd : 0<delta t c := div_pos (mul_pos ht.1 hc.1) hden
  have he : (1/2:ℝ)≤edge t c := by
    unfold edge
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hc.1.le]
  have hdiff : peak c-edge t c=delta t c := by unfold peak edge delta; ring
  exact ⟨hd,he,by linarith,div_pos (sqrt_pos.mpr (div_pos (mul_pos (by norm_num) hc.1) ht.1)) hd⟩

/-- The actual affine Green coordinate has its exact two printed normalizations.
Use: identifies the compact-core polynomial and the determinant density.
Article: jacobi, Theorem D.7.
Proof: clear the nonzero chi denominator and expand the affine expressions. -/
theorem affine_coordinate {t c : ℝ} (hc : c≠1) (v : ℝ) :
    edge t c+delta t c*v=peak c*nu t c v ∧
    2*(edge t c+delta t c*v)-1=(2*peak c-1)*L t v := by
  have hden : 1-c≠0 := sub_ne_zero.mpr (Ne.symm hc)
  unfold edge delta peak nu L
  constructor <;> field_simp <;> ring

end
end jacobi.Fredholm
