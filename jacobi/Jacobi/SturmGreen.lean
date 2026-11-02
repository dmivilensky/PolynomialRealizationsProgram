import jacobi.Jacobi.Weight
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Article: jacobi, Proposition A.1.
The actual Jacobi differential operator is symmetric on all polynomial
test functions for the true singular Jacobi weight. Its boundary terms
vanish for the entire parameter range alpha,beta>-1.
Source: the classical Jacobi Sturm--Liouville Green identity.
Use: the weighted Green identity identifies its actual polynomial eigenfunctions as orthogonal.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial Real Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- The literal shifted Jacobi differential operator applied to a real polynomial.
Use: the weighted Green identity identifies its actual polynomial eigenfunctions as orthogonal.
Article: jacobi, Proposition A.1.
-/
def sturm (a b : ℝ) (p : Polynomial ℝ) (t : ℝ) : ℝ :=
  t*(1-t)*p.derivative.derivative.eval t+(a+1-(a+b+2)*t)*p.derivative.eval t

/-- The actual Jacobi differential operator applied to any polynomial is continuous.
Use: all weighted Sturm products in the Green identity have genuine convergent integrals.
Article: jacobi, Proposition A.1.
Proof: every evaluated polynomial and every affine coefficient is continuous, and continuity is preserved by sums and products. -/
theorem sturm_continuous (a b : ℝ) (p : Polynomial ℝ) : Continuous (sturm a b p) := by
  unfold sturm
  fun_prop

/-- The actual shifted Jacobi polynomials satisfy the literal Sturm eigenvalue equation.
Use: the genuine weighted Green identity gives pairwise orthogonality.
Article: jacobi, Proposition A.1.
Proof: use the already proved evaluation of the exact polynomial differential equation. -/
theorem shifted_sturm_equation {a b : ℝ} (ha : -1<a) (n : ℕ) (t : ℝ) :
    sturm a b (shiftedPolynomial a b n) t+
      (n:ℝ)*(n+a+b+1)*(shiftedPolynomial a b n).eval t=0 :=
  shiftedPolynomial_equation_eval ha n t

/-- The literal Jacobi Sturm operator has its genuine weighted Green identity for every pair of real polynomials.
Use: proves orthogonality of the actual Jacobi family, without assuming a positive spectral measure or missing endpoint regularity.
Article: jacobi, Proposition A.1.
Proof: differentiate the actual flux-weighted Wronskian. Its two
operator terms are integrable because the weight is integrable and the
polynomial multipliers are continuous. The flux is continuous and zero
at both endpoints, so the genuine fundamental theorem makes the integral zero. -/
theorem sturm_green {a b : ℝ} (ha : -1<a) (hb : -1<b) (p q : Polynomial ℝ) :
    ∫ t in (0:ℝ)..1,weight a b t*(sturm a b p t*q.eval t-p.eval t*sturm a b q t)=0 := by
  -- All endpoint and convergence facts concern the original possibly singular Jacobi weight.
  let W := fun t : ℝ => fluxWeight a b t*(p.derivative.eval t*q.eval t-p.eval t*q.derivative.eval t)
  have hflux := fluxWeight_properties ha hb
  have hcont : Continuous W := hflux.1.mul
    ((p.derivative.continuous.mul q.continuous).sub (p.continuous.mul q.derivative.continuous))
  have hi := weight_mul_integrable ha hb
    (((sturm_continuous a b p).mul q.continuous).sub (p.continuous.mul (sturm_continuous a b q)))
  have hd (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
      HasDerivAt W (weight a b t*(sturm a b p t*q.eval t-p.eval t*sturm a b q t)) t := by
    have h := (fluxWeight_hasDerivAt a b ht).mul
      (((p.derivative.hasDerivAt t).mul (q.hasDerivAt t)).sub
        ((p.hasDerivAt t).mul (q.derivative.hasDerivAt t)))
    convert h using 1
    dsimp only [sturm,Pi.mul_apply,Pi.sub_apply]
    rw [fluxWeight_eq a b ht]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0:ℝ)≤1) hcont.continuousOn hd hi
  simpa only [W,hflux.2.1,hflux.2.2,zero_mul,sub_self] using h

/-- The true Jacobi Sturm eigenvalues increase strictly with polynomial degree for every alpha,beta>-1.
Use: discharges the nonzero spectral difference needed in polynomial orthogonality.
Article: jacobi, Proposition A.1.
Proof: the next-degree difference is 2*n+alpha+beta+2, strictly positive in the full stated range. -/
theorem sturm_eigenvalue_strictMono {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    StrictMono (fun n : ℕ => (n:ℝ)*(n+a+b+1)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- The actual shifted Jacobi polynomials of different degrees are orthogonal for their genuine weight.
Use: the complete lower-degree orthogonality and finite zero-location theorems.
Article: jacobi, Proposition A.1.
Proof: substitute both actual Sturm eigenvalue equations into the
proved weighted Green identity. Its integrand is the nonzero eigenvalue
difference times the original weighted polynomial product, whose integral must vanish. -/
theorem shiftedPolynomial_orthogonal {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {n m : ℕ} (hnm : n≠m) :
    ∫ t in (0:ℝ)..1,weight a b t*((shiftedPolynomial a b n).eval t*(shiftedPolynomial a b m).eval t)=0 := by
  -- The source polynomials are independently defined; their orthogonality is a proved consequence of Green's identity.
  let p := shiftedPolynomial a b n
  let q := shiftedPolynomial a b m
  let D := (m:ℝ)*(m+a+b+1)-(n:ℝ)*(n+a+b+1)
  have hD : D≠0 := sub_ne_zero.mpr ((sturm_eigenvalue_strictMono ha hb).injective.ne hnm.symm)
  have he : (fun t => weight a b t*(sturm a b p t*q.eval t-p.eval t*sturm a b q t))=
      fun t => D*(weight a b t*(p.eval t*q.eval t)) := by
    funext t
    dsimp only [D]
    linear_combination weight a b t*q.eval t*(shifted_sturm_equation (b := b) ha n t)-
      weight a b t*p.eval t*(shifted_sturm_equation (b := b) ha m t)
  have h := sturm_green ha hb p q
  rw [he,intervalIntegral.integral_const_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hD

end
end jacobi.Jacobi
