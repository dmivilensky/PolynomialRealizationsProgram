import jacobi.Bessel.ZeroLocation
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
Article: jacobi, Proposition C.4.
The actual entire normalized series is real on the real axis. Its real
restriction and the real parts of its actual complex derivatives satisfy
the genuine real differential equation, not an independently chosen ODE.
Source: the real coefficients of the classical normalized Bessel series.
Use: proves reality of the actual entire function before its real Sturm analysis.
-/
namespace jacobi.Bessel
noncomputable section
open Complex
open scoped ComplexConjugate

/-- Every original normalized Bessel coefficient at real order is fixed by conjugation.
Use: proves reality of the actual entire function before its real Sturm analysis.
Article: jacobi, Proposition C.4.
Proof: the genuine Gamma coefficient formula and conjugation of Gamma leave each real parameter fixed. -/
theorem coefficient_conj (a : ℝ) (n : ℕ) :
    conj (coefficient (a:ℂ) n)=coefficient (a:ℂ) n := by
  rw [coefficient_formula]
  simp [← Gamma_conj,Complex.conj_ofNat]

/-- The actual entire normalized Bessel function is real on the real spectral axis.
Use: transfers its genuine real Sturm zeros to zeros of the original complex function.
Article: jacobi, Proposition C.4.
Proof: conjugation is continuous and maps the genuinely convergent
series to itself term by term. Uniqueness of its sum gives conjugate symmetry. -/
theorem normalized_conj (a x : ℝ) :
    conj (normalized (a:ℂ) (x:ℂ))=normalized (a:ℂ) (x:ℂ) := by
  have h := (normalized_hasSum (a:ℂ) (x:ℂ)).map Complex.conjCLE Complex.conjCLE.continuous
  change HasSum (fun n => conj (coefficient (a:ℂ) n*(x:ℂ)^n))
    (conj (normalized (a:ℂ) (x:ℂ))) at h
  have hh : HasSum (fun n => coefficient (a:ℂ) n*(x:ℂ)^n)
      (conj (normalized (a:ℂ) (x:ℂ))) := by
    simpa only [_root_.map_mul,_root_.map_pow,coefficient_conj,conj_ofReal] using h
  exact hh.unique (normalized_hasSum (a:ℂ) (x:ℂ))

/-- The real restriction of the original entire normalized Bessel function.
Use: defines the genuine radial solution in the oscillation proof.
Article: jacobi, Lemma 1.3.
-/
def realNormalized (a x : ℝ) : ℝ := (normalized (a:ℂ) (x:ℂ)).re

/-- The real part of the genuine complex first derivative of the normalized Bessel function.
Use: supplies the actual real derivative and the Liouville-transformed slope.
Article: jacobi, Lemma 1.3.
-/
def realSlope (a x : ℝ) : ℝ := (deriv (normalized (a:ℂ)) (x:ℂ)).re

/-- The real part of the genuine complex second derivative of the normalized Bessel function.
Use: supplies the actual second derivative and its exact real differential equation.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
-/
def realAcceleration (a x : ℝ) : ℝ := (deriv (deriv (normalized (a:ℂ))) (x:ℂ)).re

/-- The real restriction vanishes exactly when the original entire function vanishes there.
Use: the oscillation argument produces genuine complex spectral zeros.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: conjugate symmetry makes the imaginary part zero, so the real part detects the full value. -/
theorem realNormalized_zero_iff (a x : ℝ) :
    realNormalized a x=0 ↔ normalized (a:ℂ) (x:ℂ)=0 := by
  have he : normalized (a:ℂ) (x:ℂ)=(realNormalized a x:ℂ) :=
    (Complex.conj_eq_iff_re.mp (normalized_conj a x)).symm
  rw [he,Complex.ofReal_eq_zero]

/-- The declared real slope is the actual ordinary derivative of the real restriction.
Use: the real differential equation and the transformed-wave chain rule.
Article: jacobi, Lemma 1.3.
Proof: restrict the genuine complex derivative to real inputs, then apply the real-part linear map. -/
theorem realNormalized_hasDerivAt (a x : ℝ) :
    HasDerivAt (realNormalized a) (realSlope a x) x :=
  (normalized_analytic (a:ℂ) (x:ℂ)).differentiableAt.hasDerivAt.real_of_complex

/-- The declared real acceleration is the actual derivative of the real slope.
Use: computes the second derivative of the Liouville-transformed solution.
Article: jacobi, Lemma 1.3.
Proof: the analytic complex first derivative is differentiable; restrict and take its real part. -/
theorem realSlope_hasDerivAt (a x : ℝ) :
    HasDerivAt (realSlope a) (realAcceleration a x) x :=
  (normalized_analytic (a:ℂ) (x:ℂ)).deriv.differentiableAt.hasDerivAt.real_of_complex

/-- The actual real normalized Bessel function satisfies the literal real spectral equation.
Use: transforms to the restoring wave equation that forces arbitrarily large zeros.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: take real parts in the already proved complex entire differential equation. -/
theorem realNormalized_equation {a : ℝ} (ha : -1<a) (x : ℝ) :
    4*x*realAcceleration a x+4*(a+1)*realSlope a x+realNormalized a x=0 := by
  have h := congrArg Complex.re (normalized_equation (a := (a:ℂ)) (by simpa using ha) (x:ℂ))
  simpa [realAcceleration,realSlope,realNormalized,Complex.mul_re] using h

/-- The genuine complex derivative along the real axis is the real slope itself, embedded in the complex field.
Use: transfers simplicity of actual complex zeros to the real sign-change argument.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: reality identifies the complex restriction with the embedded
real function. Uniqueness of its real-parameter derivative identifies the two slopes. -/
theorem realSlope_complex (a x : ℝ) :
    (realSlope a x:ℂ)=deriv (normalized (a:ℂ)) (x:ℂ) := by
  -- Both slopes differentiate the same actual real-axis restriction.
  have he : (fun y : ℝ => (realNormalized a y:ℂ))=fun y : ℝ => normalized (a:ℂ) (y:ℂ) :=
    funext fun y => Complex.conj_eq_iff_re.mp (normalized_conj a y)
  have h := (realNormalized_hasDerivAt a x).ofReal_comp
  rw [he] at h
  exact h.unique ((normalized_analytic (a:ℂ) (x:ℂ)).differentiableAt.hasDerivAt.comp_ofReal)

/-- The real normalized Bessel slope is nonzero at every genuine spectral zero.
Use: excludes local extrema and proves stable sign changes for transfer to the finite Jacobi family.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: a zero real slope would be a zero complex derivative, contradicting the actual complex simplicity theorem. -/
theorem realSlope_ne_zero {a x : ℝ} (ha : -1<a) (hx : normalized (a:ℂ) (x:ℂ)=0) :
    realSlope a x≠0 := by
  intro h
  apply normalized_zero_simple (by simpa using ha) hx
  rw [← realSlope_complex,h,Complex.ofReal_zero]

/-- The actual real Bessel function takes both signs in every neighborhood of each spectral zero.
Use: the intermediate value theorem transfers these genuine simple zeros through Mehler--Heine.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: absence of a negative or positive value in the neighborhood would
make the zero a local minimum or maximum. Fermat's theorem would force
the genuine nonzero slope to vanish in either case. -/
theorem realNormalized_signs {a x ε : ℝ} (ha : -1<a)
    (hx : normalized (a:ℂ) (x:ℂ)=0) (hε : 0<ε) :
    (∃ u∈Set.Ioo (x-ε) (x+ε),realNormalized a u<0) ∧
      (∃ v∈Set.Ioo (x-ε) (x+ε),0<realNormalized a v) := by
  -- This proof needs only the actual derivative, not any proposed order of the zeros.
  have hzero : realNormalized a x=0 := (realNormalized_zero_iff a x).mpr hx
  have hder := realNormalized_hasDerivAt a x
  have hne := realSlope_ne_zero ha hx
  have hN : Set.Ioo (x-ε) (x+ε)∈nhds x := Ioo_mem_nhds (by linarith) (by linarith)
  constructor
  · by_contra hn
    have hmin : IsLocalMin (realNormalized a) x := by
      filter_upwards [hN] with y hy
      rw [hzero]
      exact le_of_not_gt (fun h => hn ⟨y,hy,h⟩)
    exact hne (hmin.hasDerivAt_eq_zero hder)
  · by_contra hn
    have hmax : IsLocalMax (realNormalized a) x := by
      filter_upwards [hN] with y hy
      rw [hzero]
      exact le_of_not_gt (fun h => hn ⟨y,hy,h⟩)
    exact hne (hmax.hasDerivAt_eq_zero hder)

end
end jacobi.Bessel
