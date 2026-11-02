import jacobi.Bessel.Real
import jacobi.Bessel.Oscillation
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Article: jacobi, Proposition B.1.
The actual entire Bessel function gives u(x)=x^(alpha+1/2)*F_alpha(x^2).
Both ordinary derivatives and its restoring equation are proved directly.
Source: the classical substitution u=sqrt(x)*J_alpha(x), with the harmless
constant normalization retained from the original entire series.
Use: its restoring equation proves arbitrarily large actual Bessel zeros.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The genuine Liouville-transformed normalized Bessel function on the positive axis.
Use: its restoring equation proves arbitrarily large actual Bessel zeros.
Article: jacobi, Theorem 2.1.
-/
def wave (a x : ℝ) : ℝ := x^(a+1/2)*realNormalized a (x^2)

/-- The explicit ordinary slope of the genuine transformed Bessel wave.
Use: supplies the first derivative in the actual oscillation argument.
Article: jacobi, Theorem 2.1.
-/
def waveSlope (a x : ℝ) : ℝ :=
  (a+1/2)*x^(a-1/2)*realNormalized a (x^2)+2*x^(a+3/2)*realSlope a (x^2)

/-- The explicit ordinary acceleration of the genuine transformed Bessel wave.
Use: verifies the exact restoring equation rather than assuming an ODE solution certificate.
Article: jacobi, Theorem 2.1.
-/
def waveAcceleration (a x : ℝ) : ℝ :=
  (a+1/2)*(a-1/2)*x^(a-3/2)*realNormalized a (x^2)+
  4*(a+1)*x^(a+1/2)*realSlope a (x^2)+4*x^(a+5/2)*realAcceleration a (x^2)

/-- The printed transformed slope is the actual ordinary derivative on the positive axis.
Use: the oscillation comparison applies to the original Bessel function.
Article: jacobi, Theorem 2.1.
Proof: differentiate the positive real power and compose the genuine
spectral derivative with x squared. A real-power shift collects the chain factor x. -/
theorem wave_hasDerivAt (a : ℝ) {x : ℝ} (hx : 0<x) :
    HasDerivAt (wave a) (waveSlope a x) x := by
  -- The positive-axis power is differentiated in its full real exponent range.
  have h := (Real.hasDerivAt_rpow_const (p := a+1/2) (Or.inl hx.ne')).mul
    ((realNormalized_hasDerivAt a (x^2)).comp x ((hasDerivAt_id x).pow 2))
  convert h using 1
  · rfl
  · dsimp only [waveSlope,Function.comp_apply,Pi.pow_apply,id_eq]
    rw [show a+1/2-1=a-1/2 by ring,
      show a+3/2=(a+1/2)+1 by ring,Real.rpow_add_one hx.ne']
    norm_num only [Nat.reduceSub,pow_one,mul_one]
    ring

/-- The printed acceleration is the actual derivative of the transformed slope.
Use: converts the exact normalized Bessel equation into a genuine second-order real wave equation.
Article: jacobi, Theorem 2.1.
Proof: apply the product and chain rules to both slope terms, then
combine the two real-power shifts. The two spectral first-derivative
contributions add to precisely 4*(alpha+1). -/
theorem waveSlope_hasDerivAt (a : ℝ) {x : ℝ} (hx : 0<x) :
    HasDerivAt (waveSlope a) (waveAcceleration a x) x := by
  -- Both differentiated factors are actual derivatives of the same original entire function.
  have hF := (realNormalized_hasDerivAt a (x^2)).comp x ((hasDerivAt_id x).pow 2)
  have hG := (realSlope_hasDerivAt a (x^2)).comp x ((hasDerivAt_id x).pow 2)
  have h1 := ((Real.hasDerivAt_rpow_const (p := a-1/2) (Or.inl hx.ne')).const_mul (a+1/2)).mul hF
  have h2 := ((Real.hasDerivAt_rpow_const (p := a+3/2) (Or.inl hx.ne')).const_mul 2).mul hG
  convert h1.add h2 using 1
  · rfl
  · dsimp only [waveAcceleration]
    rw [show a-1/2-1=a-3/2 by ring,show a+3/2-1=a+1/2 by ring,
      show a+5/2=(a+1/2)+2 by ring,Real.rpow_add hx (a+1/2) 2,Real.rpow_two,
      show a+3/2=(a+1/2)+1 by ring,Real.rpow_add_one hx.ne' (a+1/2),
      show a+1/2=(a-1/2)+1 by ring,Real.rpow_add_one hx.ne' (a-1/2)]
    norm_num only [Nat.reduceSub,pow_one,mul_one,Function.comp_apply,Pi.pow_apply,id_eq,Nat.cast_ofNat]
    ring

/-- The true Bessel wave satisfies its exact Schrödinger equation on the positive axis.
Use: outside a finite radius its restoring coefficient is bounded below by a positive constant.
Article: jacobi, Theorem 2.1.
Proof: real-power shifts put all terms over one positive power of x.
The genuine normalized Bessel differential equation cancels the spectral
derivatives; the remaining inverse-square coefficient is alpha^2-1/4. -/
theorem wave_equation {a : ℝ} (ha : -1<a) {x : ℝ} (hx : 0<x) :
    waveAcceleration a x+(1+(1/4-a^2)/x^2)*wave a x=0 := by
  -- No large-argument asymptotic formula is needed for this exact identity.
  have h := realNormalized_equation ha (x^2)
  unfold waveAcceleration wave
  rw [show a+1/2=(a-3/2)+2 by ring,Real.rpow_add hx (a-3/2) 2,Real.rpow_two,
    show a+5/2=(a-3/2)+4 by ring,Real.rpow_add hx (a-3/2) 4,
    show x^(4:ℝ)=x^4 by exact Real.rpow_natCast x 4]
  have he : (1+(1/4-a^2)/x^2)*(x^(a-3/2)*x^2)=
      x^(a-3/2)*x^2+(1/4-a^2)*x^(a-3/2) := by
    field_simp [hx.ne']
  rw [← mul_assoc (1+(1/4-a^2)/x^2),he]
  linear_combination x^(a-3/2)*x^2*h

/-- A positive-axis transformed zero is exactly a genuine zero of the original entire Bessel function.
Use: turns real wave oscillation into the article's spectral zero set sigma=j^2.
Article: jacobi, Theorem 2.1.
Proof: the positive real-power prefactor never vanishes, and reality of
the original entire function identifies its real and complex zeros. -/
theorem wave_zero_iff (a : ℝ) {x : ℝ} (hx : 0<x) :
    wave a x=0 ↔ normalized (a:ℂ) ((x^2:ℝ):ℂ)=0 := by
  rw [wave,mul_eq_zero,or_iff_right (ne_of_gt (Real.rpow_pos_of_pos hx _)),realNormalized_zero_iff]

end
end jacobi.Bessel
