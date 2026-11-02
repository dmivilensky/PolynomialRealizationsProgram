import jacobi.Analytic.ReferenceWave
import jacobi.Reference.WaveEquation

/-!
Article: jacobi, Lemma C.1.
The genuine complex-order reference wave has two actual spatial
derivatives. Their explicit Gauss formulas give the same singular
Schrodinger equation used for uniform high-frequency propagation.
Use: fixes the initial derivative coordinate and the actual reference equation.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The original sine prefactor's logarithmic slope at complex order.
Use: fixes the initial derivative coordinate and the actual reference equation.
Article: jacobi, Lemma C.1.
-/
def weightLogSlope (a : ℂ) (t : ℝ) : ℂ := gamma a*Real.pi*Real.cos (Real.pi*t)/Real.sin (Real.pi*t)

/-- The actual logarithmic slope derivative at complex order.
Use: computes the second spatial derivative of the reference wave.
Article: jacobi, Lemma C.1.
-/
def weightLogAcceleration (a : ℂ) (t : ℝ) : ℂ := -gamma a*Real.pi^2/Real.sin (Real.pi*t)^2

/-- The singular reference potential before adding the fixed energy shift.
Use: its uniform inverse-square bound propagates the genuine initial state.
Article: jacobi, Lemma C.1.
-/
def singularPotential (a : ℂ) (t : ℝ) : ℂ :=
  gamma a*(gamma a-1)*Real.pi^2/Real.sin (Real.pi*t)^2

/-- The complex sine prefactor has the stated genuine first spatial derivative.
Use: proves that the reference energy is built from actual solution derivatives.
Article: jacobi, Lemma C.1.
Proof: locally the physical sine base is positive. Differentiate its
complex logarithm and exponential representation, then simplify using
the actual nonzero physical sine and pi. -/
theorem weight_hasDerivAt (a : ℂ) {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (weight a) (weightLogSlope a t*weight a t) t := by
  -- Positivity selects the original power branch on an actual physical neighborhood.
  have hs := jacobi.Reference.sine_pos ht
  have hb : 0<Real.sin (Real.pi*t)/Real.pi := div_pos hs Real.pi_pos
  have hbase : HasDerivAt (fun s : ℝ => ((Real.sin (Real.pi*s)/Real.pi:ℝ):ℂ))
      (Real.cos (Real.pi*t):ℂ) t := by
    have hr : HasDerivAt (fun s : ℝ => Real.sin (Real.pi*s)/Real.pi) (Real.cos (Real.pi*t)) t := by
      convert (((Real.hasDerivAt_sin (Real.pi*t)).comp t
        ((hasDerivAt_id t).const_mul Real.pi)).div_const Real.pi) using 1 <;>
        simp only [Function.comp_def,mul_one,mul_div_cancel_right₀ _ Real.pi_ne_zero]
    exact hr.ofReal_comp
  have hslit : ((Real.sin (Real.pi*t)/Real.pi:ℝ):ℂ)∈Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hb)
  have hlog := (Complex.hasDerivAt_log hslit).comp t hbase
  have he := (hlog.mul_const (gamma a)).cexp
  have hne : ∀ᶠ s : ℝ in 𝓝 t,((Real.sin (Real.pi*s)/Real.pi:ℝ):ℂ)≠0 :=
    hbase.continuousAt.eventually_ne (Complex.ofReal_ne_zero.mpr hb.ne')
  have hEq : weight a=ᶠ[𝓝 t] fun s => Complex.exp
      (Complex.log ((Real.sin (Real.pi*s)/Real.pi:ℝ):ℂ)*gamma a) := by
    filter_upwards [hne] with s hsn
    exact Complex.cpow_def_of_ne_zero hsn _
  convert! he.congr_of_eventuallyEq hEq using 1
  rw [weight,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne')]
  dsimp [weightLogSlope]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hs.ne',Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- The original complex logarithmic slope has its actual inverse-sine-square derivative.
Use: the true second reference derivative retains the exact complex singular potential.
Article: jacobi, Lemma C.1.
Proof: multiply the already proved derivative of pi*cot(pi*t), obtained
from the real reference slope at exponent one, by the constant complex exponent. -/
theorem weightLogSlope_hasDerivAt (a : ℂ) {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (weightLogSlope a) (weightLogAcceleration a t) t := by
  -- The old order alpha=1/2 has exponent one, so its real cotangent derivative supplies the common spatial factor.
  have hh := ((jacobi.Reference.weightLogSlope_hasDerivAt (1/2) ht).ofReal_comp).const_mul (gamma a)
  convert! hh using 1
  · funext s
    simp only [weightLogSlope,jacobi.Reference.weightLogSlope,jacobi.Reference.gamma]
    norm_num
    ring
  · simp only [weightLogAcceleration,jacobi.Reference.weightLogAcceleration,jacobi.Reference.gamma]
    norm_num
    ring

/-- The original complex-order wave's explicit first spatial derivative.
Use: supplies the actual second component of the high-frequency initial state.
Article: jacobi, Lemma C.1.
-/
def waveSlope (a omega : ℂ) (t : ℝ) : ℂ :=
  weight a t*(weightLogSlope a t*waveCore a omega (coordinate t:ℂ)+
    (coordinateSlope t:ℂ)*deriv (waveCore a omega) (coordinate t:ℂ))

/-- The original complex-order wave's explicit second spatial derivative.
Use: identifies the actual singular reference equation before energy propagation.
Article: jacobi, Lemma C.1.
-/
def waveAcceleration (a omega : ℂ) (t : ℝ) : ℂ :=
  weight a t*((weightLogAcceleration a t+weightLogSlope a t^2)*waveCore a omega (coordinate t:ℂ)+
    (2*weightLogSlope a t*(coordinateSlope t:ℂ)+(coordinateAcceleration t:ℂ))*deriv (waveCore a omega) (coordinate t:ℂ)+
    (coordinateSlope t:ℂ)^2*deriv (deriv (waveCore a omega)) (coordinate t:ℂ))

/-- The actual Gauss core is analytic in its spatial argument at every physical interior point.
Use: both explicit reference derivatives are genuine ordinary spatial derivatives.
Article: jacobi, Lemma C.1.
Proof: the original coordinate lies inside the proved unit Gauss convergence disk. -/
theorem waveCore_analytic (a omega : ℂ) {t : ℝ} (ht : t∈Ioo 0 1) :
    AnalyticAt ℂ (waveCore a omega) (coordinate t:ℂ) :=
  jacobi.Reference.Hypergeometric.analytic (coordinate_norm_lt_one ht)

/-- The displayed complex-order reference slope is the actual spatial derivative.
Use: high-frequency energy estimates apply to the original reference solution.
Article: jacobi, Lemma C.1.
Proof: differentiate the genuine sine prefactor and Gauss core, composing
the latter with the original real-to-complex coordinate derivative. -/
theorem wave_hasDerivAt (a omega : ℂ) {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (wave a omega) (waveSlope a omega t) t := by
  have hh := (waveCore_analytic a omega ht).differentiableAt.hasDerivAt.comp t (coordinate_hasDerivAt t).ofReal_comp
  convert! (weight_hasDerivAt a ht).mul hh using 1
  dsimp [waveSlope]
  ring

/-- The displayed complex-order reference acceleration is the actual slope derivative.
Use: the true complex-order wave energy has the differential equation used in its propagation bound.
Article: jacobi, Lemma C.1.
Proof: differentiate the exact first-derivative formula, using the
actual prefactor, logarithmic slope, coordinate and analytic Gauss derivatives. -/
theorem waveSlope_hasDerivAt (a omega : ℂ) {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (waveSlope a omega) (waveAcceleration a omega t) t := by
  -- Both derivatives of the actual Gauss function are evaluated inside its original disk.
  have hx := (coordinate_hasDerivAt t).ofReal_comp
  have hx' := (coordinateSlope_hasDerivAt t).ofReal_comp
  have hh := (waveCore_analytic a omega ht).differentiableAt.hasDerivAt.comp t hx
  have hh' := (waveCore_analytic a omega ht).deriv.differentiableAt.hasDerivAt.comp t hx
  convert! (weight_hasDerivAt a ht).mul
    (((weightLogSlope_hasDerivAt a ht).mul hh).add (hx'.mul hh')) using 1
  dsimp [waveAcceleration]
  ring

end
end jacobi.ComplexReference
