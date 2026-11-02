import jacobi.Analytic.HypergeometricParameters
import jacobi.Reference.JointContinuity
import jacobi.Hankel.SquaredExpansion
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
Article: jacobi, Lemma C.1.
The original sine-power Gauss solution is extended in its actual order,
as well as its frequency. It is jointly continuous through the singular
physical endpoint and analytic along genuine analytic parameter curves.
Its real-order restriction is the previously constructed reference wave.
Use: fixes the same endpoint normalization in complex and real GL.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original affine reference exponent continued in the complex order.
Use: fixes the same endpoint normalization in complex and real GL.
Article: jacobi, Lemma C.1.
-/
def gamma (a : ℂ) : ℂ := a/2+3/4

/-- The original sine-power prefactor, with its complex exponent and actual positive physical base.
Use: restores the normalized endpoint power after the Gauss core is continued.
Article: jacobi, Lemma C.1.
-/
def weight (a : ℂ) (t : ℝ) : ℂ := ((Real.sin (Real.pi*t)/Real.pi:ℝ):ℂ)^gamma a

/-- The original reference Gauss core with both order and frequency complex.
Use: supplies the actual holomorphic reference functions in the analytic GL summands.
Article: jacobi, Lemma C.1.
-/
def waveCore (a omega x : ℂ) : ℂ :=
  ordinaryHypergeometric (gamma a-omega/(Real.pi:ℂ))
    (gamma a+omega/(Real.pi:ℂ)) (gamma a+1/2) x

/-- The continued original reference solution at complex order and frequency.
Use: the analytic GL construction evaluates this same solution at target and reference frequencies.
Article: jacobi, Lemma C.1.
-/
def wave (a omega : ℂ) (t : ℝ) : ℂ := weight a t*waveCore a omega (jacobi.Reference.coordinate t:ℂ)

/-- The continued affine exponent agrees exactly with the original real reference exponent.
Use: identifies every real restriction of the continued prefactor and Gauss solution.
Article: jacobi, Lemma C.1.
Proof: real inclusion preserves the displayed affine formula. -/
theorem gamma_real (a : ℝ) : gamma (a:ℂ)=(jacobi.Reference.gamma a:ℂ) := by
  unfold gamma jacobi.Reference.gamma
  push_cast
  ring

/-- The genuine physical sine base is nonnegative throughout the original reference half-open interval.
Use: complex powers have the original real branch and remain jointly continuous at the left endpoint.
Article: jacobi, Lemma C.1.
Proof: at zero the base is zero; in the interior its sine and the denominator pi are positive. -/
theorem sineBase_nonneg {t : ℝ} (ht : t∈Ico 0 1) : 0≤Real.sin (Real.pi*t)/Real.pi := by
  rcases eq_or_lt_of_le ht.1 with he | he
  · rw [← he]
    simp
  · exact (div_pos (jacobi.Reference.sine_pos ⟨he,ht.2⟩) Real.pi_pos).le

/-- The actual complex sine prefactor has exactly the real-exponent norm given by the real part of its order.
Use: all later complex-order endpoint bounds retain the actual source scale t^(Re gamma).
Article: jacobi, Lemma C.1.
Proof: the physical base is nonnegative and the exponent has positive real part; apply the community complex-power norm identity. -/
theorem weight_norm {a : ℂ} (ha : 0<(gamma a).re) {t : ℝ} (ht : t∈Ico 0 1) :
    ‖weight a t‖=(Real.sin (Real.pi*t)/Real.pi)^(gamma a).re :=
  Complex.norm_cpow_eq_rpow_re_of_nonneg (sineBase_nonneg ht) ha.ne'

/-- Analytic changes of the original complex order and frequency give an analytic actual Gauss core at every spatial argument in its convergence disk.
Use: the continued GL summands have genuinely holomorphic reference factors.
Article: jacobi, Lemma C.1.
Proof: the affine numerator and denominator parameters are analytic, the
denominator has positive real part, and the actual spatial argument is
inside the unit disk. Apply the proved simultaneous-parameter Gauss theorem. -/
theorem waveCore_comp_analytic {A W X : ℂ → ℂ} {p : ℂ}
    (hA : AnalyticAt ℂ A p) (hW : AnalyticAt ℂ W p) (hX : AnalyticAt ℂ X p)
    (ha : 0<(gamma (A p)).re) (hx : ‖X p‖<1) :
    AnalyticAt ℂ (fun u => waveCore (A u) (W u) (X u)) p := by
  have hg : AnalyticAt ℂ (fun u => gamma (A u)) p := by unfold gamma; fun_prop
  exact jacobi.Reference.Hypergeometric.parameters_comp_analytic
    (hg.sub hW.div_const) (hg.add hW.div_const) (hg.add analyticAt_const) hX
    (by norm_num; linarith) hx

/-- The actual normalized sine prefactor is analytic along analytic order curves, including its identically zero left-endpoint value.
Use: multiplication by the original endpoint normalization preserves holomorphy of the GL reference factors.
Article: jacobi, Lemma C.1.
Proof: for a nonzero fixed physical base the power is an exponential of
the analytic exponent times a constant logarithm. At a zero base, the
positive-real-part exponent stays nonzero on a neighborhood, so the
actual prefactor is identically zero there. -/
theorem weight_comp_analytic {A : ℂ → ℂ} {p : ℂ} (hA : AnalyticAt ℂ A p)
    (ha : 0<(gamma (A p)).re) (t : ℝ) : AnalyticAt ℂ (fun u => weight (A u) t) p := by
  -- The endpoint value is proved for the actual complex power, not supplied by a replacement convention.
  have hg : AnalyticAt ℂ (fun u => gamma (A u)) p := by unfold gamma; fun_prop
  by_cases hb : ((Real.sin (Real.pi*t)/Real.pi:ℝ):ℂ)=0
  · have hne : gamma (A p)≠0 := ne_of_apply_ne Complex.re ha.ne'
    apply (analyticAt_const (v := (0:ℂ))).congr
    filter_upwards [hg.continuousAt.eventually_ne hne] with u hu
    simp only [weight,hb,Complex.zero_cpow hu]
  · have he : (fun u => weight (A u) t)=
        (fun u => Complex.exp (Complex.log ((Real.sin (Real.pi*t)/Real.pi:ℝ):ℂ)*gamma (A u))) := by
      funext u
      exact Complex.cpow_def_of_ne_zero hb _
    rw [he]
    exact (analyticAt_const.mul hg).cexp

/-- The original complex-order reference wave is analytic along analytic order and frequency curves at every physical point, including zero.
Use: proves the pointwise holomorphic reference factors required in Appendix E.1 and (d).
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual physical coordinate is inside the genuine Gauss
convergence disk, including at zero. Multiply the proved holomorphic
Gauss core by the proved holomorphic original sine prefactor. -/
theorem wave_comp_analytic {A W : ℂ → ℂ} {p : ℂ}
    (hA : AnalyticAt ℂ A p) (hW : AnalyticAt ℂ W p)
    (ha : 0<(gamma (A p)).re) {t : ℝ} (ht : t∈Ico 0 1) :
    AnalyticAt ℂ (fun u => wave (A u) (W u) t) p :=
  (weight_comp_analytic hA ha t).mul (waveCore_comp_analytic hA hW analyticAt_const ha
    (jacobi.Reference.coordinate_norm_lt_one_of_nonneg ht))

/-- The actual complex-order reference wave is jointly continuous in order, frequency and physical position, including its singular left endpoint.
Use: each analytic GL kernel summand retains joint parameter and spatial continuity.
Article: jacobi, Lemma C.1.
Proof: the original sine base is nonnegative, and its complex power is
jointly continuous at every positive-real-part exponent, even when the
base is zero. The proved normal Gauss series is jointly continuous in
all its parameters and its true physical coordinate; multiply these actual factors. -/
theorem wave_joint_continuous {a omega : ℂ} {t : ℝ}
    (ha : 0<(gamma a).re) (ht : t∈Ico 0 1) :
    ContinuousAt (fun p : ℂ × ℂ × ℝ => wave p.1 p.2.1 p.2.2) (a,omega,t) := by
  -- The common coefficient majorant allows every parameter and the endpoint to move simultaneously.
  have hg : Continuous gamma := by unfold gamma; fun_prop
  have hx : Continuous (fun t : ℝ => (jacobi.Reference.coordinate t:ℂ)) := by
    apply Complex.continuous_ofReal.comp
    exact continuous_iff_continuousAt.mpr (fun s => (jacobi.Reference.coordinate_hasDerivAt s).continuousAt)
  have hc := jacobi.Reference.Hypergeometric.parameters_comp_continuousAt
    (A := fun p : ℂ × ℂ × ℝ => gamma p.1-p.2.1/(Real.pi:ℂ))
    (B := fun p => gamma p.1+p.2.1/(Real.pi:ℂ))
    (C := fun p => gamma p.1+1/2) (X := fun p => (jacobi.Reference.coordinate p.2.2:ℂ))
    (p := (a,omega,t)) (by fun_prop) (by fun_prop) (by fun_prop)
    (hx.comp (continuous_snd.comp continuous_snd)) (by norm_num; linarith)
    (jacobi.Reference.coordinate_norm_lt_one_of_nonneg ht)
  have hw := (Complex.continuousAt_cpow_of_re_pos
    (p := (((Real.sin (Real.pi*t)/Real.pi:ℝ):ℂ),gamma a))
    (Or.inl (by simpa only [Complex.ofReal_re] using sineBase_nonneg ht)) ha).comp_of_eq
    (show ContinuousAt (fun p : ℂ × ℂ × ℝ =>
      (((Real.sin (Real.pi*p.2.2)/Real.pi:ℝ):ℂ),gamma p.1)) (a,omega,t) by fun_prop) rfl
  exact hw.mul hc

/-- At real orders the actual continued reference wave is exactly the original source wave at every physical point.
Use: the analytic GL construction preserves all earlier real reference functions and normalizations.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the continued exponent restricts to the original real exponent;
on the nonnegative physical base the complex power equals inclusion
of the actual real power. The remaining Gauss parameters agree literally. -/
theorem wave_real (a : ℝ) (omega : ℂ) {t : ℝ} (ht : t∈Ico 0 1) :
    wave (a:ℂ) omega t= jacobi.Reference.wave a omega t := by
  simp only [wave,weight,waveCore,gamma_real,jacobi.Reference.wave,jacobi.Reference.waveCore]
  rw [← Complex.ofReal_cpow (sineBase_nonneg ht)]
  rfl

end
end jacobi.ComplexReference
