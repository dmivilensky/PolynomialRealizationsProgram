import polyak.Global.Sampling.AliasingPhase
import polyak.Global.Sampling.AliasingDecay
import polyak.Global.Sampling.PeriodicReduction
import polyak.Global.Circle.SmoothConvolutionRegularity

/-! The actual density times conjugate phase has summable Fourier
coefficients with quadratic decay, including the mirrored analytic junction. -/
noncomputable section
namespace polyak.Global.Sampling
open polyak.General Set MeasureTheory Complex
open scoped ContDiff

def conjugatePhase (q : Tuning) (s x : ℝ) : ℂ := Kernels.cis (-phase q s x)

def conjugatePhaseFirst (q : Tuning) (s x : ℝ) : ℂ :=
  conjugatePhase q s x * ((-phaseDerivative q s x : ℝ) : ℂ) * I

theorem hasDerivAt_conjugatePhase (q : Tuning) (s x : ℝ) :
    HasDerivAt (conjugatePhase q s) (conjugatePhaseFirst q s x) x := by
  have hh := (((hasDerivAt_phase q s x).neg.ofReal_comp).mul_const I).cexp
  convert hh using 1
  · rfl
  · dsimp [conjugatePhase,conjugatePhaseFirst,Kernels.cis]
    ring

@[fun_prop] theorem continuous_conjugatePhase (q : Tuning) (s : ℝ) :
    Continuous (conjugatePhase q s) :=
  Kernels.continuous_cis.comp (continuous_phase q s).neg

@[fun_prop] theorem continuous_conjugatePhaseFirst (q : Tuning) (s : ℝ) :
    Continuous (conjugatePhaseFirst q s) := by
  unfold conjugatePhaseFirst
  fun_prop

theorem conjugatePhase_periodic (q : Tuning) (s : ℝ) :
    Function.Periodic (conjugatePhase q s) (2*Real.pi) := by
  intro x
  simp only [conjugatePhase,phase_periodic q s x]

theorem conjugatePhaseFirst_periodic (q : Tuning) (s : ℝ) :
    Function.Periodic (conjugatePhaseFirst q s) (2*Real.pi) := by
  intro x
  simp only [conjugatePhaseFirst,conjugatePhase_periodic q s x,phaseDerivative_periodic q s x]

theorem hasDerivWithinAt_conjugatePhaseFirst_right (q : Tuning) (s : ℝ)
    {x : ℝ} (hx : x∈Ioo 0 (2*Real.pi)) :
    HasDerivWithinAt (conjugatePhaseFirst q s)
      (conjugatePhaseFirst q s x * ((-phaseDerivative q s x : ℝ) : ℂ) * I -
        (phaseSecond q s x : ℂ)*conjugatePhase q s x*I) (Ioi x) x := by
  have hh := (((hasDerivAt_conjugatePhase q s x).hasDerivWithinAt.mul
    ((hasDerivWithinAt_phaseDerivative_right q s hx).neg.ofReal_comp)).mul_const I)
  convert hh using 1
  · rfl
  · simp only [Pi.neg_apply,Complex.ofReal_neg]
    ring

def densityPhaseFirst (q : Tuning) (s : ℝ) (F : ℝ→ℝ) (x : ℝ) : ℂ :=
  ((deriv F x : ℝ) : ℂ)*conjugatePhase q s x + (F x : ℂ)*conjugatePhaseFirst q s x

def densityPhaseSecond (q : Tuning) (s : ℝ) (F : ℝ→ℝ) (x : ℝ) : ℂ :=
  ((deriv (deriv F) x : ℝ) : ℂ)*conjugatePhase q s x +
    (2:ℂ)*((deriv F x : ℝ) : ℂ)*conjugatePhaseFirst q s x +
    (F x : ℂ)*conjugatePhaseFirst q s x*((-phaseDerivative q s x : ℝ) : ℂ)*I -
    (phaseSecond q s x : ℂ)*((F x : ℂ)*conjugatePhase q s x*I)

theorem densityPhase_fourier_decay (q : Tuning) (s : ℝ) (f : C(Circle,ℝ))
    (hSmooth : ContDiff ℝ ∞ (fun x => f (Circle.ofReal x))) :
    ∃C : ℝ,0≤C ∧ ∀n : ℤ,n≠0→‖fourierCoeff (densityPhase q s f) n‖≤C/(n:ℝ)^2 := by
  let F : ℝ→ℝ := fun x=>f (Circle.ofReal x)
  have hF : ContDiff ℝ ∞ F := hSmooth
  have hFd : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  have hFdd : ContDiff ℝ ∞ (deriv (deriv F)) := (contDiff_infty_iff_deriv.mp hFd).2
  have hdf (x : ℝ) : HasDerivAt F (deriv F x) x :=
    (hF.differentiable (by simp) x).hasDerivAt
  have hddf (x : ℝ) : HasDerivAt (deriv F) (deriv (deriv F) x) x :=
    (hFd.differentiable (by simp) x).hasDerivAt
  have hfirst : Continuous (densityPhaseFirst q s F) := by
    unfold densityPhaseFirst
    exact ((Complex.continuous_ofReal.comp hFd.continuous).mul
      (continuous_conjugatePhase q s)).add
      ((Complex.continuous_ofReal.comp hF.continuous).mul (continuous_conjugatePhaseFirst q s))
  have hper : Function.Periodic F (2*Real.pi) := Circle.realPullback_periodic f
  have hperd : Function.Periodic (deriv F) (2*Real.pi) := Circle.periodic_derivative hper
  have hend : densityPhaseFirst q s F (2*Real.pi)=densityPhaseFirst q s F 0 := by
    have h1 := hperd 0
    have h2 := hper 0
    have h3 := conjugatePhase_periodic q s 0
    have h4 := conjugatePhaseFirst_periodic q s 0
    simp only [zero_add] at h1 h2 h3 h4
    simp only [densityPhaseFirst,h1,h2,h3,h4]
  have heq (x : ℝ) : densityPhase q s f (Circle.ofReal x)=(F x:ℂ)*conjugatePhase q s x := by
    simp only [densityPhase,ContinuousMap.coe_mk,Circle.phaseLift_ofReal,conjugatePhase,F]
  have hfirstderiv (x : ℝ) :
      HasDerivAt (fun x=>densityPhase q s f (Circle.ofReal x)) (densityPhaseFirst q s F x) x := by
    simp_rw [heq]
    exact (hdf x).ofReal_comp.mul (hasDerivAt_conjugatePhase q s x)
  have hsecondderiv (x : ℝ) (hx : x∈Ioo 0 (2*Real.pi)) :
      HasDerivWithinAt (densityPhaseFirst q s F) (densityPhaseSecond q s F x) (Ioi x) x := by
    have hh := (((hddf x).ofReal_comp.hasDerivWithinAt.mul
      (hasDerivAt_conjugatePhase q s x).hasDerivWithinAt).add
      ((hdf x).ofReal_comp.hasDerivWithinAt.mul
        (hasDerivWithinAt_conjugatePhaseFirst_right q s hx)))
    convert hh using 1
    · rfl
    · dsimp [densityPhaseSecond]
      ring
  have hcont : Continuous (fun x=>
      ((deriv (deriv F) x : ℝ) : ℂ)*conjugatePhase q s x +
      (2:ℂ)*((deriv F x : ℝ) : ℂ)*conjugatePhaseFirst q s x +
      (F x : ℂ)*conjugatePhaseFirst q s x*((-phaseDerivative q s x : ℝ) : ℂ)*I) := by
    have : Continuous F := hF.continuous
    have : Continuous (deriv F) := hFd.continuous
    have : Continuous (deriv (deriv F)) := hFdd.continuous
    fun_prop
  have hsecond : IntervalIntegrable (densityPhaseSecond q s F) volume 0 (2*Real.pi) := by
    have hi := phaseSecond_intervalIntegrable q s
    have hc : IntervalIntegrable (fun x=>(phaseSecond q s x:ℂ)) volume 0 (2*Real.pi) :=
      ⟨hi.1.ofReal,hi.2.ofReal⟩
    have hm := hc.mul_continuousOn (g:=fun x=>(F x:ℂ)*conjugatePhase q s x*I)
      (((Complex.continuous_ofReal.comp hF.continuous).mul (continuous_conjugatePhase q s)).mul
        continuous_const).continuousOn
    exact (hcont.intervalIntegrable 0 (2*Real.pi)).sub hm
  exact fourierCoeff_decay_of_piecewise_C2 _ hfirst.continuousOn hend
    (fun x _ => (hfirstderiv x).hasDerivWithinAt) hsecondderiv hsecond

end polyak.Global.Sampling
