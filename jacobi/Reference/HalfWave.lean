import jacobi.Reference.WeightedSpace
import jacobi.Reference.EndpointFrequency

/-!
Article: jacobi, Proposition C.2.
The genuine reference wave is entire with values in the continuous
functions on the physical half interval. We use the already shared
unit-interval subtype and clamp its second half to the midpoint.
Pairing with a function supported on the first half therefore gives
exactly the original integral, while retaining a fixed compact domain.
Use: realizes the source half-interval wave on a fixed compact domain before pairing with zero-extended L2 inputs.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex Filter
open scoped Topology
attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual physical half-interval coordinate, on the shared original compact interval.
Use: realizes the source half-interval wave on a fixed compact domain before pairing with zero-extended L2 inputs.
Article: jacobi, Theorem 2.1.
-/
def halfTime : C(Interval,ℝ) :=
  ⟨fun t => min (t:ℝ) (1/2),continuous_subtype_val.min continuous_const⟩

/-- The compact-domain coordinate always belongs to the genuine physical half interval.
Use: every analytic coefficient and amplitude estimate applies to the actual original wave at this coordinate.
Article: jacobi, Theorem 2.1.
Proof: both entries of the minimum are nonnegative, and the second entry is one half. -/
theorem halfTime_mem (t : Interval) : halfTime t∈Icc (0:ℝ) (1/2) :=
  ⟨le_min t.property.1 (by norm_num),min_le_right _ _⟩

/-- The genuine spatial factor of each original frequency-series term, as a continuous function on the compact physical domain.
Use: its geometric norm bound upgrades actual scalar frequency analyticity to function-space analyticity for arbitrary integral coefficients.
Article: jacobi, Proposition 2.2.
-/
def halfSpatialTerm (a : ℝ) (ha : -1<a) (n : ℕ) : C(Interval,ℂ) where
  toFun t := (weight a (halfTime t):ℂ)*(coordinate (halfTime t):ℂ)^n
  continuous_toFun := by
    have hc : Continuous coordinate := continuous_iff_continuousAt.mpr
      (fun t => (coordinate_hasDerivAt t).continuousAt)
    exact (Complex.continuous_ofReal.comp ((weight_properties ha).1.comp halfTime.continuous)).mul
      ((Complex.continuous_ofReal.comp (hc.comp halfTime.continuous)).pow n)

/-- The actual compact-domain spatial terms have one fixed geometric norm bound.
Use: the proved positive-parameter hypergeometric norm series is a genuine Banach-space normal majorant for the original wave.
Article: jacobi, Proposition C.2.
Proof: the original coordinate has norm at most one half. The genuine
zero-th continuous spatial term bounds its sine-power prefactor at
every point; take the supremum after multiplying by the actual power. -/
theorem halfSpatialTerm_norm (a : ℝ) (ha : -1<a) (n : ℕ) :
    ‖halfSpatialTerm a ha n‖≤‖halfSpatialTerm a ha 0‖*(1/2:ℝ)^n := by
  -- The bound is uniform up to the singular spatial endpoint and includes the original zero-th term.
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hw := (halfSpatialTerm a ha 0).norm_coe_le_norm t
  change ‖(weight a (halfTime t):ℂ)*(coordinate (halfTime t):ℂ)^0‖≤_ at hw
  simp only [pow_zero,mul_one] at hw
  change ‖(weight a (halfTime t):ℂ)*(coordinate (halfTime t):ℂ)^n‖≤_
  rw [norm_mul,norm_pow]
  exact mul_le_mul hw (pow_le_pow_left₀ (norm_nonneg _)
    (coordinate_half_bound (halfTime_mem t)) n) (by positivity) (norm_nonneg _)

/-- On every actual frequency disk the genuine compact-domain wave series has a summable Banach norm majorant.
Use: proves function-space analyticity and permits arbitrary continuous integral functionals, including every source L2 coefficient.
Article: jacobi, Theorem 2.1.
Proof: combine the original frequency coefficient majorant with the
proved geometric spatial norm bound. The positive-parameter community
2F1 norm series at one half is genuinely summable. -/
theorem halfWave_majorant (a : ℝ) (ha : -1<a) (omega : ℂ) :
    ∃ M:ℕ → ℝ,Summable M ∧ ∀ w∈Metric.ball omega 1,∀ n,
      ‖frequencyCoefficient a n w • halfSpatialTerm a ha n‖≤M n := by
  -- The series is the true original reference series in a complete space of continuous functions.
  obtain ⟨D,_,hbound⟩ := frequencyCoefficient_bound a omega
  let U := fun n => ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) ((gamma a:ℂ)+1/2) n*(1/2:ℂ)^n‖
  have hU : Summable U := Hypergeometric.summable_norm (by norm_num)
  refine ⟨fun n => U n*‖halfSpatialTerm a ha 0‖,hU.mul_right _,fun w hw n => ?_⟩
  have hh := mul_le_mul (hbound w hw n) (halfSpatialTerm_norm a ha n)
    (norm_nonneg _) (norm_nonneg _)
  rw [norm_smul]
  apply hh.trans_eq
  dsimp [U]
  rw [norm_mul (ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) ((gamma a:ℂ)+1/2) n),norm_pow]
  norm_num
  ring

/-- The actual original reference frequency series in the space of continuous physical half-interval functions.
Use: its proved genuine entire dependence allows integration against arbitrary zero-extended L2 functions in the GL completeness argument.
Article: jacobi, Proposition C.2.
-/
def halfWave (a : ℝ) (ha : -1<a) (omega : ℂ) : C(Interval,ℂ) :=
  ∑' n,frequencyCoefficient a n omega • halfSpatialTerm a ha n

/-- The genuine compact-domain original reference series is summable in its actual continuous-function norm at every complex frequency.
Use: its evaluations and continuous integral functionals commute with the original convergent sum.
Article: jacobi, Proposition C.2.
Proof: apply the proved compact-frequency summable norm majorant at its own genuine center. -/
theorem halfWave_summable (a : ℝ) (ha : -1<a) (omega : ℂ) :
    Summable (fun n => frequencyCoefficient a n omega • halfSpatialTerm a ha n) := by
  obtain ⟨M,hM,hbound⟩ := halfWave_majorant a ha omega
  exact hM.of_norm_bounded (hbound omega (Metric.mem_ball_self (by norm_num)))

/-- Evaluation of the genuine compact-domain Banach-space series is exactly the original actual reference wave.
Use: the analyticity argument applies to the literal source coefficient integral rather than to a newly specified analytic function.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: genuine summability allows the continuous evaluation functional
to commute with the original sum. The resulting scalar terms are
precisely the original hypergeometric wave expansion, point by point. -/
theorem halfWave_apply (a : ℝ) (ha : -1<a) (omega : ℂ) (t : Interval) :
    halfWave a ha omega t=wave a omega (halfTime t) := by
  -- The actual original coefficients and the actual physical prefactor are retained without approximation.
  have hh := (ContinuousMap.evalCLM ℂ t).map_tsum (halfWave_summable a ha omega)
  change halfWave a ha omega t=∑' n,frequencyCoefficient a n omega*
    ((weight a (halfTime t):ℂ)*(coordinate (halfTime t):ℂ)^n) at hh
  rw [hh,wave,waveCore,ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [frequencyCoefficient]
  ring

/-- The actual reference wave is entire as a function with values in the genuine continuous physical half-interval functions.
Use: arbitrary source L2 coefficient integrals are actual entire functions after applying their continuous integral functional.
Article: jacobi, Theorem 2.1.
Proof: each original scalar coefficient times its genuine continuous
spatial term is entire. The proved true summable Banach norm majorant
is uniform on an actual frequency disk; apply the community complex
normal-series theorem in that same complete function space. -/
theorem halfWave_analytic (a : ℝ) (ha : -1<a) (omega : ℂ) :
    AnalyticAt ℂ (halfWave a ha) omega := by
  obtain ⟨M,hM,hbound⟩ := halfWave_majorant a ha omega
  have hd := Complex.differentiableOn_tsum_of_summable_norm hM
    (F := fun n w => frequencyCoefficient a n w • halfSpatialTerm a ha n)
    (fun n w _ => ((frequencyCoefficient_analytic a n w).smul analyticAt_const).differentiableAt.differentiableWithinAt)
    Metric.isOpen_ball (fun n w hw => hbound w hw n)
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))

end
end jacobi.Reference
