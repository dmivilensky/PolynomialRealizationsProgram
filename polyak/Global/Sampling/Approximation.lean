import polyak.Global.Sampling.PeriodicReduction
import polyak.Global.Sampling.AliasingBound
import Mathlib.Analysis.SpecificLimits.Basic

/-! Uniform Fourier aliasing transfers a positive margin to every
sufficiently large period. There is no upper bound on the periods. -/
noncomputable section
namespace polyak.Global.Sampling
open polyak.General polyak.Levels MeasureTheory Filter
open scoped Topology

theorem eventually_periodic_of_uniform_margin (q:Tuning) (s:ℝ) (f:C(Circle,ℝ))
    (hf:∀x,0≤f x) (μ:Measure Circle) [IsFiniteMeasure μ]
    (hμ:μ=Circle.haar.withDensity (fun x=>ENNReal.ofReal (f x)))
    {δ:ℝ} (hδ:0<δ)
    (hmin:0<∫x,Circle.minimizer (Geometry.shiftedCurve q s) x∂μ)
    (hmargin:∀n:ℤ,n≠0→δ≤∫x,Circle.lag (Geometry.shiftedCurve q s) n x∂μ)
    (hdecay:∃C:ℝ,0≤C ∧ ∀n:ℤ,n≠0→‖fourierCoeff (densityPhase q s f) n‖≤C/(n:ℝ)^2) :
    ∃L0:ℕ,∀L≥L0,PeriodicFP (Geometry.shiftedCurve q s) L := by
  obtain ⟨C,hC,hcoeff⟩:=hdecay
  obtain ⟨K,_hK,herror⟩:=exists_aliasing_error_bound (densityPhase q s f) hC hcoeff
  have ht : Tendsto (fun L:ℕ=>K/(L:ℝ)^2) atTop (𝓝 (0:ℝ)) := by
    have hh := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).pow 2
    have hg:=hh.const_mul K
    simpa only [div_pow,one_pow,←mul_div_assoc,mul_one,zero_pow (by norm_num : 2≠0),mul_zero] using hg
  have hev : ∀ᶠL:ℕ in atTop,0<L ∧ K/(L:ℝ)^2<min (δ/2)
      (∫x,Circle.minimizer (Geometry.shiftedCurve q s) x∂μ) := by
    filter_upwards [eventually_ge_atTop (1:ℕ),ht.eventually
      (eventually_lt_nhds (lt_min (half_pos hδ) hmin))] with L hL hsmall
    exact ⟨by omega,hsmall⟩
  obtain ⟨L0,hL0⟩:=eventually_atTop.mp hev
  refine ⟨L0,fun L hL=>?_⟩
  obtain ⟨hLp,hsmall⟩:=hL0 L hL
  apply periodicFP_of_uniform_aliasing q s f hf hLp μ
    (δ:=δ) (e:=K/(L:ℝ)^2) (by linarith [(lt_min_iff.mp hsmall).1])
    (lt_min_iff.mp hsmall).2 hmargin
  intro n hn
  rw [phaseMoment_sampleMeasure q s f hf hLp,hμ,phaseMoment_density q s f hf]
  exact herror L hLp n hn

end polyak.Global.Sampling
