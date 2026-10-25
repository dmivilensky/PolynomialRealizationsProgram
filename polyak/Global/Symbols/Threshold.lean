import polyak.Global.Symbols.Limits
import polyak.Levels.Threshold.ShiftThreshold
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! The actual attained shift threshold has a limit symbol describing
all its finite-measure extremals simultaneously. -/
noncomputable section
namespace polyak.Global.Symbols
open Levels MeasureTheory Filter Set Topology

 theorem shifted_curves_tendstoUniformly (q : General.Tuning) {s : ℕ→ℝ} {t : ℝ}
    (hs : Tendsto s atTop (𝓝 t)) :
    TendstoUniformly (fun j ω=>Geometry.shiftedCurve q (s j) ω)
      (fun ω=>Geometry.shiftedCurve q t ω) atTop := by
  have hmap : Continuous (fun p : ℝ×Frequency=>(q,p)) := continuous_const.prodMk continuous_id
  have hc := Geometry.shiftedAngle_jointContinuous.comp hmap
  have hu : TendstoUniformly (fun r ω=>Geometry.shiftedCurve q r ω)
      (fun ω=>Geometry.shiftedCurve q t ω) (𝓝 t) :=
    ContinuousOn.tendstoUniformly (f:=fun r (ω : Frequency)=>Geometry.shiftedAngle q r ω)
      (U:=univ) Filter.univ_mem hc.continuousOn
  intro U hU
  exact hs.eventually (hu U hU)

def thresholdApproach (t : ℝ) (j : ℕ) : ℝ := t-1/((j:ℝ)+1)

theorem thresholdApproach_lt (t : ℝ) (j : ℕ) : thresholdApproach t j<t := by
  unfold thresholdApproach
  have hp : 0<1/((j:ℝ)+1) := one_div_pos.mpr (by positivity)
  linarith

theorem thresholdApproach_tendsto (t : ℝ) :
    Tendsto (thresholdApproach t) atTop (𝓝 t) := by
  have hi : Tendsto (fun j : ℕ=>1/((j:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  change Tendsto (fun j : ℕ=>t-1/((j:ℝ)+1)) atTop (𝓝 t)
  simpa only [sub_zero] using (tendsto_const_nhds (x:=t)).sub hi

theorem thresholdApproach_strictMono (t : ℝ) : StrictMono (thresholdApproach t) := by
  intro i j hij
  have hp : (0:ℝ)<(i:ℝ)+1 := by positivity
  have hlt : (i:ℝ)+1<(j:ℝ)+1 := by exact_mod_cast (Nat.add_lt_add_right hij 1)
  have hh := one_div_lt_one_div_of_lt hp hlt
  unfold thresholdApproach
  linarith

/-- Theorem limitsymbol, in fact for every allowed subset of signed lags. -/
theorem limit_symbol_at_sigmaOn (q : General.Tuning) (𝒩 : Set ℤ) (hN : 𝒩⊆nonzeroLags) :
    Nonempty (LimitSymbol (Geometry.shiftedCurve q (Threshold.sigmaOn q 𝒩)) 𝒩) := by
  let Θ : ℕ→Curve := fun j=>Geometry.shiftedCurve q (thresholdApproach (Threshold.sigmaOn q 𝒩) j)
  apply limit_symbol_of_infeasible_approximation Θ
    (Geometry.shiftedCurve q (Threshold.sigmaOn q 𝒩))
  · exact shifted_curves_tendstoUniformly q (thresholdApproach_tendsto _)
  · intro j hj
    have hh := (Threshold.shifted_feasible_iff q 𝒩 hN _).mp hj
    have hn := thresholdApproach_lt (Threshold.sigmaOn q 𝒩) j
    linarith
  · exact Threshold.sigmaOn_feasible q 𝒩 hN

/-- One common symbol controls every genuine threshold extremal of q. -/
theorem limit_symbol (q : General.Tuning) :
    Nonempty (LimitSymbol (Geometry.shiftedCurve q (Threshold.sigma q)) nonzeroLags) :=
  limit_symbol_at_sigmaOn q nonzeroLags (fun _ h=>h)

theorem LimitSymbol.continuous {Θ : Curve} {𝒩 : Set ℤ} (S : LimitSymbol Θ 𝒩) :
    Continuous (S.weights.eval Θ) := S.weights.continuous_eval Θ

theorem LimitSymbol.normalized {Θ : Curve} {𝒩 : Set ℤ} (S : LimitSymbol Θ 𝒩) :
    (∑'n,S.weights.weight n)+S.weights.gamma=1 := S.weights.normalized

end polyak.Global.Symbols
