import polyak.Asymptotics.SmallQ
import polyak.Boundary.P1.PhysicalContinuation
import polyak.Regularity.Critical

/-!
Article: Appendix C, the actual small-q rate and its strict spiral excess.
Use: the globally checked P₁ source is identified with its analytic endpoint;
local implicit uniqueness then identifies the actual heavy-ball rate, while the
spiral is identified by its unique positive polynomial root.
-/
namespace polyak.Asymptotics.SmallQ
noncomputable section
open Filter Set Spectral
open scoped Topology

/-- The actual exact rate as a function of the Polyak parameter. -/
def actualFactor (q : ℝ) : ℝ := Real.exp (T q)

def actualParameter (q : ℝ) : ℝ := 2*actualFactor q/(1+(actualFactor q)^2)

/-- The local P₁ reserve is obtained from the actual source implicit equations. -/
def sourceA (z : ℝ) : ℝ := Boundary.P1.localBranch z 0

theorem sourceA_analytic : AnalyticAt ℝ sourceA 0 :=
  Boundary.P1.localBranch_coordinate_analyticAt 0

theorem sourceA_zero : sourceA 0=1/8 := Boundary.P1.localBranch_initial.1

def optimalBranch : RescaledBranch sourceA := rescaledBranch sourceA sourceA_analytic

def spiralBranch : RescaledBranch (fun _ => 0) := rescaledBranch (fun _ => 0) analyticAt_const

/-- The actual a priori bound forces the factor to zero as q↓0. -/
theorem actualFactor_tendsto_zero :
    Tendsto actualFactor (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hu : ∀ᶠ q in 𝓝[>] (0 : ℝ),actualFactor q≤q*Real.exp (Real.arsinh 1) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hh:=(abs_le.mp (abs_T_sub_log_le hq)).2
    calc
      _ ≤ Real.exp (Real.log q+Real.arsinh 1) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_add,Real.exp_log hq]
  have ht : Tendsto (fun q : ℝ => q*Real.exp (Real.arsinh 1)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [id_eq,zero_mul] using
      ((tendsto_id : Tendsto (fun q : ℝ => q) (𝓝 0) (𝓝 0)).mono_left
        nhdsWithin_le_nhds).mul_const (Real.exp (Real.arsinh 1))
  exact squeeze_zero' (Eventually.of_forall (fun q => (Real.exp_pos (T q)).le)) hu ht

theorem actualParameter_tendsto_zero :
    Tendsto actualParameter (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
  have hh:=(actualFactor_tendsto_zero.const_mul (2 : ℝ)).div
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1)).add
      (actualFactor_tendsto_zero.pow 2)) (by norm_num : (1+(0 : ℝ)^2)≠0)
  have ht : Tendsto actualParameter (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert hh using 1
    · funext q
      rfl
    · norm_num
  refine tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall (fun q => ?_)⟩
  change 0<2*Real.exp (T q)/(1+(Real.exp (T q))^2)
  exact div_pos (by positivity) (by positivity)

/-- The physical reciprocal-cosh identity uses the actual maximal exponent. -/
theorem cosh_actualParameter (q : ℝ) : Real.cosh (T q)=1/actualParameter q := by
  unfold actualParameter actualFactor
  rw [Real.cosh_eq,Real.exp_neg]
  field_simp
  ring

/-- The actual rate ratio is the source's positive hyperbolic root. -/
theorem actual_ratio_eventually : ∀ᶠ q in 𝓝[>] (0 : ℝ),
    actualFactor q/q=Real.exp (Real.arsinh (Boundary.P1.localU (actualParameter q))) := by
  filter_upwards [actualParameter_tendsto_zero.eventually Boundary.P1.V_eq_localU_eventually,
    self_mem_nhdsWithin,(gt_mem_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds]
    with q hf hq hq1
  have he : Real.exp (T q-Real.log q)=actualFactor q/q := by
    rw [Real.exp_sub,Real.exp_log hq]
    rfl
  rw [←he,Regularity.T_sub_log_eq_V hq hq1,hf (T q) (cosh_actualParameter q)]

/-- The compactified actual ratio converges to the nonsingular positive source root. -/
theorem actual_ratio_tendsto :
    Tendsto (fun q => actualFactor q/q) (𝓝[>] (0 : ℝ)) (𝓝 leading) := by
  have hu:=Boundary.P1.localU_tendsto.comp
    (actualParameter_tendsto_zero.mono_right nhdsWithin_le_nhds)
  have hh:=(Real.continuous_exp.continuousAt.tendsto).comp
    (Real.continuous_arsinh.continuousAt.tendsto.comp hu)
  have hlim : Real.exp (Real.arsinh (1 : ℝ))=leading := by
    rw [Real.exp_arsinh]
    norm_num [leading]
  rw [hlim] at hh
  exact (tendsto_congr' actual_ratio_eventually).mpr hh

theorem compactParameter_ratio {q ρ : ℝ} (hq : q≠0) :
    compactParameter q (ρ/q)=2*ρ/(1+ρ^2) := by
  unfold compactParameter
  field_simp

/-- Local implicit uniqueness identifies the actual optimal rate with the constructed branch. -/
theorem actualFactor_eq_branch : ∀ᶠ q in 𝓝[>] (0 : ℝ),actualFactor q=q*optimalBranch.r q := by
  have hg : Tendsto (fun q => (q,actualFactor q/q)) (𝓝[>] (0 : ℝ)) (𝓝 (0,leading)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds actual_ratio_tendsto
  filter_upwards [hg.eventually optimalBranch.unique,actual_ratio_eventually,
    self_mem_nhdsWithin] with q hu heq hq
  have hpoly : (actualFactor q/q)^2-
      2*Boundary.P1.localU (actualParameter q)*(actualFactor q/q)-1=0 := by
    rw [heq,Real.exp_arsinh]
    have hh:=Real.sq_sqrt (by positivity : 0≤1+(Boundary.P1.localU (actualParameter q))^2)
    nlinarith
  have hz : sourceEquation sourceA (q,actualFactor q/q)=0 := by
    rw [sourceEquation_physical,compactParameter_ratio hq.ne']
    change (1+(q*(actualFactor q/q))^2)^2*
      ((actualFactor q/q)^2-2*Boundary.P1.localU (actualParameter q)*(actualFactor q/q)-1)=0
    rw [hpoly,mul_zero]
  have hr:=hu.mp hz
  rw [hr]
  exact (mul_div_cancel₀ (actualFactor q) hq.ne').symm

/-- The zero-reserve analytic branch is the actual spiral factor for all small positive q. -/
theorem spiralFactor_eq_branch : ∀ᶠ q in 𝓝[>] (0 : ℝ),Spiral.factor q=q*spiralBranch.r q := by
  have hp : ∀ᶠ q in 𝓝 (0 : ℝ),0<spiralBranch.r q :=
    spiralBranch.analytic.continuousAt.eventually (lt_mem_nhds (by rw [spiralBranch.initial]; exact leading_pos))
  filter_upwards [spiralBranch.equation.filter_mono nhdsWithin_le_nhds,
    hp.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin,
    (gt_mem_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds] with q he hp hq hq1
  have hh:=sourceEquation_spiral q (spiralBranch.r q)
  rw [he,mul_zero] at hh
  have hpoly : Spiral.spiralPolynomial (q*spiralBranch.r q) q=0 := by
    exact (mul_eq_zero.mp hh.symm).resolve_left (by positivity)
  exact (Spiral.existsUnique_spiral_root hq hq1).unique (Spiral.factor_spec hq hq1) ⟨mul_pos hq hp,hpoly⟩

/-- The first printed small-q expansion is now for the actual exact heavy-ball rate. -/
theorem actualFactor_expansion :
    (fun q => actualFactor q-((1+Real.sqrt 2)*q-(2+3*Real.sqrt 2/2)*q^2))
      =O[𝓝[>] (0 : ℝ)] (fun q => q^3) := by
  have hh:=(optimalBranch.factor_expansion sourceA_analytic).mono
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ)≤𝓝 0)
  apply hh.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [actualFactor_eq_branch] with q hq
  rw [hq]
  rfl

/-- The strict spiral excess has the complete printed cubic coefficient and quartic remainder. -/
theorem actual_spiral_excess_expansion :
    (fun q => actualFactor q-Spiral.factor q-((10+7*Real.sqrt 2)/4)*q^3)
      =O[𝓝[>] (0 : ℝ)] (fun q => q^4) := by
  have hh:=(branch_difference_expansion optimalBranch spiralBranch sourceA_analytic sourceA_zero).mono
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ)≤𝓝 0)
  apply hh.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [actualFactor_eq_branch,spiralFactor_eq_branch] with q hq hs
  rw [hq,hs]
  rfl

end
end polyak.Asymptotics.SmallQ
