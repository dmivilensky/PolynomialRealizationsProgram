import polyak.FareyPlateau.FanAnalysis.UniformTaylor
import polyak.FareyPlateau.FanAnalysis.PartialJets
import polyak.FareyPlateau.FanAnalysis.JetConverse

/-! Jointly analytic ambient tests turn their computed pointwise quadratic
limits into one compact-uniform estimate and one strict sign neighborhood. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Set Filter
open scoped Topology
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [CompactSpace X]

namespace AmbientUniform
variable (F : E×ℝ→ℝ) (coordinates : X→E) (hcoord : Continuous coordinates)
  {r : ℝ} (hr : 0<r)
  (hF : ∀x t,|t|<r → AnalyticAt ℝ F (coordinates x,t))

def fiber (x : X) (t : ℝ) : ℝ := F (coordinates x,t)

omit [TopologicalSpace X] [CompactSpace X] in
include hF in
theorem analytic_fiber (x : X) (t : ℝ) (ht : |t|<r) :
    AnalyticAt ℝ (fiber F coordinates x) t := by
  exact (hF x t ht).comp (f := fun u:ℝ=>(coordinates x,u)) (analyticAt_const.prod analyticAt_id)

omit [CompactSpace X] in
include hcoord hr hF in
theorem continuous_second (x : X) :
    ContinuousAt (fun p:X×ℝ=>deriv^[2] (fiber F coordinates p.1) p.2) (x,0) := by
  have hm : ContinuousAt (fun p:X×ℝ=>(coordinates p.1,p.2)) (x,0) :=
    (hcoord.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
  have hc := (continuousAt_partialSecond (hF x 0 (by simpa only [abs_zero] using hr))).comp
    (f := fun p:X×ℝ=>(coordinates p.1,p.2)) hm
  apply hc.congr_of_eventuallyEq
  have he : ∀ᶠ p:X×ℝ in 𝓝 (x,0),|p.2|<r :=
    continuousAt_snd.abs.eventually (eventually_lt_nhds (show |(0:ℝ)|<r by simpa only [abs_zero] using hr))
  filter_upwards [he] with p hp
  exact (partialSecond_eq_deriv (hF p.1 p.2 hp)).symm

include hcoord hr hF in
theorem quadratic_uniform (c : X→ℝ)
    (hlim : ∀x,Tendsto (fun δ=>F (coordinates x,δ)/δ^2) (𝓝[≠] 0) (𝓝 (c x)))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ δ in 𝓝[≠] (0:ℝ), ∀x,|F (coordinates x,δ)/δ^2-c x|<ε := by
  have hj (x : X) := quadratic_limit_zero_jets
    (analytic_fiber F coordinates hF x 0 (by simpa only [abs_zero] using hr)) (hlim x)
  have hh := uniform_quadratic_taylor (fiber F coordinates) hr
    (analytic_fiber F coordinates hF) (continuous_second F coordinates hcoord hr hF)
    (fun x=>(hj x).1) (fun x=>(hj x).2.1) hε
  simpa only [fiber,fun x=>(hj x).2.2] using hh

omit [CompactSpace X] in
include hcoord hr hF in
theorem continuous_coefficient (c : X→ℝ)
    (hlim : ∀x,Tendsto (fun δ=>F (coordinates x,δ)/δ^2) (𝓝[≠] 0) (𝓝 (c x))) : Continuous c := by
  have hc : Continuous (fun x=>partialSecond F (coordinates x,0)/2) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((continuousAt_partialSecond (hF x 0 (by simpa only [abs_zero] using hr))).comp
      (f := fun x:X=>(coordinates x,(0:ℝ))) (hcoord.continuousAt.prodMk continuousAt_const)).div_const 2
  apply hc.congr
  intro x
  rw [partialSecond_eq_deriv (hF x 0 (by simpa only [abs_zero] using hr))]
  exact (quadratic_limit_zero_jets (analytic_fiber F coordinates hF x 0
    (by simpa only [abs_zero] using hr)) (hlim x)).2.2

include hcoord hr hF in
theorem uniform_positive (c : X→ℝ)
    (hlim : ∀x,Tendsto (fun δ=>F (coordinates x,δ)/δ^2) (𝓝[≠] 0) (𝓝 (c x)))
    (hpos : ∀x,0<c x) : ∀ᶠ δ in 𝓝[≠] (0:ℝ), ∀x,0<F (coordinates x,δ) := by
  cases isEmpty_or_nonempty X with
  | inl h => exact Eventually.of_forall (fun _ x=>isEmptyElim x)
  | inr h =>
    obtain ⟨x₀,_hx₀,hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty
      (continuous_coefficient F coordinates hcoord hr hF c hlim).continuousOn
    have he := quadratic_uniform F coordinates hcoord hr hF c hlim (half_pos (hpos x₀))
    filter_upwards [he,self_mem_nhdsWithin] with δ hδ hz x
    have hbound : c x₀≤c x := hmin (mem_univ x)
    have hratio : 0<F (coordinates x,δ)/δ^2 := by
      have hh := (abs_lt.mp (hδ x)).1
      linarith [hpos x₀]
    have hp := mul_pos hratio (sq_pos_of_ne_zero hz)
    simpa only [div_mul_cancel₀ _ (pow_ne_zero 2 hz)] using hp

include hcoord hr hF in
theorem uniform_positive_of_pointwise
    (hlim : ∀x,∃c:ℝ,0<c ∧
      Tendsto (fun δ=>F (coordinates x,δ)/δ^2) (𝓝[≠] 0) (𝓝 c)) :
    ∀ᶠ δ in 𝓝[≠] (0:ℝ), ∀x,0<F (coordinates x,δ) := by
  classical
  choose c hpos hc using hlim
  exact uniform_positive F coordinates hcoord hr hF c hc hpos

end AmbientUniform
end polyak.FareyPlateau.FanAnalysis
