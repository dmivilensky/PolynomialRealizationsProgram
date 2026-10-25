import polyak.Global.Symbols.RealSeries
import polyak.Global.Symbols.Slackness
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The full residual-mass limit holds as a genuine weak limit against
arbitrary L¹ tests, with the uniform oscillatory tail proved analytically. -/
noncomputable section
namespace polyak.Global.Symbols
open Levels MeasureTheory Filter Set Topology
open scoped BigOperators

theorem realSymbol_integrals_tendsto {𝒩 : Set ℤ} (a : ℕ→Weights 𝒩) (b : Weights 𝒩)
    (hc : ∀n,Tendsto (fun j=>(a j).weight n) atTop (𝓝 (b.weight n)))
    (Θ : ℕ→Curve) (Ψ : Curve)
    (hΘ : ∀ω,Tendsto (fun j=>Θ j ω) atTop (𝓝 (Ψ ω)))
    {φ : ℝ→ℝ} (hφ : Integrable φ) :
    Tendsto (fun j=>∫x,(a j).realSymbol (Θ j) x*φ x) atTop
      (𝓝 (∫x,b.realSymbol Ψ x*φ x)) := by
  have hw := weighted_tsum_tendsto a b hc
    (fun j=>oscillatoryMoment (Θ j) φ) (oscillatoryMoment Ψ φ)
    (fun j n=>oscillatoryMoment_norm_bound (Θ j) hφ n)
    (fun n=>oscillatoryMoment_norm_bound Ψ hφ n)
    (fun n=>oscillatoryMoment_tendsto Θ Ψ hΘ hφ n)
    (fun ε hε=>oscillatoryMoment_uniform_tail Θ Ψ hΘ hφ ε hε)
  have ht := (oscillatoryMoment_tendsto Θ Ψ hΘ hφ 0).sub hw
  simp_rw [Weights.integral_realSymbol _ _ hφ]
  exact ht

/-- Positivity against all compactly supported nonnegative tests determines
pointwise sign on the whole closed source interval, including both endpoints. -/
theorem nonpos_on_interval_of_integral_tests (f : ℝ→ℝ) (hf : Continuous f)
    (htest : ∀φ : ℝ→ℝ,Integrable φ→(∀x,0≤φ x)→
      (∀x,x∉Icc (0:ℝ) Real.pi→φ x=0)→(∫x,f x*φ x)≤0) :
    ∀x∈Icc (0:ℝ) Real.pi,f x≤0 := by
  let g : ℝ→ℝ := fun x=>max (f x) 0
  let φ : ℝ→ℝ := (Icc (0:ℝ) Real.pi).indicator g
  have hg : Continuous g := hf.max continuous_const
  have hφ : Integrable φ := (integrable_indicator_iff measurableSet_Icc).mpr
    (hg.continuousOn.integrableOn_compact isCompact_Icc)
  have hφpos : ∀x,0≤φ x := by
    intro x
    by_cases hx : x∈Icc (0:ℝ) Real.pi
    · simp only [φ,indicator_of_mem hx,g];exact le_max_right _ _
    · simp only [φ,indicator_of_notMem hx,le_refl]
  have hφout : ∀x,x∉Icc (0:ℝ) Real.pi→φ x=0 := fun x hx=>indicator_of_notMem hx g
  have hi := htest φ hφ hφpos hφout
  have he : (fun x=>f x*φ x)=(Icc (0:ℝ) Real.pi).indicator (fun x=>(g x)^2) := by
    ext x
    by_cases hx : x∈Icc (0:ℝ) Real.pi
    · simp only [φ,indicator_of_mem hx]
      by_cases hfx : 0≤f x
      · simp only [g,max_eq_left hfx];ring
      · rw [show g x=0 from max_eq_right (le_of_not_ge hfx)]
        ring
    · simp only [φ,indicator_of_notMem hx,mul_zero]
  rw [he,integral_indicator measurableSet_Icc] at hi
  have hgs : IntegrableOn (fun x=>(g x)^2) (Icc (0:ℝ) Real.pi) :=
    (hg.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hz : (∫x in Icc (0:ℝ) Real.pi,(g x)^2)=0 :=
    le_antisymm hi (integral_nonneg (fun _=>sq_nonneg _))
  have hae := (integral_eq_zero_iff_of_nonneg (fun x=>sq_nonneg (g x)) hgs).mp hz
  have hzero : g=ᵐ[volume.restrict (Icc (0:ℝ) Real.pi)] (fun _=>0) := by
    filter_upwards [hae] with x hx
    exact (sq_eq_zero_iff).mp hx
  have hEq := Measure.eqOn_of_ae_eq hzero hg.continuousOn continuous_const.continuousOn
    (show Icc (0:ℝ) Real.pi⊆closure (interior (Icc (0:ℝ) Real.pi)) by
      simpa only [closure_interior_Icc (ne_of_lt Real.pi_pos)] using (subset_rfl : Icc (0:ℝ) Real.pi⊆Icc 0 Real.pi))
  intro x hx
  have hh := hEq hx
  change max (f x) 0=0 at hh
  linarith [le_max_left (f x) 0]

/-- The signs of all finite or infinite normalized input symbols pass to
the actual uniformly convergent residual-mass limit. -/
theorem limit_nonpos {𝒩 : Set ℤ} (a : ℕ→Weights 𝒩) (b : Weights 𝒩)
    (hc : ∀n,Tendsto (fun j=>(a j).weight n) atTop (𝓝 (b.weight n)))
    (Θ : ℕ→Curve) (Ψ : Curve)
    (hΘ : ∀ω,Tendsto (fun j=>Θ j ω) atTop (𝓝 (Ψ ω)))
    (hS : ∀j ω,(a j).eval (Θ j) ω≤0) : ∀ω,b.eval Ψ ω≤0 := by
  have ht : ∀φ : ℝ→ℝ,Integrable φ→(∀x,0≤φ x)→
      (∀x,x∉Icc (0:ℝ) Real.pi→φ x=0)→(∫x,b.realSymbol Ψ x*φ x)≤0 := by
    intro φ hφ hpos hout
    apply le_of_tendsto (realSymbol_integrals_tendsto a b hc Θ Ψ hΘ hφ)
    apply Eventually.of_forall
    intro j
    apply integral_nonpos
    intro x
    change (a j).realSymbol (Θ j) x*φ x≤0
    by_cases hx : x∈Icc (0:ℝ) Real.pi
    · have hs : (a j).realSymbol (Θ j) x≤0 := by
        rw [(a j).realSymbol_eq_eval (Θ j) ⟨x,hx⟩]
        exact hS j ⟨x,hx⟩
      exact mul_nonpos_of_nonpos_of_nonneg hs (hpos x)
    · rw [hout x hx,mul_zero]
  have hnp := nonpos_on_interval_of_integral_tests (b.realSymbol Ψ) (b.continuous_realSymbol Ψ) ht
  intro ω
  rw [←b.realSymbol_eq_eval Ψ ω]
  exact hnp ω ω.property

end polyak.Global.Symbols
