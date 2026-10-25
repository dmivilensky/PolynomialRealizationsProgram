import polyak.Boundary.P5.DerivativeSource
import polyak.Boundary.P5.P2Endpoint

/-! Analytic and one-sided inverse-coordinate calculus for the central source family. -/
namespace polyak.Boundary.P5
noncomputable section
open Spectral Filter Set
open scoped Topology

def centralExponentArc : Set ℝ := {t | Real.cosh t≤P2.Ga}

theorem centralParameter_mem {t : ℝ} (hl : 1<Real.cosh t) (hu : Real.cosh t≤P2.Ga) :
    Real.cosh t-1∈Ioo (0 : ℝ) (11791/500000) :=
  ⟨by linarith,(by linarith [centralEndpoint_lt])⟩

theorem hasDerivWithinAt_of_branch (F : ℝ → ℝ)
    (hformula : ∀ h∈Icc (0 : ℝ) (P2.Ga-1),∀ t : ℝ,Real.cosh t=1+h →
      F t=Real.arsinh (continuationU h)) {t : ℝ} (hl : 1<Real.cosh t) (hu : Real.cosh t≤P2.Ga) :
    HasDerivWithinAt F (boundaryDerivative t) centralExponentArc t := by
  have hh:=centralParameter_mem hl hu
  have hd':=sourceValue_hasDerivAt hh
  have he : F=ᶠ[𝓝[centralExponentArc] t]
      (fun s => Real.arsinh (continuationU (Real.cosh s-1))) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hformula (Real.cosh s-1) ⟨by linarith [Real.one_le_cosh s],by
      change Real.cosh s≤P2.Ga at hs
      linarith⟩ s (by ring)
  apply hd'.hasDerivWithinAt.congr_of_eventuallyEq he
  exact hformula (Real.cosh t-1) ⟨by linarith,by linarith⟩ t (by ring)

theorem abs_boundaryDerivative_lt_one_of_source {t : ℝ}
    (hdu : |Selection.continuation (Real.cosh t-1) 0+
      (Real.cosh t-1)*deriv Selection.continuation (Real.cosh t-1) 0|<1) (hl : 1<Real.cosh t)
    (hu : Real.cosh t≤P2.Ga) : |boundaryDerivative t|<1 := by
  have hd:=hdu
  have hs : |Real.sinh t|<1 := by
    have he:=Real.sinh_sq t
    have hg:=P2.Ga_bounds.2
    nlinarith [sq_abs (Real.sinh t),abs_nonneg (Real.sinh t),Real.one_le_cosh t]
  have hroot : 1≤Real.sqrt (1+continuationU (Real.cosh t-1)^2) := by
    calc
      (1 : ℝ)=Real.sqrt 1 := Real.sqrt_one.symm
      _≤Real.sqrt (1+continuationU (Real.cosh t-1)^2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (continuationU (Real.cosh t-1))])
  have hr : 0<Real.sqrt (1+continuationU (Real.cosh t-1)^2) := by linarith
  unfold boundaryDerivative
  rw [abs_div,abs_mul,abs_of_pos hr]
  apply (div_lt_one hr).mpr
  have hm:=mul_le_mul_of_nonneg_right hd.le (abs_nonneg (Real.sinh t))
  nlinarith

theorem hasDerivAt_of_branch (F : ℝ → ℝ)
    (hformula : ∀ h∈Icc (0 : ℝ) (P2.Ga-1),∀ t : ℝ,Real.cosh t=1+h →
      F t=Real.arsinh (continuationU h)) {t : ℝ} (hl : 1<Real.cosh t) (hu : Real.cosh t<P2.Ga) :
    HasDerivAt F (boundaryDerivative t) t := by
  apply (hasDerivWithinAt_of_branch F hformula hl hu.le).hasDerivAt
  exact Filter.mem_of_superset
    (Real.continuous_cosh.continuousAt.eventually (gt_mem_nhds hu))
      (fun s hs => show Real.cosh s≤P2.Ga from hs.le)

theorem analyticAt_of_branch (F : ℝ → ℝ)
    (hformula : ∀ h∈Icc (0 : ℝ) (P2.Ga-1),∀ t : ℝ,Real.cosh t=1+h →
      F t=Real.arsinh (continuationU h)) {t : ℝ} (hl : 1<Real.cosh t) (hu : Real.cosh t<P2.Ga) :
    AnalyticAt ℝ F t := by
  have ha : AnalyticAt ℝ (fun s => Real.cosh s-1) t := by fun_prop
  have hU : AnalyticAt ℝ (fun s => continuationU (Real.cosh s-1)) t :=
    AnalyticAt.comp (g:=continuationU) (f:=fun s => Real.cosh s-1)
      (continuationU_analyticAt (centralParameter_mem hl hu.le)) ha
  have hf : AnalyticAt ℝ (fun s => Real.arsinh (continuationU (Real.cosh s-1))) t :=
    Real.analyticAt_arsinh.comp hU
  apply hf.congr
  have hn : ∀ᶠ s in 𝓝 t,Real.cosh s<P2.Ga :=
    Real.continuous_cosh.continuousAt.eventually (gt_mem_nhds hu)
  filter_upwards [hn] with s hs
  exact (hformula (Real.cosh s-1) ⟨by linarith [Real.one_le_cosh s],by linarith⟩ s (by ring)).symm

/-- The negative exact P₂ junction has its actual right derivative from P₅. -/
theorem hasDerivWithinAt_right_of_branch (F : ℝ → ℝ)
    (hformula : ∀ h∈Icc (0 : ℝ) (P2.Ga-1),∀ t : ℝ,Real.cosh t=1+h →
      F t=Real.arsinh (continuationU h)) {t : ℝ} (ht : t<0) (hu : Real.cosh t≤P2.Ga) :
    HasDerivWithinAt F (boundaryDerivative t) (Ici t) t := by
  have hl : 1<Real.cosh t := Real.one_lt_cosh.mpr ht.ne
  apply (hasDerivWithinAt_of_branch F hformula hl hu).mono_of_mem_nhdsWithin
  filter_upwards [(gt_mem_nhds ht).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hs hst
  change Real.cosh s≤P2.Ga
  change t≤s at hst
  have habs : |s|≤|t| := by rw [abs_of_neg hs,abs_of_neg ht]; linarith
  exact (Real.cosh_le_cosh.mpr habs).trans hu

end
end polyak.Boundary.P5
