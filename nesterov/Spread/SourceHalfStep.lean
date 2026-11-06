import nesterov.Spread.HalfStep
import nesterov.Spread.ComplexSlacks

/-! The source formulation assumes amplitude and phase continuity only on
the real band. A proved clipped extension supplies the internal coordinates. -/
namespace nesterov.Spread
noncomputable section
open MeasureTheory Spectral Set
open scoped BigOperators NNReal

structure SourceHalfStepData where
  pair : SymbolPair
  t : ℝ
  K : ℕ
  s : ℝ
  eta : ℝ
  defect : ℝ
  radial : ℝ→ℝ
  phase : ℝ→ℝ
  t_neg : t<0
  K_ge : 3≤K
  s_pos : 0<s
  s_le : s≤canonicalKernel.s1
  eta_pos : 0<eta
  eta_lt : eta<1
  defect_nonneg : 0≤defect
  defect_le : defect≤bandMargin canonicalKernel K s/2
  small : canonicalKernel.longConstant*(|t|/(bandMargin canonicalKernel K s*(s*centerAngle K)))^2+
    defect<Real.sqrt eta/8
  radial_cont : ContinuousOn radial (Icc (centerAngle K-s*centerAngle K) (centerAngle K+s*centerAngle K))
  phase_cont : ContinuousOn phase (Icc (centerAngle K-s*centerAngle K) (centerAngle K+s*centerAngle K))
  radial_pos : ∀ ω∈Icc (centerAngle K-s*centerAngle K) (centerAngle K+s*centerAngle K),0<radial ω
  polar : ∀ ω∈Icc (centerAngle K-s*centerAngle K) (centerAngle K+s*centerAngle K),
    (g pair (Phase.frequency ω):ℂ)-2*Complex.I*skew pair (Phase.frequency ω)=
      (radial ω:ℂ)*Complex.exp (-(phase ω:ℂ)*Complex.I)
  phase_defect : ∀ ω∈Icc (centerAngle K-s*centerAngle K) (centerAngle K+s*centerAngle K),
    |ω-2*phase ω|≤defect

namespace SourceHalfStepData
variable (D : SourceHalfStepData)

theorem band_order : centerAngle D.K-D.s*centerAngle D.K≤centerAngle D.K+D.s*centerAngle D.K := by
  have h := mul_pos D.s_pos (centerAngle_pos D.K_ge)
  linarith

def toHalfStep : HalfStepData where
  pair := D.pair
  t := D.t
  K := D.K
  s := D.s
  eta := D.eta
  defect := D.defect
  radial := extendBand D.band_order D.radial D.radial_cont
  phase := extendBand D.band_order D.phase D.phase_cont
  t_neg := D.t_neg
  K_ge := D.K_ge
  s_pos := D.s_pos
  s_le := D.s_le
  eta_pos := D.eta_pos
  eta_lt := D.eta_lt
  defect_nonneg := D.defect_nonneg
  defect_le := D.defect_le
  small := D.small
  radial_pos := extendBand_positive D.band_order D.radial D.radial_cont D.radial_pos
  polar := by
    intro c hc
    have he : Phase.frequency (Real.arccos (c:ℝ))=c := by
      apply Subtype.ext
      exact Real.cos_arccos c.property.1 c.property.2
    rw [extendBand_eq D.band_order D.radial D.radial_cont hc,
      extendBand_eq D.band_order D.phase D.phase_cont hc]
    simpa only [he] using D.polar (Real.arccos (c:ℝ)) hc
  phase_defect := by
    intro c hc
    rw [extendBand_eq D.band_order D.phase D.phase_cont hc]
    exact D.phase_defect _ hc

/-- All noncritical lags and the strict minimizer reserve, with only the
source's bandwise amplitude/phase regularity. -/
theorem noncritical :
    0<meanG D.toHalfStep.probability D.pair ∧
    |D.toHalfStep.charge|<meanG D.toHalfStep.probability D.pair ∧
    (∀ n : ℕ,1≤n → 0<upperSlack D.pair D.t D.toHalfStep.probability D.toHalfStep.charge n) ∧
    (∀ n : ℕ,2≤n → 0<lowerSlack D.pair D.t D.toHalfStep.probability D.toHalfStep.charge n) :=
  D.toHalfStep.noncritical

/-- The literal averaged lag-one premise completes feasibility and supplies
finite atoms on the original band. -/
theorem feasible_and_finite
    (hfirst : D.eta*Real.exp D.t*Real.sinh |D.t| *meanG D.toHalfStep.probability D.pair<
      ∫ c,lagOneSymbol D.pair D.t c ∂D.toHalfStep.probability) :
    Feasible D.pair D.t D.toHalfStep.probability D.toHalfStep.charge ∧
    ∃ (J : Type) (_ : Fintype J) (w : J→ℝ≥0) (c : J→Frequency)
      (hw : ∑ j,w j=1), (∀ j,c j∈bandCarrier D.K D.s) ∧
      ∃ C : ℝ,Feasible D.pair D.t (finiteSpectrum w c hw) C ∧
        |C|<meanG (finiteSpectrum w c hw) D.pair :=
  ⟨D.toHalfStep.feasible_of_first_lag hfirst,D.toHalfStep.finite_of_first_lag hfirst⟩

end SourceHalfStepData
end
end nesterov.Spread
