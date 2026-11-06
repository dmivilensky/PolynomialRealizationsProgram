import nesterov.Attainment.BoundaryDual
import nesterov.Attainment.HullAnalytic

/-! Public source-level projections of the actual limiting dual witness:
its probability representation, common analytic neighbourhood, strict
endpoint signs, and exact normalized lag functionals. -/
noncomputable section
open MeasureTheory Set
open scoped Topology OnePoint
namespace nesterov.Attainment
open Spectral

theorem ExponentFrame.radius_eq_abs {t : ℝ} (F : ExponentFrame t) : F.radius=|t| := by
  have hh := congrArg abs F.physical
  have hs : |F.sign|=1 := by rcases F.sign_cases with hs | hs <;> simp [hs]
  simpa only [abs_mul,hs,one_mul,abs_of_pos F.radius_pos] using hh

namespace BoundaryDual
variable {M : StationaryMethod} {μ L : ℝ} (B : BoundaryDual M μ L)

def complexSymbol : ℂ → ℂ :=
  polyak.Spectral.windowExtension (restrictSymbolCLM B.frame.lo B.frame.hi B.frame.center B.d)

theorem complexSymbol_holomorphic : DifferentiableOn ℂ B.complexSymbol (interior (LagWindow B.frame.lo)) :=
  polynomial_dualHull_holomorphic _ _ _ _ _ _ _ B.mem_hull

theorem physical_interior (c : Frequency) : (Real.arccos (c:ℝ) : ℂ) ∈ interior (LagWindow B.frame.lo) :=
  polyak.Spectral.real_mem_interior_lagWindow (half_pos B.frame.radius_pos)
    ⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩

theorem complexSymbol_physical (c : Frequency) :
    B.complexSymbol (Real.arccos (c:ℝ))=(B.symbol c:ℂ) := by
  have he := polyak.Spectral.windowExtension_coe
    (restrictSymbolCLM B.frame.lo B.frame.hi B.frame.center B.d)
    (physicalAngle B.frame.lo (half_pos B.frame.radius_pos) c)
  change B.complexSymbol (Real.arccos (c:ℝ))=
    B.d.2 (B.frame.center,physicalAngle B.frame.lo (half_pos B.frame.radius_pos) c) at he
  rw [he]
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using
      dualHull_trace_im_zero _ _ _ _ _ _ _ B.mem_hull c

theorem symbol_eq_integral (c : Frequency) :
    B.symbol c = ∫ l, ((B.generator l).2
      (B.frame.center,physicalAngle B.frame.lo (half_pos B.frame.radius_pos) c)).re ∂B.Λ :=
  (B.barycenter (traceCLM B.frame.lo B.frame.hi B.frame.center
    (physicalAngle B.frame.lo (half_pos B.frame.radius_pos) c))).symm

theorem symbol_endpoint_neg (hμ : 0 < μ) (hμL : μ < L)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L)
    (c : Frequency) (hc : (c:ℝ)=1 ∨ (c:ℝ)= -1) : B.symbol c < 0 :=
  dualHull_endpoint_neg _ _ _ _ _ _ _ c hc (B.gap_endpoint_neg hμ hμL htq c hc) B.mem_hull

/-- The source normalization N_n=sinh(n|T|)/sinh|T| differs from the
compact Banach normalization by this one common positive factor. -/
def sourceFunctional (l : DualLabel) (c : Frequency) : ℝ :=
  Real.sinh B.frame.radius * ((B.generator l).2
    (B.frame.center,physicalAngle B.frame.lo (half_pos B.frame.radius_pos) c)).re

def sourceSymbol (c : Frequency) : ℝ := Real.sinh B.frame.radius*B.symbol c

theorem sourceSymbol_eq_integral (c : Frequency) :
    B.sourceSymbol c=∫ l,B.sourceFunctional l c ∂B.Λ := by
  unfold sourceSymbol sourceFunctional
  rw [B.symbol_eq_integral,integral_const_mul]

theorem sourceSymbol_nonpositive (c : Frequency) : B.sourceSymbol c ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (Real.sinh_pos_iff.mpr B.frame.radius_pos).le (B.nonpositive c)

def sourceComplexSymbol (z : ℂ) : ℂ := (Real.sinh B.frame.radius:ℂ)*B.complexSymbol z

theorem sourceComplexSymbol_holomorphic :
    DifferentiableOn ℂ B.sourceComplexSymbol (interior (LagWindow B.frame.lo)) :=
  B.complexSymbol_holomorphic.const_mul (Real.sinh B.frame.radius:ℂ)

theorem sourceComplexSymbol_physical (c : Frequency) :
    B.sourceComplexSymbol (Real.arccos (c:ℝ))=(B.sourceSymbol c:ℂ) := by
  simp only [sourceComplexSymbol,B.complexSymbol_physical,sourceSymbol,Complex.ofReal_mul]

theorem sourceSymbol_endpoint_neg (hμ : 0 < μ) (hμL : μ < L)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L)
    (c : Frequency) (hc : (c:ℝ)=1 ∨ (c:ℝ)= -1) : B.sourceSymbol c < 0 :=
  mul_neg_of_pos_of_neg (Real.sinh_pos_iff.mpr B.frame.radius_pos)
    (B.symbol_endpoint_neg hμ hμL htq c hc)

theorem zeroSet_eq_sourceZeros : B.zeroSet={c | B.sourceSymbol c=0} := by
  ext c
  have him : (B.d.2 (B.frame.center,physicalAngle B.frame.lo
      (half_pos B.frame.radius_pos) c)).im=0 :=
    dualHull_trace_im_zero _ _ _ _ _ _ _ B.mem_hull c
  have hs : Real.sinh B.frame.radius≠0 := (Real.sinh_pos_iff.mpr B.frame.radius_pos).ne'
  change B.d.2 (B.frame.center,physicalAngle B.frame.lo (half_pos B.frame.radius_pos) c)=0 ↔
    Real.sinh B.frame.radius*B.symbol c=0
  rw [mul_eq_zero,or_iff_right hs]
  constructor
  · intro h
    change (B.d.2 _).re=0
    rw [h,Complex.zero_re]
  · intro h
    apply Complex.ext
    · exact h
    · simpa only [Complex.zero_im] using him

theorem sourceZeros_finite (hμ : 0<μ) (hμL : μ<L)
    (htq : Real.log (Rates.quadraticRate M μ L)<Closure.T M μ L) :
    {c | B.sourceSymbol c=0}.Finite := by
  rw [←B.zeroSet_eq_sourceZeros]
  exact B.zeroSet_finite hμ hμL htq

theorem source_measure_carried {ν : Spectrum} {C : ℝ}
    (h : Feasible (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) ν C) :
    (ν : Measure Frequency) {c | B.sourceSymbol c=0}ᶜ=0 := by
  rw [←B.zeroSet_eq_sourceZeros]
  exact B.measure_carried h

end BoundaryDual
end nesterov.Attainment
