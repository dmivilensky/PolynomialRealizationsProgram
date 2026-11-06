import nesterov.Attainment.DualMeasure
import nesterov.Attainment.FiniteSupport
import nesterov.Attainment.Optimal

/-! An actual probability measure on compactified signed lag labels represents
one common analytic limiting dual. It is carried by constraints active for
every optimal feasible pair, exactly as in the finite-support lemma. -/
noncomputable section
open MeasureTheory Set
open scoped Topology OnePoint
namespace nesterov.Attainment
open Spectral

structure BoundaryDual (M : StationaryMethod) (μ L : ℝ) where
  frame : ExponentFrame (Closure.T M μ L)
  d : DualPoint frame.lo frame.hi
  Λ : DualMeasure
  mem_hull : d ∈ polynomialDualHull M.queryPolynomial (M.normalizedPolynomial μ L)
    frame.lo frame.hi frame.sign (half_pos frame.radius_pos)
  charge : d.1=0
  nonpositive : ∀ c : Frequency,
    (d.2 (frame.center,physicalAngle frame.lo (half_pos frame.radius_pos) c)).re ≤ 0
  barycenter : ∀ F : DualPoint frame.lo frame.hi →L[ℝ] ℝ,
    (∫ l,F (dualLabelMap frame.lo frame.hi (half_pos frame.radius_pos)
      (gapEntireMap M.queryPolynomial (M.normalizedPolynomial μ L) frame.lo frame.hi frame.sign)
      (skewEntireMap M.queryPolynomial (M.normalizedPolynomial μ L) frame.lo frame.hi frame.sign) l) ∂Λ)=F d

theorem exists_boundaryDual (M : StationaryMethod) {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) (ht : Closure.T M μ L ≠ 0) : Nonempty (BoundaryDual M μ L) := by
  obtain ⟨F⟩ := exists_exponentFrame ht
  obtain ⟨d,Λ,hd,hcharge,hneg,hrep⟩ := exists_limiting_dual_measure_of_sequence
    M.queryPolynomial (M.normalizedPolynomial μ L) F.lo F.hi F.sign (half_pos F.radius_pos)
    F.center F.approaching F.approaching_tendsto (frame_strictCertificates M hμ hμL F)
  exact ⟨⟨F,d,Λ,hd,hcharge,hneg,hrep⟩⟩

namespace BoundaryDual
variable {M : StationaryMethod} {μ L : ℝ} (B : BoundaryDual M μ L)

def generator : C(DualLabel,DualPoint B.frame.lo B.frame.hi) :=
  dualLabelMap B.frame.lo B.frame.hi (half_pos B.frame.radius_pos)
    (gapEntireMap M.queryPolynomial (M.normalizedPolynomial μ L) B.frame.lo B.frame.hi B.frame.sign)
    (skewEntireMap M.queryPolynomial (M.normalizedPolynomial μ L) B.frame.lo B.frame.hi B.frame.sign)

def symbol (c : Frequency) : ℝ :=
  (B.d.2 (B.frame.center,physicalAngle B.frame.lo (half_pos B.frame.radius_pos) c)).re

def zeroSet : Set Frequency :=
  dualZeros B.frame.lo B.frame.hi (half_pos B.frame.radius_pos) B.frame.center B.d

theorem pair_eq : polynomialPair M.queryPolynomial (M.normalizedPolynomial μ L)
    (B.frame.sign*B.frame.center) = M.symbolPair μ L (Closure.T M μ L) := by
  rw [show B.frame.sign*(B.frame.center : ℝ)=Closure.T M μ L from B.frame.physical]
  rfl

theorem gap_endpoint_neg (hμ : 0 < μ) (hμL : μ < L)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L)
    (c : Frequency) (hc : (c:ℝ)=1 ∨ (c:ℝ)= -1) :
    g (polynomialPair M.queryPolynomial (M.normalizedPolynomial μ L) (B.frame.sign*B.frame.center)) c < 0 := by
  rw [B.pair_eq]
  exact nesterov.Attainment.gap_endpoint_neg M hμ hμL htq c hc

theorem zeroSet_finite (hμ : 0 < μ) (hμL : μ < L)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L) : B.zeroSet.Finite :=
  dualZeros_finite _ _ _ _ _ _ _ B.mem_hull (B.gap_endpoint_neg hμ hμL htq oneFrequency (Or.inl rfl))

theorem zeroSet_interior (hμ : 0 < μ) (hμL : μ < L)
    (htq : Real.log (Rates.quadraticRate M μ L) < Closure.T M μ L)
    {c : Frequency} (hc : c ∈ B.zeroSet) : -1 < (c:ℝ) ∧ (c:ℝ) < 1 :=
  dualZeros_interior _ _ _ _ _ _ _ B.mem_hull (B.gap_endpoint_neg hμ hμL htq) hc

theorem measure_carried {ν : Spectrum} {C : ℝ}
    (h : Feasible (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) ν C) :
    (ν : Measure Frequency) B.zeroSetᶜ=0 := by
  have hpos := B.frame.feasible_to_positive h
  rw [← B.pair_eq] at hpos
  have hm := dualHull_moment_nonneg _ _ _ _ _ _ _ hpos B.mem_hull
  rw [B.charge,zero_mul,add_zero] at hm
  exact measure_compl_dualZeros_eq_zero B.frame.lo B.frame.hi (half_pos B.frame.radius_pos)
    B.frame.center B.d ν B.nonpositive (fun c => dualHull_trace_im_zero _ _ _ _ _ _ _ B.mem_hull c) hm

def normalizedSlack (ν : Spectrum) (C : ℝ) (l : DualLabel) : ℝ :=
  dualMomentCLM B.frame.lo B.frame.hi (half_pos B.frame.radius_pos) B.frame.center
    (B.frame.sign*C) ν (B.generator l)

theorem normalizedSlack_continuous (ν : Spectrum) (C : ℝ) :
    Continuous (B.normalizedSlack ν C) :=
  (dualMomentCLM _ _ _ _ _ _).continuous.comp B.generator.continuous

theorem normalizedSlack_nonneg {ν : Spectrum} {C : ℝ}
    (h : Feasible (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) ν C)
    (l : DualLabel) : 0 ≤ B.normalizedSlack ν C l := by
  have hpos := B.frame.feasible_to_positive h
  rw [← B.pair_eq] at hpos
  exact generator_moment_nonneg _ _ _ _ _ _ _ hpos ⟨l,rfl⟩

/-- The same actual dual probability measure is carried by active constraints
for every optimal feasible pair. The two infinity labels remain distinct. -/
theorem measure_active {ν : Spectrum} {C : ℝ}
    (h : Feasible (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) ν C) :
    (B.Λ : Measure DualLabel) {l | B.normalizedSlack ν C l=0}ᶜ=0 := by
  let F := dualMomentCLM B.frame.lo B.frame.hi (half_pos B.frame.radius_pos) B.frame.center
    (B.frame.sign*C) ν
  have hF : F B.d=0 := by
    have hpos := B.frame.feasible_to_positive h
    rw [← B.pair_eq] at hpos
    have hm := dualHull_moment_nonneg _ _ _ _ _ _ _ hpos B.mem_hull
    rw [B.charge,zero_mul,add_zero] at hm
    change (∫ c,(B.d.2 (B.frame.center,physicalAngle B.frame.lo (half_pos B.frame.radius_pos) c)).re ∂ν)+
      (B.frame.sign*C)*B.d.1=0
    rw [B.charge,mul_zero,add_zero]
    exact le_antisymm (integral_nonpos B.nonpositive) hm
  have hi : Integrable (B.normalizedSlack ν C) (B.Λ : Measure DualLabel) :=
    (B.normalizedSlack_continuous ν C).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hzero : (∫ l,B.normalizedSlack ν C l ∂B.Λ)=0 := (B.barycenter F).trans hF
  have hae := (integral_eq_zero_iff_of_nonneg (B.normalizedSlack_nonneg h) hi).mp hzero
  exact (ae_iff).mp hae

end BoundaryDual
end nesterov.Attainment
