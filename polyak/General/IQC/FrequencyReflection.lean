import polyak.General.IQC.HomotopyRealFrequency
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Appendix D: the source Fourier convention uses exp(-ikω), whereas the
official Fourier-basis synthesis uses exp(+ikω).  Reflection is an actual
isometry on Lp.  Reflecting the matrix, transfer and transformed signals
together preserves both the pointwise graph condition and the IQC integral.
The final homotopy theorem therefore uses the article's real spatial
signals with the literal negative-exponential Fourier convention. -/

namespace polyak.General.IQC
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace Fourier
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

def reflectLp {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (x : Lp E p circleMeasure) : Lp E p circleMeasure :=
  Lp.compMeasurePreserving Neg.neg (Measure.measurePreserving_neg circleMeasure) x

theorem reflectLp_ae {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (x : Lp E p circleMeasure) : reflectLp x=ᵐ[circleMeasure] fun w=>x (-w) :=
  Lp.coeFn_compMeasurePreserving x (Measure.measurePreserving_neg circleMeasure)

theorem reflectLp_norm {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (x : Lp E p circleMeasure) : ‖reflectLp x‖=‖x‖ :=
  Lp.norm_compMeasurePreserving x (Measure.measurePreserving_neg circleMeasure)

theorem reflectLp_twice {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (x : Lp E p circleMeasure) : reflectLp (reflectLp x)=x := by
  have he := Lp.compMeasurePreserving_comp_apply x
    (Measure.measurePreserving_neg circleMeasure) (Measure.measurePreserving_neg circleMeasure)
  simpa [reflectLp,Function.comp_def] using he.symm

def frequencyReflection : ScalarFrequency→ₗᵢ[ℝ]ScalarFrequency :=
  Lp.compMeasurePreservingₗᵢ ℝ Neg.neg (Measure.measurePreserving_neg circleMeasure)

def sourceHalfLineTransform : SequenceSpace ℂ→ₗᵢ[ℝ]ScalarFrequency :=
  frequencyReflection.comp halfLineTransform

theorem sourceHalfLineTransform_ae (x : SequenceSpace ℂ) :
    sourceHalfLineTransform x=ᵐ[circleMeasure] fun w=>halfLineTransform x (-w) :=
  reflectLp_ae (halfLineTransform x)

theorem sourceHalfLineTransform_norm (x : SequenceSpace ℂ) :
    ‖sourceHalfLineTransform x‖=‖x‖ := sourceHalfLineTransform.norm_map x

theorem reflect_multiply (g : Lp ℂ ∞ circleMeasure) (x : ScalarFrequency) :
    reflectLp (multiply (scalarOperator g) x)=
      multiply (scalarOperator (reflectLp g)) (reflectLp x) := by
  apply Lp.ext
  have hm := (Measure.measurePreserving_neg circleMeasure).quasiMeasurePreserving.ae
    (multiply_ae (scalarOperator g) x)
  have hg := (Measure.measurePreserving_neg circleMeasure).quasiMeasurePreserving.ae
    (scalarOperator_ae g)
  filter_upwards [reflectLp_ae (multiply (scalarOperator g) x),hm,hg,
    multiply_ae (scalarOperator (reflectLp g)) (reflectLp x),
    scalarOperator_ae (reflectLp g),reflectLp_ae g,reflectLp_ae x]
    with w hR hm hg hm' hg' hRg hRx
  rw [hR,hm,hg,hm',hg',hRg,hRx]

/-- The same plant relation, in the literal source transform convention,
becomes the canonical relation with the reflected transfer. -/
theorem source_transform_to_canonical (g : Lp ℂ ∞ circleMeasure)
    (x y : SequenceSpace ℂ)
    (h : sourceHalfLineTransform y=multiply (scalarOperator g) (sourceHalfLineTransform x)) :
    halfLineTransform y=
      multiply (scalarOperator (reflectLp g)) (halfLineTransform x) := by
  have he := congrArg (fun z : ScalarFrequency=>reflectLp z) h
  change reflectLp (reflectLp (halfLineTransform y))=
    reflectLp (multiply (scalarOperator g) (reflectLp (halfLineTransform x))) at he
  simpa only [reflect_multiply,reflectLp_twice] using he

theorem canonical_transform_to_source (g : Lp ℂ ∞ circleMeasure)
    (x y : SequenceSpace ℂ)
    (h : halfLineTransform y=multiply (scalarOperator g) (halfLineTransform x)) :
    sourceHalfLineTransform y=
      multiply (scalarOperator (reflectLp g)) (sourceHalfLineTransform x) := by
  change reflectLp (halfLineTransform y)=
    multiply (scalarOperator (reflectLp g)) (reflectLp (halfLineTransform x))
  rw [h,reflect_multiply]

def sourceTransfer (h : ℕ→ℝ) : Lp ℂ ∞ circleMeasure := reflectLp (transfer h)

theorem sourceTransfer_ae (h : ℕ→ℝ) :
    sourceTransfer h=ᵐ[circleMeasure] fun w=>transfer h (-w) := reflectLp_ae _

def reflectMatrix (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) :
    Fin 2→Fin 2→Lp ℂ ∞ circleMeasure := fun i j=>reflectLp (P i j)

theorem reflectMatrix_ae (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) :
    ∀ᵐ w ∂circleMeasure,∀ i j,reflectMatrix P i j w=P i j (-w) :=
  ae_all_iff.mpr (fun i=>ae_all_iff.mpr (fun j=>reflectLp_ae (P i j)))

theorem reflectMatrix_twice (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) :
    reflectMatrix (reflectMatrix P)=P := by
  funext i j
  exact reflectLp_twice (P i j)

theorem joint_reflection_gap (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure)
    (G : Lp ℂ ∞ circleMeasure) {epsilon : ℝ}
    (hgap : ∀ᵐ w ∂circleMeasure,
      matrixGraphValue (P 0 0 w) (P 0 1 w) (P 1 0 w) (P 1 1 w) (G w)≤ -epsilon) :
    ∀ᵐ w ∂circleMeasure,matrixGraphValue
      (reflectMatrix P 0 0 w) (reflectMatrix P 0 1 w)
      (reflectMatrix P 1 0 w) (reflectMatrix P 1 1 w) (reflectLp G w)≤ -epsilon := by
  have hg := (Measure.measurePreserving_neg circleMeasure).quasiMeasurePreserving.ae hgap
  filter_upwards [hg,reflectMatrix_ae P,reflectLp_ae G] with w hw hP hG
  simp only [hP,hG]
  exact hw

private theorem scalarPoint_ae (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) :
    ∀ᵐ w ∂circleMeasure,∀ x y : ℂ,pointValue (scalarIQC P) w x y=
      inner ℝ x (P 0 0 w*x)+inner ℝ x (P 0 1 w*y)+
      inner ℝ y (P 1 0 w*x)+inner ℝ y (P 1 1 w*y) := by
  filter_upwards [scalarOperator_ae (P 0 0),scalarOperator_ae (P 0 1),
    scalarOperator_ae (P 1 0),scalarOperator_ae (P 1 1)] with w h00 h01 h10 h11
  intro x y
  simp only [pointValue,scalarIQC,h00,h01,h10,h11]

theorem joint_reflection_pointValue (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) :
    ∀ᵐ w ∂circleMeasure,∀ x y : ℂ,
      pointValue (scalarIQC (reflectMatrix P)) w x y=pointValue (scalarIQC P) (-w) x y := by
  have hp := (Measure.measurePreserving_neg circleMeasure).quasiMeasurePreserving.ae (scalarPoint_ae P)
  filter_upwards [scalarPoint_ae (reflectMatrix P),hp,reflectMatrix_ae P] with w hR hP hM
  intro x y
  rw [hR,hP]
  simp only [hM]

theorem joint_reflection_integral (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure)
    (x y : Energy.FrequencyCircle→ℂ) :
    (∫ w,pointValue (scalarIQC (reflectMatrix P)) w (x w) (y w) ∂circleMeasure)=
      ∫ w,pointValue (scalarIQC P) w (x (-w)) (y (-w)) ∂circleMeasure := by
  calc
    _ = ∫ w,pointValue (scalarIQC P) (-w) (x w) (y w) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [joint_reflection_pointValue P] with w hw
      exact hw (x w) (y w)
    _ = _ := by
      simpa only [neg_neg] using integral_neg_eq_self
        (fun w=>pointValue (scalarIQC P) w (x (-w)) (y (-w))) circleMeasure

theorem source_reflection_integral (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure)
    (x y : SequenceSpace ℂ) :
    (∫ w,pointValue (scalarIQC (reflectMatrix P)) w
      (halfLineTransform x w) (halfLineTransform y w) ∂circleMeasure)=
    ∫ w,pointValue (scalarIQC P) w
      (sourceHalfLineTransform x w) (sourceHalfLineTransform y w) ∂circleMeasure := by
  rw [joint_reflection_integral]
  apply integral_congr_ae
  filter_upwards [sourceHalfLineTransform_ae x,sourceHalfLineTransform_ae y] with w hx hy
  rw [hx,hy]

theorem source_gap_to_canonical (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure)
    (h : ℕ→ℝ) {epsilon : ℝ}
    (hgap : ∀ᵐ w ∂circleMeasure,
      matrixGraphValue (P 0 0 w) (P 0 1 w) (P 1 0 w) (P 1 1 w) (transfer h (-w))≤ -epsilon) :
    ∀ᵐ w ∂circleMeasure,
      matrixGraphValue (reflectMatrix P 0 0 w) (reflectMatrix P 0 1 w)
        (reflectMatrix P 1 0 w) (reflectMatrix P 1 1 w) (transfer h w)≤ -epsilon := by
  have hg := (Measure.measurePreserving_neg circleMeasure).quasiMeasurePreserving.ae hgap
  filter_upwards [hg,reflectMatrix_ae P] with w hw hP
  simp only [neg_neg] at hw
  simpa only [hP] using hw

end Fourier
namespace Feedback
open Fourier
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- The generic frequency homotopy theorem in the article's Fourier
convention. The bounded transfer, matrix and transformed real coordinate
signals are reflected together. No impulse-response representation is
assumed. -/
theorem homotopy_source_frequency_bound_of_transform {d : ℕ}
    (F : Feedback (EuclideanSpace ℝ (Fin d))) (g : Lp ℂ ∞ circleMeasure)
    (htransform : ∀ (i : Fin d) (x : SequenceSpace (EuclideanSpace ℝ (Fin d))),
      sourceHalfLineTransform (coordinateSignal i (F.plantL2 x))=
        multiply (scalarOperator g) (sourceHalfLineTransform (coordinateSignal i x)))
    (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) {epsilon : ℝ} (hepsilon : 0<epsilon)
    (hgap : ∀ᵐ w ∂circleMeasure,
      matrixGraphValue (P 0 0 w) (P 0 1 w) (P 1 0 w) (P 1 1 w) (g w)≤ -epsilon)
    (hpos : ∀ tau : ℝ,tau∈Icc (0:ℝ) 1→∀ x : SequenceSpace (EuclideanSpace ℝ (Fin d)),
      0≤∑ i : Fin d,∫ w,pointValue (scalarIQC P) w
        (sourceHalfLineTransform (coordinateSignal i x) w)
        (sourceHalfLineTransform (coordinateSignal i (tau • F.deltaL2 x)) w) ∂circleMeasure) :
    ∃ C : ℝ,0<C ∧ ∀ tau : ℝ,tau∈Icc (0:ℝ) 1→
      ∀ f : ℕ→EuclideanSpace ℝ (Fin d),SquareSummable f→
      SquareSummable (F.run tau f) ∧ sequenceNorm (F.run tau f)≤C*sequenceNorm f := by
  apply homotopy_real_frequency_bound_of_transform F (reflectLp g)
    (fun i x=>source_transform_to_canonical g _ _ (htransform i x))
    (reflectMatrix P) hepsilon (joint_reflection_gap P g hgap)
  intro tau htau x
  have he (i : Fin d) := source_reflection_integral P
    (coordinateSignal i x) (coordinateSignal i (tau • F.deltaL2 x))
  simpa only [he] using hpos tau htau x

/-- Every solution of the original real feedback equation inherits the
uniform estimate. Square summability is a conclusion about that solution. -/
theorem homotopy_source_frequency_solution_bound {d : ℕ}
    (F : Feedback (EuclideanSpace ℝ (Fin d))) (g : Lp ℂ ∞ circleMeasure)
    (htransform : ∀ (i : Fin d) (x : SequenceSpace (EuclideanSpace ℝ (Fin d))),
      sourceHalfLineTransform (coordinateSignal i (F.plantL2 x))=
        multiply (scalarOperator g) (sourceHalfLineTransform (coordinateSignal i x)))
    (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) {epsilon : ℝ} (hepsilon : 0<epsilon)
    (hgap : ∀ᵐ w ∂circleMeasure,
      matrixGraphValue (P 0 0 w) (P 0 1 w) (P 1 0 w) (P 1 1 w) (g w)≤ -epsilon)
    (hpos : ∀ tau : ℝ,tau∈Icc (0:ℝ) 1→∀ x : SequenceSpace (EuclideanSpace ℝ (Fin d)),
      0≤∑ i : Fin d,∫ w,pointValue (scalarIQC P) w
        (sourceHalfLineTransform (coordinateSignal i x) w)
        (sourceHalfLineTransform (coordinateSignal i (tau • F.deltaL2 x)) w) ∂circleMeasure) :
    ∃ C : ℝ,0<C ∧ ∀ tau : ℝ,tau∈Icc (0:ℝ) 1→
      ∀ f : ℕ→EuclideanSpace ℝ (Fin d),SquareSummable f→
      ∀ x : ℕ→EuclideanSpace ℝ (Fin d),x=F.plant (tau • F.delta x)+f→
      SquareSummable x ∧ sequenceNorm x≤C*sequenceNorm f := by
  obtain ⟨C,hC,hbound⟩ := homotopy_source_frequency_bound_of_transform F g htransform P
    hepsilon hgap hpos
  refine ⟨C,hC,?_⟩
  intro tau htau f hf x hx
  rw [F.eq_run_of_equation tau f x hx]
  exact hbound tau htau f hf

theorem homotopy_source_frequency_uniform_bound {d : ℕ}
    (F : Feedback (EuclideanSpace ℝ (Fin d))) {h : ℕ→ℝ}
    (hh : Summable (fun n=>|h n|)) (hF : ∀ x,F.plant x=convolution h x)
    (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) {epsilon : ℝ} (hepsilon : 0<epsilon)
    (hgap : ∀ᵐ w ∂circleMeasure,
      matrixGraphValue (P 0 0 w) (P 0 1 w) (P 1 0 w) (P 1 1 w) (transfer h (-w))≤ -epsilon)
    (hpos : ∀ tau : ℝ,tau∈Icc (0:ℝ) 1→∀ x : SequenceSpace (EuclideanSpace ℝ (Fin d)),
      0≤∑ i : Fin d,∫ w,pointValue (scalarIQC P) w
        (halfLineTransform (coordinateSignal i x) (-w))
        (halfLineTransform (coordinateSignal i (tau • F.deltaL2 x)) (-w)) ∂circleMeasure) :
    ∃ C : ℝ,0<C ∧ ∀ tau : ℝ,tau∈Icc (0:ℝ) 1→
      ∀ f : ℕ→EuclideanSpace ℝ (Fin d),SquareSummable f→
      SquareSummable (F.run tau f) ∧ sequenceNorm (F.run tau f)≤C*sequenceNorm f := by
  apply homotopy_real_frequency_uniform_bound F hh hF (reflectMatrix P) hepsilon
    (source_gap_to_canonical P h hgap)
  intro tau htau x
  have he (i : Fin d) := joint_reflection_integral P
    (fun w=>halfLineTransform (coordinateSignal i x) w)
    (fun w=>halfLineTransform (coordinateSignal i (tau • F.deltaL2 x)) w)
  simpa only [he] using hpos tau htau x

end Feedback
end
end polyak.General.IQC
