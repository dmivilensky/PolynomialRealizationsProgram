import polyak.Global.Sampling.SampleSymmetry
import polyak.Global.Sampling.AliasingProduct
import polyak.Global.Sampling.AliasingBound

/-! The complete source aliasing lemma for genuine sampled measures.
The density is relative to probability Haar, so the weights are f/L;
with the source's Lebesgue density f/(2*pi), these are 2*pi*f_source/L. -/
noncomputable section
namespace polyak.Global.Sampling
open polyak.General MeasureTheory
open scoped ContDiff

theorem aliasing_lemma (q:Tuning) (s:ℝ) (f:C(Circle,ℝ))
    (hf:∀x,0≤f x) (heven:∀x,f (-x)=f x)
    (hSmooth:ContDiff ℝ ∞ (fun x=>f (Circle.ofReal x))) :
    ∃C:ℝ,0≤C ∧
      (∀L:ℕ,0<L→Circle.Symmetric (sampleMeasure f L)) ∧
      (∀L:ℕ,0<L→∀n m:ℤ,
        Circle.phaseMoment (phase q s) (phase_periodic q s) (sampleMeasure f L) (n+m*L)=
          Circle.phaseMoment (phase q s) (phase_periodic q s) (sampleMeasure f L) n) ∧
      ∀L:ℕ,0<L→∀n:ℤ,2*|n|≤(L:ℤ)→
        ‖Circle.phaseMoment (phase q s) (phase_periodic q s) (sampleMeasure f L) n-
          Circle.phaseMoment (phase q s) (phase_periodic q s)
            (Circle.haar.withDensity (fun x=>ENNReal.ofReal (f x))) n‖≤C/(L:ℝ)^2 := by
  obtain ⟨D,hD,hcoeff⟩:=densityPhase_fourier_decay q s f hSmooth
  obtain ⟨C,hC,hbound⟩:=exists_aliasing_error_bound (densityPhase q s f) hD hcoeff
  refine ⟨C,hC,fun _ hL=>sampleMeasure_symmetric f heven hL,?_,?_⟩
  · intro L hL n m
    rw [phaseMoment_sampleMeasure q s f hf hL,phaseMoment_sampleMeasure q s f hf hL]
    exact sampleAverage_periodic _ hL n m
  · intro L hL n hn
    rw [phaseMoment_sampleMeasure q s f hf hL,phaseMoment_density q s f hf]
    exact hbound L hL n hn

end polyak.Global.Sampling
