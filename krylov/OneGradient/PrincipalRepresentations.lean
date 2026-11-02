import krylov.OneGradient.EndpointAtoms
import krylov.OneGradient.RadauUniqueness
import krylov.OneGradient.MissingMomentRange
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(b), original principal representations.
Use: identify the two actual physical Gauss--Radau endpoint measures as the
unique missing-moment extremizers among all original supported probability measures.
Source: classical Radau localizing-square uniqueness, here applied to the
constructed genuine full-atom physical endpoint measures and original moments.
-/

namespace krylov.OneGradient
noncomputable section
open Polynomial Matrix MeasureTheory krylov.Reference jacobi.Finite
variable {n : ℕ}

/-- Every actual spectral endpoint completion is the unique supported
probability measure with its known moments and its extremal first missing moment.
Use: the original principal representations are unique among all measures,
without a finite-support restriction on the competitor.
Article: main_krylov, s5:moment(b).
Proof: genuine physical endpoint eigenvectors supply their positive endpoint
atoms, and all n+1 atoms are present. The original low moments and final
moment equality give the real Radau localizer uniqueness hypotheses. -/
theorem spectral_endpoint_measure_unique
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (I : chebyshev1.SpectralInterval)
    (hne : ∃ b : ℝ,(lanczosCompletion A hA g hg hc b-I.mu • 1).PosSemidef ∧
      (I.L • 1-lanczosCompletion A hA g hg hc b).PosSemidef)
    (b : ℝ) (hC : (lanczosCompletion A hA g hg hc b).PosDef)
    (hend : b=spectralLowerPivot A hA g hg hc I.mu ∨ b=spectralUpperPivot A hA g hg hc I.L)
    (sigma : Measure ℝ) [IsProbabilityMeasure sigma]
    (hs : ∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L)
    (hm : ∀ k≤2*n,measureMoment sigma k=gradientMoment A hA g hg k)
    (hlast : measureMoment sigma (2*n+1)=gradientMoment (lanczosCompletion A hA g hg hc b) hC g hg (2*n+1)) :
    sigma=gradientProbabilityMeasure (lanczosCompletion A hA g hg hc b) hC g hg := by
  let C := lanczosCompletion A hA g hg hc b
  let M := gradientSpectralData C hC g hg
  have hcount : (activeSpectralValues C hC.1 g).card=n+1 :=
    (gradientSpectralData_count C hC g).trans (completion_full_atoms A hA g hg hc b hC)
  have hnode : (∃ j,M.node j=I.mu) ∨ (∃ j,M.node j=I.L) := by
    obtain ⟨hlo,hhi,hl,hh⟩ := spectral_endpoint_atoms A hA g hg hc I hne
    rcases hend with rfl|rfl
    · exact Or.inl hl
    · exact Or.inr hh
  apply endpoint_radau_unique M hcount I hnode sigma hs
  intro k hk
  rw [discrete_gradient_moment]
  by_cases hsmall : k≤2*n
  · exact (hm k hsmall).trans (fibre_fixed_gradient_moments A hA g hg hc b hC k hsmall).symm
  · have he : k=2*n+1 := by omega
    subst k
    exact hlast

/-- The genuine physical lower and upper endpoint probability measures are
exactly the unique principal representations attaining their original affine
missing-moment extrema.
Use: close the endpoint clause of the all-probability-measure moment theorem
with actual n+1 positive atoms, prescribed nodes and uniqueness, including a
collapsed interval where the two actual measures coincide.
Article: main_krylov, s5:moment(b); s5:fibre(b), Gauss--Radau rules.
Proof: original spectral feasibility derives both actual positive endpoint
completions and their positive endpoint atoms. Their known moments and support
are genuine; the proved Radau uniqueness identifies each endpoint candidate. -/
theorem spectral_principal_representations
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (I : chebyshev1.SpectralInterval)
    (hne : ∃ b : ℝ,(lanczosCompletion A hA g hg hc b-I.mu • 1).PosSemidef ∧
      (I.L • 1-lanczosCompletion A hA g hg hc b).PosSemidef) :
    let lo := spectralLowerPivot A hA g hg hc I.mu
    let hi := spectralUpperPivot A hA g hg hc I.L
    let c := ((gradientSpectralData A hA g hg).reconstructed.data.linkProduct n)^2
    let d := gradientMoment A hA g hg (2*n+1)-c*lastJacobiPivot A hA g hg hc
    ∃ hlo : (lanczosCompletion A hA g hg hc lo).PosDef,
      ∃ hhi : (lanczosCompletion A hA g hg hc hi).PosDef,
      let low := gradientProbabilityMeasure (lanczosCompletion A hA g hg hc lo) hlo g hg
      let high := gradientProbabilityMeasure (lanczosCompletion A hA g hg hc hi) hhi g hg
      (∀ᵐ x ∂low,x∈Set.Icc I.mu I.L) ∧ (∀ᵐ x ∂high,x∈Set.Icc I.mu I.L) ∧
      (∀ k≤2*n,measureMoment low k=gradientMoment A hA g hg k ∧
        measureMoment high k=gradientMoment A hA g hg k) ∧
      ((activeSpectralValues (lanczosCompletion A hA g hg hc lo) hlo.1 g).card=n+1) ∧
      ((activeSpectralValues (lanczosCompletion A hA g hg hc hi) hhi.1 g).card=n+1) ∧
      (∃ j,(gradientSpectralData (lanczosCompletion A hA g hg hc lo) hlo g hg).node j=I.mu) ∧
      (∃ j,(gradientSpectralData (lanczosCompletion A hA g hg hc hi) hhi g hg).node j=I.L) ∧
      (∀ sigma : Measure ℝ,IsProbabilityMeasure sigma →
        (∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L) →
        (∀ k≤2*n,measureMoment sigma k=gradientMoment A hA g hg k) →
        (measureMoment sigma (2*n+1)=c*lo+d ↔ sigma=low) ∧
        (measureMoment sigma (2*n+1)=c*hi+d ↔ sigma=high)) := by
  let lo := spectralLowerPivot A hA g hg hc I.mu
  let hi := spectralUpperPivot A hA g hg hc I.L
  obtain ⟨hlo,hhi,hlnode,hhnode⟩ := spectral_endpoint_atoms A hA g hg hc I hne
  have hr := physical_spectral_fibre_interval A hA g hg hc I.mu I.L hne
  have hlband := (hr.2 lo).mpr ⟨le_rfl,hr.1⟩
  have hhband := (hr.2 hi).mpr ⟨hr.1,le_rfl⟩
  refine ⟨hlo,hhi,gradient_probability_supported _ hlo g hg I.mu I.L hlband.1 hlband.2,
    gradient_probability_supported _ hhi g hg I.mu I.L hhband.1 hhband.2,?_,?_,?_,hlnode,hhnode,?_⟩
  · intro k hk
    simp only [gradient_probability_moment]
    exact ⟨fibre_fixed_gradient_moments A hA g hg hc lo hlo k hk,
      fibre_fixed_gradient_moments A hA g hg hc hi hhi k hk⟩
  · exact (gradientSpectralData_count _ hlo g).trans (completion_full_atoms A hA g hg hc lo hlo)
  · exact (gradientSpectralData_count _ hhi g).trans (completion_full_atoms A hA g hg hc hi hhi)
  · intro sigma hprob hs hm
    let : IsProbabilityMeasure sigma := hprob
    have hlow := fibre_missing_gradient_moment A hA g hg hc lo hlo
    have hhigh := fibre_missing_gradient_moment A hA g hg hc hi hhi
    constructor
    · constructor
      · intro he
        exact spectral_endpoint_measure_unique A hA g hg hc I hne lo hlo (Or.inl rfl) sigma hs hm (he.trans hlow.symm)
      · rintro rfl
        rw [gradient_probability_moment]
        exact hlow
    · constructor
      · intro he
        exact spectral_endpoint_measure_unique A hA g hg hc I hne hi hhi (Or.inr rfl) sigma hs hm (he.trans hhigh.symm)
      · rintro rfl
        rw [gradient_probability_moment]
        exact hhigh

end
end krylov.OneGradient
