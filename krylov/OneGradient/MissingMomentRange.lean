import krylov.OneGradient.MomentAffine
import krylov.OneGradient.MomentAttainment
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(b), exact all-probability-measure missing-moment range.
Use: close both directions of the original Hausdorff moment interval for all
genuine supported probability measures, with actual physical endpoint attainment.
Source: the proved all-measures physical compression and affine missing-moment
formula, and actual supported positive spectral probability-measure construction.
-/

/-!
Article: krylov, Corollary C.9 [s5:moment].

All supported probability measures, not only n-atomic candidates, have exactly the printed
missing-moment range; the positive affine coefficient and endpoint uniqueness are proved.
The free canonical coordinate requires a positive endpoint gap. At a collapsed interval its
coordinate is fixed.
-/

namespace krylov.OneGradient
noncomputable section
open Polynomial Matrix MeasureTheory krylov.Reference
variable {n : ℕ}

/-- The original first-missing-moment value set over all genuine supported
probability measures sharing the observed original physical moments.
Use: the quantifiers include non-atomic and singular continuous candidates.
Article: main_krylov, s5:moment(b). -/
def missingMomentValues
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0) (I : chebyshev1.SpectralInterval) : Set ℝ :=
  {t | ∃ sigma : Measure ℝ,IsProbabilityMeasure sigma ∧
    (∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L) ∧
    (∀ k≤2*n,measureMoment sigma k=gradientMoment A hA g hg k) ∧ t=measureMoment sigma (2*n+1)}

/-- The exact original all-measures missing-moment range is the affine image
of the actual attained physical Gauss--Radau pivot interval.
Use: both inclusion and every-point attainment have the original probability
measure quantifiers; no atomic restriction or presumed completion model remains.
Article: main_krylov, s5:moment(b).
Proof: every actual candidate measure constructs a real admissible physical
pivot and has the printed affine moment. Conversely every actual pivot has
a constructed genuine supported spectral probability measure with those moments. -/
theorem missing_moment_range
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (I : chebyshev1.SpectralInterval)
    (hne : ∃ b : ℝ,(lanczosCompletion A hA g hg hc b-I.mu • 1).PosSemidef ∧
      (I.L • 1-lanczosCompletion A hA g hg hc b).PosSemidef) :
    let c := ((gradientSpectralData A hA g hg).reconstructed.data.linkProduct n)^2
    let d := gradientMoment A hA g hg (2*n+1)-c*lastJacobiPivot A hA g hg hc
    missingMomentValues A hA g hg I=
      (fun b : ℝ => c*b+d) '' Set.Icc (spectralLowerPivot A hA g hg hc I.mu) (spectralUpperPivot A hA g hg hc I.L) := by
  dsimp only
  ext t
  constructor
  · rintro ⟨sigma,hprob,hsupport,hm,ht⟩
    let : IsProbabilityMeasure sigma := hprob
    obtain ⟨b,hb,he⟩ := supported_measure_missing_moment A hA g hg hc sigma I hsupport hm
    exact ⟨b,hb,he.symm.trans ht.symm⟩
  · rintro ⟨b,hb,rfl⟩
    obtain ⟨sigma,hprob,hsupport,hm,he⟩ := spectral_moment_attainment A hA g hg hc I hne b hb
    exact ⟨sigma,hprob,hsupport,hm,he.symm⟩

/-- The actual original missing-moment affine coefficient is strictly positive.
Use: the closed moment interval has the same order and degeneracy as its
original physical Jacobi pivot interval.
Article: main_krylov, s5:moment(b).
Proof: the genuine reconstructed Jacobi coupling product is strictly positive
through the actual last active site, so its real square is positive. -/
theorem missing_moment_slope_positive
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) :
    0<((gradientSpectralData A hA g hg).reconstructed.data.linkProduct n)^2 := by
  apply sq_pos_of_pos
  exact jacobi.Finite.linkProduct_pos (gradientSpectralData A hA g hg).reconstructed_irreducible
    (show n<(activeSpectralValues A hA.1 g).card by rw [hc];omega)

/-- A true positive affine map takes the complete closed real interval onto
its exact endpoint image, including a collapsed interval.
Use: turn the all-measures image theorem into explicit attained minimum and maximum moments.
Article: main_krylov, s5:moment(b).
Proof: positive multiplication preserves both endpoint orders, and division by
its actual positive coefficient constructs every intermediate preimage. -/
theorem positive_affine_image_interval (c d lo hi : ℝ) (hc : 0 < c) :
    (fun b : ℝ => c*b+d) '' Set.Icc lo hi=Set.Icc (c*lo+d) (c*hi+d) := by
  ext t
  constructor
  · rintro ⟨b,⟨hblo,hbhi⟩,rfl⟩
    constructor <;> nlinarith
  · rintro ⟨htlo,hthi⟩
    refine ⟨(t-d)/c,⟨?_,?_⟩,?_⟩
    · apply (le_div_iff₀ hc).mpr
      linarith
    · apply (div_le_iff₀ hc).mpr
      linarith
    · change c*((t-d)/c)+d=t
      rw [mul_comm c ((t-d)/c),div_mul_cancel₀ _ hc.ne',sub_add_cancel]

/-- The original all-probability-measure first-missing-moment values are exactly
one attained closed interval with the actual physical Radau endpoint moments.
Use: every interior moment and both extrema are realized by genuine supported
probability measures, and no other moment is possible.
Article: main_krylov, s5:moment(b).
Proof: the proved exact all-measures affine image has its genuine positive
original coupling-product square coefficient. Positive affine interval mapping
gives the actual endpoint values, including coincident endpoint moments. -/
theorem missing_moment_closed_interval
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (I : chebyshev1.SpectralInterval)
    (hne : ∃ b : ℝ,(lanczosCompletion A hA g hg hc b-I.mu • 1).PosSemidef ∧
      (I.L • 1-lanczosCompletion A hA g hg hc b).PosSemidef) :
    let c := ((gradientSpectralData A hA g hg).reconstructed.data.linkProduct n)^2
    let d := gradientMoment A hA g hg (2*n+1)-c*lastJacobiPivot A hA g hg hc
    missingMomentValues A hA g hg I=
      Set.Icc (c*spectralLowerPivot A hA g hg hc I.mu+d) (c*spectralUpperPivot A hA g hg hc I.L+d) := by
  dsimp only
  rw [missing_moment_range A hA g hg hc I hne]
  exact positive_affine_image_interval _ _ _ _ (missing_moment_slope_positive A hA g hg hc)

end
end krylov.OneGradient
