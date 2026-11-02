import krylov.OneGradient.MissingMomentRange
import krylov.OneGradient.CanonicalMoment
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(b), true canonical parameter over all measures.
Use: transfer the exact original all-probability-measure moment interval to
its canonical coordinate, with the actual necessary positive-width qualification.
Source: the proved all-measures moment image, genuine positive Jacobi product
square and normalized real interval coordinates.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference
variable {n : ℕ}

/-- A genuine positive affine moment normalization leaves the original
canonical pivot coordinate exactly unchanged, even at a collapsed interval.
Use: the canonical missing-moment parameter is literally the printed pivot parameter.
Article: main_krylov, s5:moment(b).
Proof: factor the real numerator and denominator and cancel only the true
positive affine coefficient; no endpoint gap is divided out in the proof. -/
theorem positive_affine_canonical (c d lo hi b : ℝ) (hc : 0<c) :
    canonicalPivot (c*lo+d) (c*hi+d) (c*b+d)=canonicalPivot lo hi b := by
  unfold canonicalPivot
  rw [show c*b+d-(c*lo+d)=c*(b-lo) by ring,
    show c*hi+d-(c*lo+d)=c*(hi-lo) by ring,mul_div_mul_left _ _ hc.ne']

/-- Over all genuine original supported probability measures the canonical
first missing moment is free on the whole unit interval precisely in the
nondegenerate physical endpoint regime.
Use: the parameter freedom has the original all-measures quantifiers,
actual attained endpoints and no atomic or representation assumption.
Article: main_krylov, s5:moment(b), positive-gap qualification.
Proof: the true all-measures missing-moment set is the attained positive affine
physical pivot image; canonical normalization cancels its genuine positive
Jacobi coefficient and the actual original pivot interval maps onto [0,1]. -/
theorem canonical_measure_moment_range
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (I : chebyshev1.SpectralInterval)
    (hne : ∃ b : ℝ,(lanczosCompletion A hA g hg hc b-I.mu • 1).PosSemidef ∧
      (I.L • 1-lanczosCompletion A hA g hg hc b).PosSemidef)
    (hgap : spectralLowerPivot A hA g hg hc I.mu<spectralUpperPivot A hA g hg hc I.L) :
    let lo := spectralLowerPivot A hA g hg hc I.mu
    let hi := spectralUpperPivot A hA g hg hc I.L
    let c := ((gradientSpectralData A hA g hg).reconstructed.data.linkProduct n)^2
    let d := gradientMoment A hA g hg (2*n+1)-c*lastJacobiPivot A hA g hg hc
    (fun t : ℝ => canonicalPivot (c*lo+d) (c*hi+d) t) '' missingMomentValues A hA g hg I=Set.Icc 0 1 := by
  dsimp only
  rw [missing_moment_range A hA g hg hc I hne,Set.image_image]
  simp only [positive_affine_canonical _ _ _ _ _ (missing_moment_slope_positive A hA g hg hc)]
  exact canonical_pivot_range hgap

/-- A genuinely collapsed original physical moment interval fixes the
canonical parameter across all admissible supported probability measures.
Use: handle the source boundary case honestly instead of asserting free
variation through a vanishing missing-moment endpoint gap.
Article: main_krylov, s5:moment(b), collapsed boundary qualification.
Proof: the same true positive affine canonical dictionary reduces to the
actual singleton pivot interval, whose totalized coordinate image is {0}. -/
theorem canonical_measure_moment_collapsed
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (I : chebyshev1.SpectralInterval)
    (hne : ∃ b : ℝ,(lanczosCompletion A hA g hg hc b-I.mu • 1).PosSemidef ∧
      (I.L • 1-lanczosCompletion A hA g hg hc b).PosSemidef)
    (hgap : spectralLowerPivot A hA g hg hc I.mu=spectralUpperPivot A hA g hg hc I.L) :
    let lo := spectralLowerPivot A hA g hg hc I.mu
    let hi := spectralUpperPivot A hA g hg hc I.L
    let c := ((gradientSpectralData A hA g hg).reconstructed.data.linkProduct n)^2
    let d := gradientMoment A hA g hg (2*n+1)-c*lastJacobiPivot A hA g hg hc
    (fun t : ℝ => canonicalPivot (c*lo+d) (c*hi+d) t) '' missingMomentValues A hA g hg I=({0} : Set ℝ) := by
  dsimp only
  rw [missing_moment_range A hA g hg hc I hne,Set.image_image]
  simp only [positive_affine_canonical _ _ _ _ _ (missing_moment_slope_positive A hA g hg hc)]
  rw [hgap]
  exact canonical_pivot_collapsed _

end
end krylov.OneGradient
