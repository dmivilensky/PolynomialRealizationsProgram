import jacobi.Trichotomy.PackingInverse
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
Article: jacobi, Proposition C.4.
The genuine centered coordinate and its actual inverse are C1 on their
original open domains. This packages the independently proved genuine
derivatives and continuity; it adds no smoothness premise to the
original spectral profile or to any of the three support regimes.
Use: the source's intrinsic C1 bijection and its genuine Jacobian are available uniformly across all three endpoint support regimes.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set jacobi.Reference

/-- The actual original intrinsic packing coordinate is C1 on the whole physical interior for every alpha>-1.
Use: the source's intrinsic C1 bijection and its genuine Jacobian are available uniformly across all three endpoint support regimes.
Article: jacobi, Proposition C.4.
Proof: its true derivative is the reciprocal original profile, already continuous and positive on the physical interior. Apply the community C1 characterization by continuous first derivative. -/
theorem packingCoordinate_contDiffOn (a : ℝ) (ha : -1<a) :
    ContDiffOn ℝ 1 (packingCoordinate a ha) (Ioo (0:ℝ) 1) := by
  apply (contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn).mpr
  refine ⟨fun t ht => (packingCoordinate_hasDerivAt a ha ht).differentiableAt.differentiableWithinAt,?_⟩
  apply (physicalProfile_reciprocal_continuousOn a ha).congr
  intro t ht
  exact (packingCoordinate_hasDerivAt a ha ht).hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffOn t ht)

/-- The genuine original inverse intrinsic coordinate is C1 throughout its actual open packing interval for every alpha>-1.
Use: the source density is constructed in an actual C1 inverse coordinate on its true positive support, independently of whether its support endpoints are finite or infinite.
Article: jacobi, Proposition C.4.
Proof: the actual inverse derivative is the original continuous profile composed with the genuine continuous inverse. The community continuous-first-derivative characterization gives C1 on the proved open image. -/
theorem packingInverse_contDiffOn (a : ℝ) (ha : -1<a) :
    ContDiffOn ℝ 1 (packingInverse a ha) (packingImage a ha) := by
  have hu : UniqueDiffOn ℝ (packingImage a ha) := (packingImage_open a ha).uniqueDiffOn
  apply (contDiffOn_one_iff_derivWithin hu).mpr
  refine ⟨fun x hx => (packingInverse_hasDerivAt a ha hx).differentiableAt.differentiableWithinAt,?_⟩
  apply ((physicalProfile_continuous a ha).comp_continuousOn (packingInverse_continuousOn a ha)).congr
  intro x hx
  exact (packingInverse_hasDerivAt a ha hx).hasDerivWithinAt.derivWithin (hu x hx)

end
end jacobi.Trichotomy
