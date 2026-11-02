import jacobi.GelfandLevitan.TransformationFactorization
import jacobi.GelfandLevitan.TransformationCompactness

/-!
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
The actual transformation is invertible. Compactness and the proved
factorization give this directly by the community Fredholm alternative,
without a separate general theorem about Volterra inverses. Every
operator in the argument is the original GL operator on the physical
half interval.
Use: keeps the exact noncommutative factorization algebra from repeatedly unfolding the full underlying L2 construction during typeclass search.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Module jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local irreducible] transformationOperator kernelOperator
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Cache the original bounded-endomorphism normed ring instance.
Use: keeps the exact noncommutative factorization algebra from repeatedly unfolding the full underlying L2 construction during typeclass search.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
local instance : NormedRing (halfSubspace →L[ℝ] halfSubspace) := inferInstance

/-- The actual transformation adjoint is the identity plus the true Volterra adjoint.
Use: applies the compact Fredholm alternative to the actual identity perturbation in transformationPlus_adjoint_isUnit.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: the community Hilbert adjoint preserves addition and fixes the identity operator. -/
theorem transformationPlus_adjoint_operator (a : ℝ) (ha : -1<a) :
    (transformationPlus a ha).adjoint=1+(transformationOperator a ha).adjoint := by
  rw [transformationPlus,map_add,ContinuousLinearMap.adjoint_id]
  rfl

/-- The actual Volterra adjoint is compact, as a consequence of the original factorization and the proved source and Volterra compactness.
Use: the compact Fredholm alternative proves the true adjoint transformation invertible.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: expand the exact GL factorization to write K* as minus the sum of K, K*K*, and (I+K)*F*(I+K)*. Each term has an already proved compact factor and bounded remaining factors. -/
theorem transformationOperator_adjoint_compact (a : ℝ) (ha : -1<a) :
    IsCompactOperator (transformationOperator a ha).adjoint := by
  -- The factorization supplies compactness here, so no unproved Schauder-adjoint lemma is needed.
  let K := transformationOperator a ha
  let S := transformationPlus a ha
  let F := kernelOperator a ha
  have hSS : S*S.adjoint=1+K+K.adjoint+K*K.adjoint := by
    rw [transformationPlus_adjoint_operator]
    change (1+K)*(1+K.adjoint)=1+K+K.adjoint+K*K.adjoint
    noncomm_ring
  have h := transformation_factorization a ha
  change S*(1+F)*S.adjoint=1 at h
  rw [mul_add,mul_one,add_mul,hSS] at h
  have hz : K.adjoint+(K+K*K.adjoint+S*F*S.adjoint)=0 := by
    calc
      _ = (1+K+K.adjoint+K*K.adjoint+S*F*S.adjoint)-1 := by abel_nf
      _ = 0 := by rw [h,sub_self]
  have he : K.adjoint= -(K+K*K.adjoint+S*F*S.adjoint) := eq_neg_of_add_eq_zero_left hz
  rw [show (transformationOperator a ha).adjoint=K.adjoint from rfl,he]
  have hK : IsCompactOperator K := transformationOperator_compact a ha
  have hF : IsCompactOperator F := kernelOperator_compact a ha
  exact ((hK.add (hK.comp_clm K.adjoint)).add ((hF.comp_clm S.adjoint).clm_comp S)).neg

/-- The adjoint of the original transformation has zero kernel.
Use: excludes minus one from the actual compact Volterra adjoint's eigenvalues in transformationPlus_adjoint_isUnit.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Source: an onto Hilbert operator has injective adjoint.
Proof: every vector has an actual preimage under the proved onto transformation. Testing a zero adjoint image against the preimage of that same vector makes its genuine norm square zero. -/
theorem transformationPlus_adjoint_injective (a : ℝ) (ha : -1<a) :
    Function.Injective (transformationPlus a ha).adjoint := by
  apply (transformationPlus a ha).adjoint.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change (transformationPlus a ha).adjoint v=0 at hv
  obtain ⟨w,hw⟩ := transformationPlus_surjective a ha v
  have h := (transformationPlus a ha).adjoint_inner_left w v
  rw [hv,inner_zero_left,hw] at h
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp h.symm

/-- The actual original adjoint transformation is a unit in the bounded Hilbert operator algebra.
Use: its star gives the genuine two-sided inverse property for the original transformation, needed by the two-bases argument.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Source: compact Fredholm alternative, mathlib.
Proof: minus one cannot be an eigenvalue of the actual compact Volterra adjoint, since that would give a nonzero null vector of the proved injective adjoint transformation. The community Fredholm alternative gives a genuine bounded inverse. -/
theorem transformationPlus_adjoint_isUnit (a : ℝ) (ha : -1<a) :
    IsUnit (transformationPlus a ha).adjoint := by
  -- Both the compact operator and the excluded nullspace are the actual original objects.
  have hne : ¬ Module.End.HasEigenvalue (transformationOperator a ha).adjoint.toLinearMap (-1:ℝ) := by
    intro he
    obtain ⟨v,hv⟩ := he.exists_hasEigenvector
    have hz : (transformationPlus a ha).adjoint v=0 := by
      rw [transformationPlus_adjoint_operator]
      change v+(transformationOperator a ha).adjoint v=0
      have he : (transformationOperator a ha).adjoint v= -v := by
        have hh := hv.apply_eq_smul
        simp only [neg_one_smul] at hh
        convert! hh using 1
      rw [he,add_neg_cancel]
    exact hv.2 ((transformationPlus_adjoint_injective a ha) (hz.trans (map_zero _).symm))
  rcases (transformationOperator_adjoint_compact a ha).hasEigenvalue_or_mem_resolventSet
      (by norm_num : (-1:ℝ)≠0) with h|h
  · exact False.elim (hne h)
  · have hu : IsUnit ((-1:halfSubspace →L[ℝ] halfSubspace)-(transformationOperator a ha).adjoint) := by
      simpa only [map_neg,map_one] using (spectrum.mem_resolventSet_iff.mp h)
    have he : (-1:halfSubspace →L[ℝ] halfSubspace)-(transformationOperator a ha).adjoint=
        -(transformationPlus a ha).adjoint := by
      rw [transformationPlus_adjoint_operator]
      abel_nf
    rw [he] at hu
    simpa only [neg_neg] using hu.neg

/-- The identity plus the actual original Volterra operator has a genuine bounded two-sided inverse.
Use: the transformed parity frame and the compactly perturbed reference systems give the two actual orthonormal bases.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: the original adjoint transformation is a proved unit; its Hilbert star is the original transformation, and star preserves units. -/
theorem transformationPlus_isUnit (a : ℝ) (ha : -1<a) : IsUnit (transformationPlus a ha) := by
  have h := (transformationPlus_adjoint_isUnit a ha).star
  simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint] using h

end
end jacobi.GelfandLevitan
