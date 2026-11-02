import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic

set_option autoImplicit false
/-!
Article: main_krylov, s3:thm:cf, actual old-plane perpendicular unit witness.
Use: construct a genuine unit vector in a true orthonormal plane that
is orthogonal to the real maximizing common tilt.
Source: elementary genuine real inner-product coordinates and actual
normalization of a proved nonzero physical vector.
-/

namespace krylov.LinearAlgebra
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every genuine orthonormal pair spans an actual unit vector orthogonal to any real target vector.
Use: Every genuine orthonormal pair spans an actual unit vector orthogonal to any real target vector.
Article: main_krylov, s3:thm:cf, actual old-plane perpendicular unit witness.
Proof: If the target annihilates the real plane, choose its genuine first unit vector; otherwise normalize the actual nonzero perpendicular two-coordinate combination. -/
theorem orthonormal_pair_perpendicular_unit (u v z : E) (hu : ‖u‖=1) (hv : ‖v‖=1) (huv : inner ℝ u v=0) :
    ∃ x : E, ‖x‖=1 ∧ x∈Submodule.span ℝ ({u,v} : Set E) ∧ inner ℝ x z=0 := by
  have huu : inner ℝ u u=1 := by rw [real_inner_self_eq_norm_sq,hu,one_pow]
  have hvv : inner ℝ v v=1 := by rw [real_inner_self_eq_norm_sq,hv,one_pow]
  have hvu : inner ℝ v u=0 := by rw [real_inner_comm];exact huv
  -- Separate the genuine zero plane projection before normalizing the actual nonzero perpendicular combination.
  by_cases hz : inner ℝ u z=0 ∧ inner ℝ v z=0
  · exact ⟨u,hu,Submodule.subset_span (Set.mem_insert _ _),hz.1⟩
  · let w := inner ℝ v z • u-inner ℝ u z • v
    have hw : w≠0 := by
      intro he
      have h₁ := congrArg (fun a => inner ℝ u a) he
      have h₂ := congrArg (fun a => inner ℝ v a) he
      dsimp only [w] at h₁ h₂
      simp only [inner_sub_right,real_inner_smul_right,huu,hvv,huv,hvu,inner_zero_right,
        mul_one,mul_zero,sub_zero,zero_sub] at h₁ h₂
      exact hz ⟨neg_eq_zero.mp h₂,h₁⟩
    have hwz : inner ℝ w z=0 := by
      dsimp only [w]
      rw [inner_sub_left,real_inner_smul_left,real_inner_smul_left]
      ring
    refine ⟨NormedSpace.normalize w,NormedSpace.norm_normalize hw,?_,?_⟩
    · apply Submodule.smul_mem
      apply Submodule.sub_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [NormedSpace.normalize,real_inner_smul_left,hwz,mul_zero]
end
end krylov.LinearAlgebra
