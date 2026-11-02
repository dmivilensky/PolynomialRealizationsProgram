import krylov.LinearAlgebra.PlanarWitness
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), actual arbitrary-query adversarial plane.
Use: construct a genuine unit normal to the real second query, including
the zero query, without assuming a policy limit or CG consistency.
Source: exact complete real orthonormal coordinates and zero-safe
normalization in an actual two-dimensional physical plane.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.LinearAlgebra
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual query in a genuine complete orthonormal plane has a
true orthogonal unit normal and a unit axis along its exact direction.
The zero query is included with the same exact length decomposition.
Use: original hidden matrices annihilate the actual second query even
for degenerate, unbounded or discontinuously varying competing policies.
Article: main_krylov, thm:local(c), genuine arbitrary-query frame.
Proof: normalize the real nonzero query and rotate its actual two
orthonormal coordinates by a quarter turn. Completeness gives the true
unit norm and orthogonality. At zero use the original complete frame. -/
theorem twoQuery_orthonormal_plane (e0 h0 : E) (he0 : ‖e0‖=1) (hh0 : ‖h0‖=1)
    (heh0 : inner ℝ e0 h0=0)
    (hfull : ∀ v : E,(inner ℝ e0 v) • e0+(inner ℝ h0 v) • h0=v) (v : E) :
    ∃ e h : E,‖e‖=1 ∧ ‖h‖=1 ∧ inner ℝ e h=0 ∧ v=‖v‖ • h := by
  by_cases hv : v=0
  · exact ⟨e0,h0,he0,hh0,heh0,by rw [hv,norm_zero,zero_smul]⟩
  let h := ‖v‖⁻¹ • v
  let a := inner ℝ e0 h
  let b := inner ℝ h0 h
  let e := b • e0-a • h0
  have hh : ‖h‖=1 := by
    rw [show h=‖v‖⁻¹ • v from rfl,norm_smul,Real.norm_of_nonneg (by positivity),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hee : inner ℝ e0 e0=1 := by rw [real_inner_self_eq_norm_sq,he0,one_pow]
  have hhe : inner ℝ h0 e0=0 := by rw [real_inner_comm,heh0]
  have hhh : inner ℝ h0 h0=1 := by rw [real_inner_self_eq_norm_sq,hh0,one_pow]
  have hab : a^2+b^2=1 := by
    have hnorm := congrArg (fun x : E => ‖x‖^2) (hfull h)
    rw [norm_add_sq_real] at hnorm
    simp only [norm_smul,Real.norm_eq_abs,sq_abs,he0,hh0,hh,mul_one,one_pow,
      real_inner_smul_left,real_inner_smul_right,heh0,mul_zero,add_zero] at hnorm
    exact hnorm
  have he : ‖e‖=1 := by
    have he2 : ‖e‖^2=1 := by
      dsimp only [e]
      rw [norm_sub_sq_real]
      simp only [norm_smul,Real.norm_eq_abs,sq_abs,he0,hh0,mul_one,
        real_inner_smul_left,real_inner_smul_right,heh0,mul_zero,sub_zero]
      nlinarith [hab]
    nlinarith [norm_nonneg e]
  have heh : inner ℝ e h=0 := by
    change inner ℝ (b • e0-a • h0) h=0
    rw [inner_sub_left,real_inner_smul_left,real_inner_smul_left]
    change b*a-a*b=0
    ring
  refine ⟨e,h,he,hh,heh,?_⟩
  dsimp only [h]
  rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul]

end
end krylov.OneGradient
