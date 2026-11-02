import krylov.LinearAlgebra.RankOneNorm
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
set_option autoImplicit false
/-!
Article: main_krylov, apE:Pi, exact norm of an orthogonal block and one oblique row.
Use: compute the real projector norm from its boundary row without a
conditioning estimate or a division by a possibly zero trial amplitude.
Source: mathlib orthogonal projection, Pythagoras and Cauchy--Schwarz.
-/

namespace krylov.LinearAlgebra
noncomputable section
open scoped InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- An orthogonal identity block plus one perpendicular unit output row has
norm exactly the norm of its input row whenever that row has norm at least one.
Use: the original bidiagonal old-flag projector has precisely this block form.
Article: main_krylov, apE:Pi, norm(Pi_l)=norm(r_l).
Proof: Pythagoras splits the actual output and input into their orthogonal
blocks. Cauchy--Schwarz bounds the row, with its norm at least one dominating
the identity block. Applying the operator to the row attains the bound. -/
theorem projection_row_norm (K : Submodule ℝ V) [K.HasOrthogonalProjection]
    (u r : V) (hu : ‖u‖=1) (huK : u∈Kᗮ) (hrK : r∈Kᗮ) (hr : 1≤‖r‖) :
    ‖K.starProjection+InnerProductSpace.rankOne ℝ u r‖=‖r‖ := by
  let T := K.starProjection+InnerProductSpace.rankOne ℝ u r
  have hp0 (x : V) : inner ℝ (K.starProjection x) u=0 :=
    (Submodule.mem_orthogonal K u).mp huK _ (K.starProjection_apply_mem x)
  have hr0 (x : V) : inner ℝ r (K.starProjection x)=0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal K r).mp hrK _ (K.starProjection_apply_mem x)
  have hupper : ‖T‖≤‖r‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg r)
    intro x
    have hout : ‖T x‖^2=‖K.starProjection x‖^2+(inner ℝ r x)^2 := by
      change ‖K.starProjection x+inner ℝ r x • u‖^2=_
      have hh := norm_add_sq_eq_norm_sq_add_norm_sq_real
        (x := K.starProjection x) (y := inner ℝ r x • u)
        (by rw [real_inner_smul_right,hp0,mul_zero])
      simpa only [← sq,norm_smul,Real.norm_eq_abs,hu,mul_one,sq_abs] using hh
    have hin : ‖x‖^2=‖K.starProjection x‖^2+‖x-K.starProjection x‖^2 := by
      have horth : inner ℝ (K.starProjection x) (x-K.starProjection x)=0 :=
        (Submodule.mem_orthogonal K _).mp (K.sub_starProjection_mem_orthogonal x) _
          (K.starProjection_apply_mem x)
      have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (K.starProjection x) (x-K.starProjection x) horth
      rw [add_sub_cancel] at hh
      simpa only [sq] using hh
    have hcs : |inner ℝ r x|≤‖r‖*‖x-K.starProjection x‖ := by
      have h := abs_real_inner_le_norm r (x-K.starProjection x)
      simpa only [inner_sub_right,hr0,sub_zero] using h
    have hcssq : (inner ℝ r x)^2≤‖r‖^2*‖x-K.starProjection x‖^2 := by
      have h := sq_le_sq₀ (abs_nonneg (inner ℝ r x))
        (mul_nonneg (norm_nonneg r) (norm_nonneg (x-K.starProjection x))) |>.mpr hcs
      simpa only [sq_abs,mul_pow] using h
    have hscale : ‖K.starProjection x‖^2≤‖r‖^2*‖K.starProjection x‖^2 := by
      have hsq : 1≤‖r‖^2 := by nlinarith [norm_nonneg r]
      nlinarith [sq_nonneg ‖K.starProjection x‖]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg r) (norm_nonneg x))).mp
    rw [hout,mul_pow,hin]
    nlinarith
  have hPr : K.starProjection r=0 := by
    rw [Submodule.starProjection_apply,
      K.orthogonalProjectionOnto_apply_of_mem_orthogonal hrK,Submodule.coe_zero]
  have hTr : T r=‖r‖^2 • u := by
    change K.starProjection r+inner ℝ r r • u=_
    rw [hPr,zero_add,real_inner_self_eq_norm_sq]
  have hlow := T.le_opNorm r
  rw [hTr,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖r‖),hu,mul_one] at hlow
  have hR : 0<‖r‖ := lt_of_lt_of_le zero_lt_one hr
  have hlower : ‖r‖≤‖T‖ := by nlinarith
  exact le_antisymm hupper hlower

end
end krylov.LinearAlgebra
