import krylov.LinearAlgebra.SymmetricBall
import krylov.LinearAlgebra.InformationRadius
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(a), sharp fresh-defect geometry.
Use: obtain the actual symmetric uncertainty witness in every nonzero
window, including zero steps and zero uncertainty budgets.
Source: the previously proved self-adjoint image-ball theorem (Rump03,
Lemma 5.1), whose witness is an orthogonal Householder reflection.
-/

namespace krylov.LinearAlgebra
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The projected symmetric image ball has its full, attained radius on every
nonzero actual window.
Use: the fresh-defect lower bound uses a real symmetric operator witness.
Article: main_krylov, apH:dcs2(a), sharp projected fresh radius.
Proof: normalize a genuine nonzero window vector. The proved reflection
construction maps the actual step to the full budget times its norm in
that window direction. Contractivity of the true projection gives the upper bound. -/
theorem projected_symmetric_image_sharp (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (hK : K≠⊥) (s : E) (omega : ℝ) (homega : 0≤omega) :
    IsGreatest {z : ℝ | ∃ T : E →L[ℝ] E,IsSelfAdjoint T ∧ ‖T‖≤omega ∧
      z=‖K.starProjection (T s)‖} (omega*‖s‖) := by
  obtain ⟨e,he,hne⟩ := K.ne_bot_iff.mp hK
  let u := ‖e‖⁻¹ • e
  have huK : u∈K := K.smul_mem _ he
  have hu : ‖u‖=1 := by
    change ‖‖e‖⁻¹ • e‖=1
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]
  have hn : ‖(omega*‖s‖) • u‖=omega*‖s‖ := by
    rw [norm_smul,Real.norm_of_nonneg (mul_nonneg homega (norm_nonneg _)),hu,mul_one]
  obtain ⟨T,hTs,hT,himage⟩ := exists_selfAdjoint_image s ((omega*‖s‖) • u) homega hn.le
  constructor
  · refine ⟨T,hTs,hT,?_⟩
    rw [himage,K.starProjection_eq_self_iff.mpr (K.smul_mem _ huK),hn]
  · rintro z ⟨T,_,hT,rfl⟩
    exact (K.norm_starProjection_apply_le _).trans ((T.le_opNorm s).trans
      (mul_le_mul_of_nonneg_right hT (norm_nonneg _)))

/-- One of the two opposite fresh scenarios retains at least the entire
attained projected uncertainty radius after every common incoming residual.
Use: no assumption on a method's incoming residual or regularity is needed.
Article: main_krylov, apH:dcs2(a), max of opposite fresh defects.
Proof: choose the genuine reflection witness above. The proved parallelogram
lower bound for the two opposite scenarios cannot be reduced by a common shift. -/
theorem projected_fresh_two_scenarios (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (hK : K≠⊥) (s c : E) (omega : ℝ) (homega : 0≤omega) :
    ∃ T : E →L[ℝ] E,IsSelfAdjoint T ∧ ‖T‖≤omega ∧
      ‖K.starProjection (T s)‖=omega*‖s‖ ∧
      omega*‖s‖≤max ‖K.starProjection (c+T s)‖ ‖K.starProjection (c-T s)‖ := by
  obtain ⟨T,hTs,hT,hvalue⟩ := (projected_symmetric_image_sharp K hK s omega homega).1
  refine ⟨T,hTs,hT,hvalue.symm,?_⟩
  have hs := two_scenario_sq (K.starProjection c) (K.starProjection (T s))
  rw [hvalue.symm] at hs
  rw [map_add,map_sub]
  let M := max ‖K.starProjection c+K.starProjection (T s)‖ ‖K.starProjection c-K.starProjection (T s)‖
  have hM : 0≤M := (norm_nonneg _).trans (le_max_left _ _)
  have hp := (sq_le_sq₀ (norm_nonneg _) hM).mpr (le_max_left
    ‖K.starProjection c+K.starProjection (T s)‖ ‖K.starProjection c-K.starProjection (T s)‖)
  have hm := (sq_le_sq₀ (norm_nonneg _) hM).mpr (le_max_right
    ‖K.starProjection c+K.starProjection (T s)‖ ‖K.starProjection c-K.starProjection (T s)‖)
  have hb := hs.trans (max_le hp hm)
  change omega*‖s‖≤M
  nlinarith [sq_nonneg ‖K.starProjection c‖,mul_nonneg homega (norm_nonneg s)]

end
end krylov.LinearAlgebra
