import krylov.XR.ConjugateVariation
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
Article: main_krylov, prop:status, equality case of the flag condition.
Use: prove that unit flag conditioning characterizes genuinely conjugate
windows, rather than merely bounding that special case in one direction.
Source: a contractive idempotent on a real Hilbert space is an orthogonal
projection; proved directly by minimizing its true squared norm on a
range/kernel line.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- A contractive projection pairs its actual range orthogonally to its
actual kernel. Article: main_krylov, prop:status. -/
theorem contractive_idempotent_range_kernel {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (P : E →L[ℝ] E) (hP : ‖P‖≤1)
    (x y : E) (hx : P x=x) (hy : P y=0) : inner ℝ x y=0 := by
  have hunit (z : E) (hz : P z=0) (hnz : ‖z‖=1) : inner ℝ x z=0 := by
    let t := -inner ℝ x z
    have he : P (x+t • z)=x := by rw [map_add,map_smul,hx,hz,smul_zero,add_zero]
    have hn := (P.le_opNorm (x+t • z)).trans
      (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
    rw [he,one_mul] at hn
    have hs := (sq_le_sq₀ (norm_nonneg x) (norm_nonneg (x+t • z))).mpr hn
    rw [norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,
      sq_abs,hnz,one_pow,mul_one] at hs
    dsimp only [t] at hs
    nlinarith only [hs,sq_nonneg (inner ℝ x z)]
  by_cases hzero : y=0
  · simp only [hzero,inner_zero_right]
  · have hp := norm_pos_iff.mpr hzero
    have hh := hunit (‖y‖⁻¹ • y) (by rw [map_smul,hy,smul_zero]) (by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le),inv_mul_cancel₀ hp.ne'])
    rw [real_inner_smul_right] at hh
    exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero hp.ne')

/-- Every genuine contractive idempotent is symmetric, with no
orthogonality hypothesis supplied. Article: main_krylov, prop:status. -/
theorem contractive_idempotent_symmetric {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (P : E →L[ℝ] E) (hP : ‖P‖≤1)
    (hid : ∀ x,P (P x)=P x) : P.toLinearMap.IsSymmetric := by
  intro x y
  have hx := contractive_idempotent_range_kernel P hP (P x) (y-P y) (hid x)
    (by rw [map_sub,hid,sub_self])
  have hy := contractive_idempotent_range_kernel P hP (P y) (x-P x) (hid y)
    (by rw [map_sub,hid,sub_self])
  rw [inner_sub_right] at hx hy
  change inner ℝ (P x) y=inner ℝ x (P y)
  calc
    _ = inner ℝ (P x) (P y) := sub_eq_zero.mp hx
    _ = inner ℝ (P y) (P x) := real_inner_comm _ _
    _ = inner ℝ (P y) x := (sub_eq_zero.mp hy).symm
    _ = _ := real_inner_comm _ _

/-- Matrix form of the standard contractive-idempotent characterization.
Article: main_krylov, prop:status. -/
theorem contractive_idempotent_isSymm {p : ℕ} (P : Matrix (Fin p) (Fin p) ℝ)
    (hP : ‖P‖≤1) (hid : P*P=P) : P.IsSymm := by
  have hn : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P‖≤1 := by
    rwa [Matrix.l2_opNorm_toEuclideanCLM]
  have hh := contractive_idempotent_symmetric (Matrix.toEuclideanCLM (𝕜 := ℝ) P) hn (fun x=>by
    rw [←mul_apply_eq_comp,←map_mul,hid])
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mp hh).isSymm

end
end krylov.XR
