import krylov.Functions.HarmonicNorm
import krylov.LinearAlgebra.PlanarWitness

/-!
Article: main_krylov, thm:H, the real harmonic Hessian slices.
Use: evaluate the genuine tensor's actual Riesz Hessian slice as the printed
rank-two matrix and prove its exact spectral norm, including zero slices.
Source: actual harmonic coefficients, orthonormality and Bessel.
-/

namespace krylov.Tensor
noncomputable section
open Matrix krylov.Functions krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A true planar reflection block has exactly its Euclidean coefficient norm.
Article: main_krylov, thm:H, harmonic increment budgets. -/
theorem planar_reflection_norm (e h : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0) (s t : ℝ) :
    ‖planarMatrix e h s t (-s)‖ = Real.sqrt (s^2+t^2) := by
  rw [Matrix.cstar_norm_def]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro w
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity), planarMatrix_action,
      planar_coordinates_norm_sq e h he hh heh]
    have hb := mul_le_mul_of_nonneg_left (two_unit_bessel e h w he hh heh)
      (by positivity : 0 ≤ s^2+t^2)
    nlinarith only [hb]
  · have hb := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (planarMatrix e h s t (-s))).le_opNorm e
    rw [he, mul_one] at hb
    have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
    have hhe : inner ℝ h e = 0 := by rw [real_inner_comm]; exact heh
    have hn : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (planarMatrix e h s t (-s)) e‖ =
        Real.sqrt (s^2+t^2) := by
      rw [planarMatrix_action]
      simp only [hee, hhe, mul_one, mul_zero, add_zero]
      apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [planar_coordinates_norm_sq e h he hh heh, Real.sq_sqrt (by positivity)]
    rwa [hn] at hb

/-- The genuine harmonic third derivative is exactly the actual rank-two
slice printed in the article, as an operator on the whole ambient space.
Article: main_krylov, thm:H. -/
theorem canonicalHarmonic_slice (e h : EuclideanSpace ℝ (Fin n)) (a : ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    canonicalVariation (canonicalHarmonicTensor e h a) v =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (planarMatrix e h ((2*a/Real.sqrt 2)*(inner ℝ e v+inner ℝ h v))
          ((2*a/Real.sqrt 2)*(inner ℝ e v-inner ℝ h v))
          (-((2*a/Real.sqrt 2)*(inner ℝ e v+inner ℝ h v)))) := by
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℝ
  intro z
  rw [canonicalVariation_pair, planarMatrix_action]
  change (harmonicForm (canonicalBilinear e) (canonicalBilinear h) a) v z w = _
  rw [harmonicForm_apply]
  simp only [show canonicalBilinear e = innerSL ℝ e from rfl,
    show canonicalBilinear h = innerSL ℝ h from rfl, innerSL_apply_apply,
    inner_add_right, inner_smul_right]
  rw [real_inner_comm z e, real_inner_comm z h]
  ring

/-- The genuine harmonic slice spectral energy is precisely four a² times
the squared actual planar input length. Article: main_krylov, thm:H. -/
theorem canonicalHarmonic_slice_norm_sq (e h : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0) (a : ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖canonicalVariation (canonicalHarmonicTensor e h a) v‖^2 =
      4*a^2*((inner ℝ e v)^2+(inner ℝ h v)^2) := by
  rw [canonicalHarmonic_slice, ← Matrix.cstar_norm_def,
    planar_reflection_norm e h he hh heh, Real.sq_sqrt (by positivity)]
  have hs : (Real.sqrt (2 : ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hz : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp
  rw [hs]
  ring

end
end krylov.Tensor
