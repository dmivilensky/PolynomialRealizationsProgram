import krylov.Functions.ValueFibreTranscript
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Article: main_krylov, prop:Fcycle(iii), localization for unrestricted common outputs.
Use: prove that the homogeneous quadratic gradient of the exact hidden cubic
has no nonzero planar zero and has a genuine positive quadratic lower bound.
Source: Appendix G, the exact data fibre; compactness of the unit sphere.
-/

namespace krylov.Functions
noncomputable section
open Set NormedSpace

/-- The genuine coordinate gradient of the homogeneous part of the cubic data-fibre difference.
Article: main_krylov, prop:Fcycle(iii). -/
def valueFibreHomogeneousGradient (d r : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (d / 2 * z.2 * (z.2 - 2 * r * z.1), d / 2 * z.1 * (2 * z.2 - r * z.1))

/-- For a nontrivial chord and positive reference ratio the homogeneous gradient vanishes only at zero.
Article: main_krylov, prop:Fcycle(iii), the assertion for every nonzero planar direction.
Proof: the first coefficient forces Y=0 or Y=2rX; either alternative makes the second force X=0. -/
theorem valueFibreHomogeneousGradient_eq_zero_iff (d r : ℝ) (hd : d ≠ 0) (hr : r ≠ 0)
    (z : ℝ × ℝ) : valueFibreHomogeneousGradient d r z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h₁ : d / 2 * z.2 * (z.2 - 2 * r * z.1) = 0 := congrArg Prod.fst h
    have h₂ : d / 2 * z.1 * (2 * z.2 - r * z.1) = 0 := congrArg Prod.snd h
    have hd₂ : d / 2 ≠ 0 := div_ne_zero hd (by norm_num)
    have hy : z.2 * (z.2 - 2 * r * z.1) = 0 := by
      apply (mul_eq_zero.mp (show d / 2 * (z.2 * (z.2 - 2 * r * z.1)) = 0 by
        nlinarith only [h₁])).resolve_left hd₂
    have hx : z.1 * (2 * z.2 - r * z.1) = 0 := by
      apply (mul_eq_zero.mp (show d / 2 * (z.1 * (2 * z.2 - r * z.1)) = 0 by
        nlinarith only [h₂])).resolve_left hd₂
    rcases mul_eq_zero.mp hy with hy | hy
    · have hx' : z.1 = 0 := by
        rcases mul_eq_zero.mp hx with hx | hx
        · exact hx
        · have hmul : r * z.1 = 0 := by linarith only [hx, hy]
          exact (mul_eq_zero.mp hmul).resolve_left hr
      exact Prod.ext hx' hy
    · have hx' : z.1 = 0 := by
        rcases mul_eq_zero.mp hx with hx | hx
        · exact hx
        · have hmul : r * z.1 = 0 := by linarith only [hx, hy]
          exact (mul_eq_zero.mp hmul).resolve_left hr
      have hy' : z.2 = 0 := by simp only [hx', mul_zero, sub_zero] at hy; exact hy
      exact Prod.ext hx' hy'
  · intro hz
    simp [hz, valueFibreHomogeneousGradient]

/-- The actual homogeneous gradient has degree exactly two under real scaling.
Article: main_krylov, prop:Fcycle(iii), quadratic-gradient scaling. -/
theorem valueFibreHomogeneousGradient_smul (d r q : ℝ) (z : ℝ × ℝ) :
    valueFibreHomogeneousGradient d r (q • z) = q ^ 2 • valueFibreHomogeneousGradient d r z := by
  ext <;> simp only [valueFibreHomogeneousGradient, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- A nontrivial exact fibre has a uniform positive quadratic gradient bound in the plane.
Article: main_krylov, prop:Fcycle(iii), localization for arbitrary common outputs.
Proof: the genuine quadratic gradient is continuous and nonzero on the compact unit sphere;
its positive minimum extends to every point by exact degree-two homogeneity. -/
theorem valueFibreHomogeneousGradient_coercive (d r : ℝ) (hd : d ≠ 0) (hr : r ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℝ × ℝ, c * ‖z‖ ^ 2 ≤ ‖valueFibreHomogeneousGradient d r z‖ := by
  have hc : Continuous (fun z : ℝ × ℝ => ‖valueFibreHomogeneousGradient d r z‖) := by
    unfold valueFibreHomogeneousGradient
    fun_prop
  have hne : (Metric.sphere (0 : ℝ × ℝ) 1).Nonempty := by
    refine ⟨(1, 0), ?_⟩
    simp [Prod.norm_def]
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere (0 : ℝ × ℝ) 1).exists_isMinOn hne hc.continuousOn
  have hn₀ : ‖z₀‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz₀
  have hz₀ne : z₀ ≠ 0 := by intro h; simp [h] at hn₀
  have hG₀ne : valueFibreHomogeneousGradient d r z₀ ≠ 0 := by
    intro h
    exact hz₀ne ((valueFibreHomogeneousGradient_eq_zero_iff d r hd hr z₀).mp h)
  refine ⟨‖valueFibreHomogeneousGradient d r z₀‖, norm_pos_iff.mpr hG₀ne, ?_⟩
  intro z
  by_cases hz : z = 0
  · simp [hz, valueFibreHomogeneousGradient]
  have hnorm : ‖normalize z‖ = 1 := norm_normalize hz
  have hmin' := hmin (a := normalize z) (by simpa only [Metric.mem_sphere, dist_zero_right] using hnorm)
  have he : valueFibreHomogeneousGradient d r z =
      ‖z‖ ^ 2 • valueFibreHomogeneousGradient d r (normalize z) := by
    conv_lhs => rw [← norm_smul_normalize z]
    exact valueFibreHomogeneousGradient_smul d r ‖z‖ (normalize z)
  rw [he, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
  exact (mul_le_mul_of_nonneg_right hmin' (sq_nonneg _)).trans_eq (mul_comm _ _)

end
end krylov.Functions
