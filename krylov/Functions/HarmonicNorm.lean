import krylov.Functions.HarmonicCubic

/-!
Article: main_krylov, thm:H, exact harmonic tensor norm.
Use: give an actual unit vector attaining the strict canonical tensor budget,
then connect the exact harmonic diagonal norm to the genuine mixed Banach
estimate. Source: the triple-angle identities at pi/12 and orthonormality.
-/

namespace krylov.Functions
noncomputable section
open InnerProductSpace krylov.Tensor
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A genuine unit vector in the canonical harmonic plane attains its exact
budget 2a. Article: main_krylov, thm:H, harmonic lower realization. -/
theorem canonicalHarmonic_attains (e h : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) (a : ℝ) :
    ∃ z : E, ‖z‖=1 ∧ (canonicalHarmonicTensor e h a).form z z z=2*a := by
  let θ := Real.pi/12
  let c := Real.cos θ
  let s := Real.sin θ
  let z := c • e+s • h
  have hee : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he,one_pow]
  have hhh : inner ℝ h h=1 := by rw [real_inner_self_eq_norm_sq,hh,one_pow]
  have hhe : inner ℝ h e=0 := (real_inner_comm e h).trans heh
  have hcircle : c^2+s^2=1 := by dsimp only [c,s];nlinarith [Real.sin_sq_add_cos_sq θ]
  have hcz : canonicalBilinear e z=c := by
    change inner ℝ e z=c
    simp only [z,inner_add_right,inner_smul_right,hee,heh,mul_one,mul_zero,add_zero]
  have hsz : canonicalBilinear h z=s := by
    change inner ℝ h z=s
    simp only [z,inner_add_right,inner_smul_right,hhh,hhe,mul_one,mul_zero,zero_add]
  have hz : ‖z‖=1 := by
    have hnorm : ‖z‖^2=1 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [z,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
        conj_trivial,hee,hhh,heh,hhe]
      nlinarith
    nlinarith [norm_nonneg z]
  have hθ : 3*θ=Real.pi/4 := by dsimp [θ];ring
  have hc3 := Real.cos_three_mul θ
  have hs3 := Real.sin_three_mul θ
  rw [hθ,Real.cos_pi_div_four] at hc3
  rw [hθ,Real.sin_pi_div_four] at hs3
  change Real.sqrt 2/2=4*c^3-3*c at hc3
  change Real.sqrt 2/2=3*s-4*s^3 at hs3
  have hcc : c*(c^2+s^2)=c := by rw [hcircle,mul_one]
  have hss : s*(c^2+s^2)=s := by rw [hcircle,mul_one]
  have hsum : c^3+3*c^2*s-3*c*s^2-s^3=Real.sqrt 2 := by nlinarith
  refine ⟨z,hz,?_⟩
  change (harmonicTensor (canonicalBilinear e) (canonicalBilinear h) a).form z z z=2*a
  rw [harmonicTensor_diagonal,hcz,hsz,hsum]
  exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr (by norm_num)).ne'

/-- The actual harmonic tensor has precisely its printed sharp diagonal norm:
all unit directions obey the bound and one true unit direction attains it.
Article: main_krylov, thm:H. -/
theorem canonicalHarmonic_exact_budget (e h : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) {a : ℝ} (ha : 0≤a) :
    (∀ x : E, ‖x‖=1 → |(canonicalHarmonicTensor e h a).form x x x|≤2*a) ∧
      ∃ z : E, ‖z‖=1 ∧ |(canonicalHarmonicTensor e h a).form z z z|=2*a := by
  refine ⟨canonicalHarmonicTensor_bound e h he hh heh ha,?_⟩
  obtain ⟨z,hz,heq⟩ := canonicalHarmonic_attains e h he hh heh a
  exact ⟨z,hz,by rw [heq,abs_of_nonneg (by positivity)]⟩

/-- The printed exact harmonic budget also bounds all genuine mixed slots.
Article: main_krylov, thm:H and thm:Hp, Banach's norm identity. -/
theorem canonicalHarmonic_mixed_bound [FiniteDimensional ℝ E]
    (e h : E) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    {a : ℝ} (ha : 0≤a) (u v w : E) :
    |(canonicalHarmonicTensor e h a).form u v w|≤2*a*‖u‖*‖v‖*‖w‖ :=
  cubic_diagonal_bound _ _ (canonicalHarmonicTensor_bound e h he hh heh ha) u v w

end
end krylov.Functions
