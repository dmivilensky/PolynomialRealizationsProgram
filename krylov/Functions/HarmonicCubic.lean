import krylov.Functions.CubicSelfConcordantBall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Article: main_krylov, thm:H, the actual harmonic cubic realization.
Use: construct the printed planar harmonic tensor in any real finite Hilbert
space and certify the actual scalar function as standard self-concordant on
the printed ball. Source: the identity (Re z^3)^2+(Im z^3)^2=norm(z)^6,
Bessel's inequality for two orthonormal vectors, and the proved actual cubic
self-concordance theorem.
-/

namespace krylov.Functions
noncomputable section
open InnerProductSpace krylov.Nonlinear
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Fix the iterated operator-space instance once, avoiding depth-dependent
-- typeclass synthesis through the three curried tensor slots.
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ)

/-- The tensor monomial of three genuine continuous linear coordinates.
Article: main_krylov, thm:H. -/
def coordinateTriple (φ ψ χ : E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  φ.smulRight (ψ.smulRight χ)

/-- The continuous trilinear map of the printed harmonic expansion.
Article: main_krylov, thm:H. -/
def harmonicForm (φ ψ : E →L[ℝ] ℝ) (a : ℝ) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (2*a/Real.sqrt 2) • (coordinateTriple φ φ φ+
    coordinateTriple φ φ ψ+coordinateTriple φ ψ φ+coordinateTriple ψ φ φ-
    coordinateTriple φ ψ ψ-coordinateTriple ψ φ ψ-coordinateTriple ψ ψ φ-
    coordinateTriple ψ ψ ψ)

/-- Exact evaluation of the continuous harmonic form.
Article: main_krylov, thm:H. -/
theorem harmonicForm_apply (φ ψ : E →L[ℝ] ℝ) (a : ℝ) (u v w : E) :
    harmonicForm φ ψ a u v w=(2*a/Real.sqrt 2)*
      (φ u*(φ v*φ w)+φ u*(φ v*ψ w)+φ u*(ψ v*φ w)+ψ u*(φ v*φ w)-
       φ u*(ψ v*ψ w)-ψ u*(φ v*ψ w)-ψ u*(ψ v*φ w)-ψ u*(ψ v*ψ w)) := by
  rfl

/-- The printed harmonic tensor 2a Re(exp(-i*pi/4)(φ+iψ)^3).
Article: main_krylov, thm:H; a=1-delta.
The real coefficient expansion is used, so all tensor symmetry is explicit. -/
def harmonicTensor (φ ψ : E →L[ℝ] ℝ) (a : ℝ) : SymmetricCubic E where
  form := harmonicForm φ ψ a
  swap₁ := by
    intro u v w
    rw [harmonicForm_apply,harmonicForm_apply]
    ring
  swap₂ := by
    intro u v w
    rw [harmonicForm_apply,harmonicForm_apply]
    ring

/-- The actual diagonal tensor polynomial equals the stated harmonic expansion.
Article: main_krylov, thm:H. -/
theorem harmonicTensor_diagonal (φ ψ : E →L[ℝ] ℝ) (a : ℝ) (x : E) :
    (harmonicTensor φ ψ a).form x x x=
      (2*a/Real.sqrt 2)*((φ x)^3+3*(φ x)^2*ψ x-3*φ x*(ψ x)^2-(ψ x)^3) := by
  change harmonicForm φ ψ a x x x=_
  rw [harmonicForm_apply]
  ring

/-- The true harmonic polynomial has its exact circle norm bound.
Article: main_krylov, thm:H, norm of the harmonic tensor.
Proof: the complementary harmonic is an explicit square in the gap. -/
theorem harmonic_polynomial_bound (c s : ℝ) (hcs : c^2+s^2≤1) :
    |c^3+3*c^2*s-3*c*s^2-s^3|≤Real.sqrt 2 := by
  have he : (c^3+3*c^2*s-3*c*s^2-s^3)^2+
      (c^3-3*c^2*s-3*c*s^2+s^3)^2=2*(c^2+s^2)^3 := by ring
  have hcube : (c^2+s^2)^3≤1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by positivity : 0≤c^2+s^2) hcs 3
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hb : (c^3+3*c^2*s-3*c*s^2-s^3)^2≤2 := by
    nlinarith [sq_nonneg (c^3-3*c^2*s-3*c*s^2+s^3)]
  nlinarith [sq_abs (c^3+3*c^2*s-3*c*s^2-s^3),
    abs_nonneg (c^3+3*c^2*s-3*c*s^2-s^3),Real.sqrt_nonneg 2]

/-- The actual harmonic tensor obeys its strict canonical diagonal budget.
Article: main_krylov, thm:H. -/
theorem harmonicTensor_diagonal_bound (φ ψ : E →L[ℝ] ℝ) {a : ℝ} (ha : 0≤a)
    (hcoord : ∀ x : E, (φ x)^2+(ψ x)^2≤‖x‖^2) :
    ∀ x : E, ‖x‖=1 → |(harmonicTensor φ ψ a).form x x x|≤2*a := by
  intro x hx
  have hcs : (φ x)^2+(ψ x)^2≤1 := by simpa only [hx,one_pow] using hcoord x
  have h := harmonic_polynomial_bound (φ x) (ψ x) hcs
  rw [harmonicTensor_diagonal,abs_mul,abs_of_nonneg (by positivity)]
  have hm := mul_le_mul_of_nonneg_left h (by positivity : 0≤2*a/Real.sqrt 2)
  have he : 2*a/Real.sqrt 2*Real.sqrt 2=2*a :=
    div_mul_cancel₀ _ (Real.sqrt_pos.mpr (by norm_num)).ne'
  exact hm.trans_eq he

/-- The two orthonormal coordinates satisfy the actual Bessel bound.
Article: main_krylov, thm:H, the canonical plane projection. -/
theorem orthonormal_pair_coordinates (e h x : E) (he : ‖e‖=1) (hh : ‖h‖=1)
    (heh : inner ℝ e h=0) :
    (inner ℝ e x)^2+(inner ℝ h x)^2≤‖x‖^2 := by
  have hee : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he,one_pow]
  have hhh : inner ℝ h h=1 := by rw [real_inner_self_eq_norm_sq,hh,one_pow]
  have hhe : inner ℝ h e=0 := (real_inner_comm e h).trans heh
  have hxe : inner ℝ x e=inner ℝ e x := real_inner_comm e x
  have hxh : inner ℝ x h=inner ℝ h x := real_inner_comm h x
  have hp : 0≤ inner ℝ (x-(inner ℝ e x) • e-(inner ℝ h x) • h)
      (x-(inner ℝ e x) • e-(inner ℝ h x) • h) := real_inner_self_nonneg
  simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    conj_trivial,hee,hhh,heh,hhe,hxe,hxh,real_inner_self_eq_norm_sq] at hp
  nlinarith

/-- The printed harmonic tensor in the canonical plane spanned by e,h.
Article: main_krylov, thm:H. -/
def canonicalHarmonicTensor [CompleteSpace E] (e h : E) (a : ℝ) : SymmetricCubic E :=
  harmonicTensor (canonicalBilinear e) (canonicalBilinear h) a

/-- The actual canonical harmonic tensor satisfies its required diagonal budget.
Article: main_krylov, thm:H. -/
theorem canonicalHarmonicTensor_bound [CompleteSpace E] (e h : E)
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0) {a : ℝ} (ha : 0≤a) :
    ∀ x : E, ‖x‖=1 → |(canonicalHarmonicTensor e h a).form x x x|≤2*a := by
  apply harmonicTensor_diagonal_bound _ _ ha
  exact fun x => orthonormal_pair_coordinates e h x he hh heh

/-- The actual harmonic cubic function of the paper is standard self-concordant
on the exact printed canonical ball.
Article: main_krylov, thm:H, the cubic lower-bound realization.
Proof: the true orthonormal-coordinate tensor bound and its actual derivative
fields instantiate the proved cubic self-concordance theorem. -/
theorem canonicalHarmonic_selfConcordant [CompleteSpace E] [FiniteDimensional ℝ E]
    (e h : E) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    {δ : ℝ} (hδ0 : 0<δ) (hδ1 : δ<1) :
    0<canonicalCubicRadius (1-δ) ∧
      IsStandardSelfConcordantOn (canonicalCubic (canonicalHarmonicTensor e h (1-δ)))
        (Metric.ball 0 (canonicalCubicRadius (1-δ))) := by
  constructor
  · exact canonicalCubicRadius_pos (by linarith) (by linarith)
  · apply canonicalCubic_selfConcordant_radius _ (by linarith)
    exact canonicalHarmonicTensor_bound e h he hh heh (by linarith)

end
end krylov.Functions
