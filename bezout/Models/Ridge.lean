import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
Article: bezout, Equation `eq:experiment-ridge`.
Use: the general distributed ridge objective has exactly the advertised
quadratic gradient; averaging worker linear terms preserves the prescribed minimizer.
Proof: differentiate squared Hilbert norms, transfer the design map using
self-adjointness, and expand the exact quadratic objective difference.
-/

namespace bezout.Models.Ridge
noncomputable section
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A worker's literal ridge objective, with symbolic data dimension and regularizer. -/
def objective (d ρ : ℝ) (A : E →L[ℝ] E) (z x : E) : ℝ :=
  ‖A x-z‖^2/(2*d)+(ρ/2)*‖x‖^2

/-- Differentiation of the actual ridge objective under its algebraic design identities.
The design identities are verified for the explicit rank-one square root separately. -/
theorem hasGradientAt_objective [CompleteSpace E] (d ρ : ℝ) (hd : d≠0)
    (A H : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (z c x : E)
    (hAA : ∀ v, A (A v)=d • (H v-ρ • v)) (hAz : A z=d • c) :
    HasGradientAt (objective d ρ A z) (H x-c) x := by
  have hf := (((A.hasFDerivAt (x := x)).sub_const z).norm_sq.const_mul (1/(2*d))).add
    ((hasFDerivAt_id x).norm_sq.const_mul (ρ/2))
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hf using 1
  · funext u
    simp only [objective, Pi.add_apply, id_eq]
    ring
  · ext u
    simp only [InnerProductSpace.toDual_apply_apply, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, id_eq,
      ContinuousLinearMap.id_apply, smul_eq_mul, two_smul]
    have hs := hA (A x-z) u
    change inner ℝ (A (A x-z)) u=inner ℝ (A x-z) (A u) at hs
    rw [map_sub, hAA, hAz, inner_sub_left, inner_smul_left, inner_smul_left,
      inner_sub_left, inner_smul_left] at hs
    simp only [conj_trivial] at hs
    simp only [inner_sub_left] at *
    field_simp
    nlinarith

/-- An exact quadratic difference formula yields the global minimizer directly. -/
theorem objective_difference (d ρ : ℝ) (hd : 0<d) (A H : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (z c x y : E)
    (hAA : ∀ v, A (A v)=d • (H v-ρ • v)) (hAz : A z=d • c) :
    objective d ρ A z (x+y)-objective d ρ A z x =
      inner ℝ (H x-c) y+(1/2)*inner ℝ (H y) y := by
  have hinner (v w : E) : inner ℝ (A v) (A w)=d*(inner ℝ (H v) w-ρ*inner ℝ v w) := by
    have hs := hA (A v) w
    change inner ℝ (A (A v)) w=inner ℝ (A v) (A w) at hs
    rw [hAA, inner_smul_left, inner_sub_left, inner_smul_left] at hs
    simpa only [conj_trivial, smul_eq_mul] using hs.symm
  have hzi : inner ℝ z (A y)=d*inner ℝ c y := by
    have hs := hA z y
    change inner ℝ (A z) y=inner ℝ z (A y) at hs
    rw [hAz, inner_smul_left] at hs
    exact hs.symm
  simp only [objective, map_add, ← real_inner_self_eq_norm_sq,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  rw [hinner x y, hinner y x, hinner y y, hzi, real_inner_comm z (A y),
    hzi, real_inner_comm y x]
  have hsym : inner ℝ (H y) x=inner ℝ (H x) y := by
    have hs := hinner x y
    have ht := hinner y x
    rw [real_inner_comm (A x) (A y), real_inner_comm x y] at ht
    nlinarith [hd]
  rw [hsym]
  field_simp
  ring

/-- Averaging the worker linear terms gives the stated global quadratic minimizer. -/
theorem mean_gradient_minimizer (H : E →L[ℝ] E) (xstar : E)
    (hH : ∀ y, 0 ≤ inner ℝ (H y) y) (f : E → ℝ)
    (hf : ∀ x y, f (x+y)-f x=inner ℝ (H x-H xstar) y+(1/2)*inner ℝ (H y) y) :
    ∀ x, f xstar≤f x := by
  intro x
  have h := hf xstar (x-xstar)
  simp only [add_sub_cancel, sub_self, inner_zero_left, zero_add] at h
  have hp := hH (x-xstar)
  linarith

end
end bezout.Models.Ridge
