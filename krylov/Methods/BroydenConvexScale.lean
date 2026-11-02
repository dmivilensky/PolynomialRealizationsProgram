import krylov.Methods.BroydenReferencePair

set_option autoImplicit false
/-!
Article: main_krylov, def:classes, genuine positive convex Broyden direction scale.
Use: prove actual convex secant interpolation preserves a true positive CG direction scale on every real nondegenerate reference pair.
Source: actual DFP/BFGS endpoint direction identities and genuine positivity of both real reference scales, including interpolation endpoints.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- Every actual convex combination of the genuine DFP and BFGS reference scales is strictly positive.
Use: Every actual convex combination of the genuine DFP and BFGS reference scales is strictly positive.
Article: main_krylov, def:classes, genuine positive convex Broyden direction scale.
Proof: The real inverse-curvature denominator is positive; one positive endpoint contribution survives at every true parameter in the closed unit interval. -/
theorem broyden_convex_scale_pos (c a : ℝ) (hc : 0<c) (ha : 0<a)
    (g r : E) (hg : g≠0) (θ : ℝ) (hθ : 0≤θ ∧ θ≤1) :
    0<(1-θ)*(c*a*‖g‖^2/(c*‖r‖^2+a*‖g‖^2))+θ*c := by
  -- True residual nondegeneracy makes both genuine endpoint scales strictly positive, including either interpolation endpoint.
  have hA : 0<‖g‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hg)
  have hσ : 0<c*‖r‖^2+a*‖g‖^2 :=
    add_pos_of_nonneg_of_pos (mul_nonneg hc.le (sq_nonneg _)) (mul_pos ha hA)
  have hp : 0<c*a*‖g‖^2/(c*‖r‖^2+a*‖g‖^2) := div_pos (mul_pos (mul_pos hc ha) hA) hσ
  by_cases hz : θ=0
  · simpa only [hz,sub_zero,one_mul,zero_mul,add_zero] using hp
  · have ht : 0<θ := lt_of_le_of_ne hθ.1 (Ne.symm hz)
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hθ.2) hp.le) (mul_pos ht hc)

/-- The genuine inverse convex Broyden update sends the actual new reference gradient to a true positive multiple of the negative next CG direction.
Use: The genuine inverse convex Broyden update sends the actual new reference gradient to a true positive multiple of the negative next CG direction.
Article: main_krylov, def:classes, genuine positive convex Broyden direction scale.
Proof: Combine the proved actual endpoint identities and genuine convex-scale positivity, retaining the real closed interpolation interval. -/
theorem inverseBroydenUpdate_reference (H : E →ₗ[ℝ] E) (g r d : E) (c a α θ : ℝ)
    (hc : 0<c) (ha : 0<a) (hα : α≠0) (hg0 : g≠0) (hθ : 0≤θ ∧ θ≤1)
    (hg : H g= -a • d) (hr : H r=c • r)
    (hgd : inner ℝ g d= -‖g‖^2) (hrd : inner ℝ r d=0) (hgr : inner ℝ g r=0) :
    ∃ b : ℝ,0<b ∧ inverseBroydenUpdate H (α • d) (r-g) θ r=
      -b • (-r+(‖r‖^2/‖g‖^2) • d) := by
  let b := (1-θ)*(c*a*‖g‖^2/(c*‖r‖^2+a*‖g‖^2))+θ*c
  refine ⟨b,broyden_convex_scale_pos c a hc ha g r hg0 θ hθ,?_⟩
  rw [inverseBroydenUpdate,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.smul_apply,
    inverseDFPUpdate_reference H g r d c a α hc ha hg0 hg hr hgd hrd hgr,
    inverseBFGSUpdate_reference H g r d c a α hα hg0 hg hr hgd hrd hgr]
  dsimp only [b]
  module
end
end krylov.Methods
