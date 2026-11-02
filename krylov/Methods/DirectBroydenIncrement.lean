import krylov.Methods.DirectBroydenOperator
import krylov.Stability.C1VanishingProduct
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), genuine direct model increments.
Use: actual scalar model changes are products of two actual cross pairings;
actual vector secant changes have a single cross pairing.
Source: literal direct update and real inner-product symmetry.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
open Filter Topology Asymptotics
open scoped InnerProductSpace
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Real inner products multiply genuine norm asymptotic orders.
Use: propagate actual cross-curvature errors through the native update.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: the true inner-product bounded-linear operator and its actual
application satisfy the standard operator norm product bound. -/
theorem real_inner_bigO {l : Filter α} (u v : α → E) (a b : α → ℝ)
    (hu : u =O[l] a) (hv : v =O[l] b) :
    (fun z => inner ℝ (u z) (v z)) =O[l] (fun z => a z*b z) :=
  clm_apply_bigO _ v a b (((innerSL ℝ).isBigO_comp u l).trans hu) hv

/-- The actual vector change under the literal direct update has exactly
one true cross pairing in every genuine rank-one term.
Use: prove old native secant errors remain first order.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: expand the genuine update action and collect its old model term. -/
theorem directBroydenOperatorUpdate_change (B : E →L[ℝ] E) (s y u : E) (phi : ℝ) :
    directBroydenOperatorUpdate B s y phi u-B u=
      (-(inner ℝ s (B s))⁻¹*inner ℝ s (B u)) • B s+
      ((inner ℝ s y)⁻¹*inner ℝ y u) • y+
      (phi*inner ℝ s (B s)*inner ℝ (directBroydenVector B.toLinearMap s y) u) •
        directBroydenVector B.toLinearMap s y := by
  change directBroydenUpdate B.toLinearMap s y phi u-B u=_
  rw [directBroydenUpdate_apply]
  simp only [div_eq_mul_inv]
  module

/-- Every actual scalar direct-model change is the sum of three products
of two genuine cross pairings and actual native curvature coefficients.
Use: derive the original second-order comparison from first-order cross
pairings, without postulating a model comparison estimate.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: apply the exact native vector change, real symmetry of the old
model and the real inner-product commutation law. -/
theorem directBroydenOperatorUpdate_pairing_change (B : E →L[ℝ] E)
    (hB : B.toLinearMap.IsSymmetric) (s y u w : E) (phi : ℝ) :
    inner ℝ u (directBroydenOperatorUpdate B s y phi w)-inner ℝ u (B w)=
      -(inner ℝ s (B s))⁻¹*inner ℝ s (B w)*inner ℝ s (B u)+
      (inner ℝ s y)⁻¹*inner ℝ y w*inner ℝ y u+
      (phi*inner ℝ s (B s))*inner ℝ (directBroydenVector B.toLinearMap s y) w*
        inner ℝ (directBroydenVector B.toLinearMap s y) u := by
  rw [← inner_sub_right,directBroydenOperatorUpdate_change]
  simp only [inner_add_right,real_inner_smul_right]
  have hu : inner ℝ u (B s)=inner ℝ s (B u) :=
    (real_inner_comm (B s) u).trans (hB s u)
  rw [hu,real_inner_comm y u,real_inner_comm (directBroydenVector B.toLinearMap s y) u]

end
end krylov.Methods
