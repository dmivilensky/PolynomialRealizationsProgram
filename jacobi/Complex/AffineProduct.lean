import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-!
Article: jacobi, Proposition C.3.
An absolutely convergent affine canonical product is continuous, and
its genuine derivative at a zero is the slope of the vanishing factor
times the original product with that factor omitted. This is used for
the two original characteristic derivatives in the rho formula.
Source: the elementary local derivative rule for a genus-zero product.
Use: legitimizes the omitted-factor and scalar-product identities in the original characteristic derivative comparison.
-/
namespace jacobi.Complex
noncomputable section
open Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every affine product with an absolutely summable original weight sequence is genuinely multipliable at each complex energy.
Use: legitimizes the omitted-factor and scalar-product identities in the original characteristic derivative comparison.
Article: jacobi, Proposition C.3.
Proof: each actual factor perturbation has norm |c-z|*|w_k|, a fixed multiple of the genuine summable weight norm. -/
theorem affine_product_multipliable {w : ℕ → ℂ} (hw : Summable (fun k => ‖w k‖)) (c z : ℂ) :
    Multipliable (fun k : ℕ => 1+(c-z)*w k) := by
  apply multipliable_one_add_of_summable
  simpa only [norm_mul] using hw.mul_left ‖c-z‖

/-- Omitting any one factor from a genuinely absolutely convergent affine product preserves genuine multipliability.
Use: extracts the actual selected characteristic factor when proving the original rho derivative identity.
Article: jacobi, Proposition C.3.
Proof: replace that one actual weight by zero, whose norm is bounded by the original summable norm, then use affine_product_multipliable. -/
theorem affine_omit_product_multipliable {w : ℕ → ℂ} (hw : Summable (fun k => ‖w k‖)) (c z : ℂ) (k : ℕ) :
    Multipliable (fun j : ℕ => if j=k then 1 else 1+(c-z)*w j) := by
  classical
  have hv : Summable (fun j : ℕ => ‖if j=k then 0 else w j‖) :=
    hw.of_nonneg_of_le (fun _ => norm_nonneg _) (by intro j; split_ifs <;> simp)
  have hm := affine_product_multipliable hv c z
  convert! hm using 1
  funext j
  split_ifs <;> simp

/-- A genuinely absolutely convergent affine canonical product is continuous in its original complex spectral variable.
Use: the omitted-factor product has its actual root value in affine_product_derivative_at_zero.
Article: jacobi, Proposition C.3.
Source: dominated convergence for infinite products, proved in mathlib.
Proof: on the unit neighborhood of z_0, the actual perturbations
are bounded by (|c-z_0|+1)*|w_k|, one summable majorant. Each
original affine factor is continuous, so product dominated convergence applies. -/
theorem affine_product_continuous {w : ℕ → ℂ} (hw : Summable (fun k => ‖w k‖)) (c : ℂ) :
    Continuous (fun z : ℂ => ∏' k : ℕ,(1+(c-z)*w k)) := by
  -- The original affine factors share one genuinely summable majorant on every actual spectral neighborhood.
  apply continuous_iff_continuousAt.mpr
  intro z
  have hs := hw.mul_left (‖c-z‖+1)
  have hp (k : ℕ) : Tendsto (fun u : ℂ => (c-u)*w k) (𝓝 z) (𝓝 ((c-z)*w k)) :=
    (tendsto_const_nhds.sub tendsto_id).mul_const _
  have hb : ∀ᶠ u : ℂ in 𝓝 z,∀ k : ℕ,‖(c-u)*w k‖≤(‖c-z‖+1)*‖w k‖ := by
    filter_upwards [Metric.ball_mem_nhds z (by norm_num : (0:ℝ)<1)] with u hu
    have hd : ‖u-z‖<1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hu
    intro k
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hh := norm_sub_le (c-z) (u-z)
    rw [sub_sub_sub_cancel_right] at hh
    linarith
  exact tendsto_tprod_one_add_of_dominated_convergence hs hp hb

/-- The genuine derivative of an actual absolutely convergent affine product at a vanishing original factor is its original slope times the actual omitted-factor product.
Use: evaluates the original reference and Bessel characteristic derivatives and identifies their ratio with the defining rho product.
Article: jacobi, Appendix C.2 (norming ratios).
Source: the elementary simple-factor derivative rule for a genus-zero canonical product, proved here using actual slopes and product continuity.
Proof: replace the selected weight by zero to obtain a continuous
omitted-factor product. The actual product factors exactly into that
function and the selected vanishing affine factor. At the original
root, its genuine difference quotient is the constant slope times
the continuous omitted product; its limit is the asserted derivative. -/
theorem affine_product_derivative_at_zero {w : ℕ → ℂ}
    (hw : Summable (fun k => ‖w k‖)) (c z : ℂ) (k : ℕ)
    (hz : 1+(c-z)*w k=0) :
    HasDerivAt (fun u : ℂ => ∏' j : ℕ,(1+(c-u)*w j))
      (-w k*(∏' j : ℕ,if j=k then 1 else 1+(c-z)*w j)) z := by
  classical
  -- The actual omitted product is formed by a zero weight, keeping the same affine-product convergence theorem.
  let v : ℕ → ℂ := fun j => if j=k then 0 else w j
  let P : ℂ → ℂ := fun u => ∏' j : ℕ,(1+(c-u)*v j)
  have hv : Summable (fun j => ‖v j‖) := hw.of_nonneg_of_le (fun _ => norm_nonneg _) (by
    intro j
    dsimp [v]
    split_ifs <;> simp)
  have hP : Continuous P := affine_product_continuous hv c
  have hrepr (u : ℂ) : P u=∏' j : ℕ,if j=k then 1 else 1+(c-u)*w j := by
    apply tprod_congr
    intro j
    dsimp [v]
    split_ifs <;> simp
  have hfact (u : ℂ) : (∏' j : ℕ,(1+(c-u)*w j))=(1+(c-u)*w k)*P u := by
    have hm := multipliable_one_add_of_summable (hv.mul_left ‖c-u‖ |>.congr (fun j => (norm_mul _ _).symm))
    have hu : Multipliable (Function.update (fun j => 1+(c-u)*w j) k 1) := by
      convert! hm using 1
      funext j
      by_cases hj : j=k <;> simp [v,hj]
    rw [Multipliable.tprod_eq_mul_tprod_ite' k hu,← hrepr]
  rw [← hrepr z]
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply ((hP.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).const_mul (-w k)).congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hne : u-z≠0 := sub_ne_zero.mpr hu
  dsimp only [slope,vsub_eq_sub,smul_eq_mul]
  rw [hfact u,hfact z,hz,zero_mul,sub_zero]
  have he : 1+(c-u)*w k= -w k*(u-z) := by linear_combination hz
  rw [he]
  field_simp [hne]

end
end jacobi.Complex
