import nesterov.Flow.Cone
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: Proposition `one`, consequence for genuine Hilbert-space solutions.
Use: a conformal real-linear embedding of one complex spiral forces the
gradient and value jets, so its actual convex remainder satisfies P_c.
-/

noncomputable section

namespace nesterov.Flow

open Filter
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem embedded_spiral_program {θ m c γ R : ℝ} {f : E → ℝ}
    (hf : Objective m f) (hc : 0 < c) (hR : 0 < R)
    (T : ℂ →L[ℝ] E) (hinner : ∀ u w : ℂ, ⟪T u, T w⟫_ℝ = R * ⟪u, w⟫_ℝ)
    {v : ℝ → E} (hsol : IsSolution θ f (fun t => T (scalarSpiral c γ t)) v) :
    OneAtomFeasible θ m c γ := by
  let x := fun t => T (scalarSpiral c γ t)
  let v' := fun t => T (spiralExponent c γ * scalarSpiral c γ t)
  let G := fun t => T (spiralMultiplier θ m c γ * scalarSpiral c γ t)
  let η := fun t => R * Real.exp (-2 * c * t) * atomValue θ m c γ
  have hv (t : ℝ) (ht : 0 ≤ t) : v t = v' t := by
    exact (hsol.position_derivative t ht).unique
      (T.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_scalarSpiral c γ t))
  have hG (t : ℝ) (ht : 0 < t) : remainderGradient m f (x t) = G t := by
    have hlocal : v =ᶠ[𝓝 t] v' := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      exact hv s hs.le
    have hdv := (T.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_scalarSpiral_velocity c γ t)).congr_of_eventuallyEq hlocal
    have heq := (hsol.velocity_derivative t ht.le).unique hdv
    have hode := congrArg T (scalarSpiral_ode θ m c γ t)
    simp only [map_add, map_zero, ← Complex.real_smul, map_smul] at hode
    rw [hv t ht.le] at heq
    dsimp [remainderGradient, x, v', G] at *
    linear_combination (norm := module) -heq - hode
  have hηderiv (t : ℝ) : HasDerivAt η
      (R * Real.exp (-2 * c * t) * (c * delta θ m c + (c - θ) * γ ^ 2)) t := by
    have hh := ((((hasDerivAt_id t).const_mul (-2 * c)).exp).const_mul R).mul_const
      (atomValue θ m c γ)
    convert hh using 1
    · rfl
    · dsimp [atomValue]
      field_simp
      ring
  have hderiv (t : ℝ) (ht : 0 < t) : HasDerivAt
      (fun s => remainder m f (x s) - η s) 0 t := by
    have hrem := (hasGradientAt_remainder (m := m) hf.differentiable (x t)).hasFDerivAt.comp_hasDerivAt t
      (T.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_scalarSpiral c γ t))
    have hrem' : HasDerivAt (fun s => remainder m f (x s))
        ⟪remainderGradient m f (x t), v' t⟫_ℝ t := by
      simpa only [Function.comp_def, InnerProductSpace.toDual_apply_apply] using hrem
    rw [hG t ht] at hrem'
    dsimp [G, v'] at hrem'
    rw [hinner, scalarSpiral_velocity_inner] at hrem'
    convert hrem'.sub (hηderiv t) using 1
    ring
  have hconst (t : ℝ) (ht : 0 < t) :
      remainder m f (x t) - η t = remainder m f (x 1) - η 1 := by
    exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
      (fun s hs => (hderiv s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hderiv s hs).deriv) ht (by norm_num)
  have hexp (a : ℝ) (ha : 0 < a) : Tendsto (fun t : ℝ => Real.exp (-a * t)) atTop (𝓝 0) := by
    simpa only [neg_mul, Function.comp_def, id_eq] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop ha)
  have hscalar : Tendsto (scalarSpiral c γ) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [scalarSpiral_norm] using hexp c hc
  have hxlim : Tendsto x atTop (𝓝 0) := by
    simpa only [map_zero, Function.comp_def, x] using T.continuous.continuousAt.tendsto.comp hscalar
  have hremzero : remainder m f 0 = 0 := by simp [remainder, hf.value_zero]
  have hremlim : Tendsto (fun t => remainder m f (x t)) atTop (𝓝 0) := by
    have hh := (hasGradientAt_remainder (m := m) hf.differentiable (0 : E)).continuousAt.tendsto.comp hxlim
    simpa only [hremzero, Function.comp_def] using hh
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have hh := ((hexp (2 * c) (by positivity)).const_mul R).mul_const (atomValue θ m c γ)
    simpa [η, neg_mul] using hh
  have hzero : remainder m f (x 1) - η 1 = 0 := by
    have hp := hremlim.sub hηlim
    have heq : (fun t => remainder m f (x t) - η t) =ᶠ[atTop]
        (fun _ => remainder m f (x 1) - η 1) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact hconst t ht
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' heq.symm) (by simpa using hp)
  have hvalue (t : ℝ) (ht : 0 < t) : remainder m f (x t) = η t := by
    have hh := hconst t ht
    rw [hzero] at hh
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    have htq : 0 < 1 + q := by linarith
    have hh := hf.toStronglyConvexObjective.remainder_tangent (x 1) (x (1 + q))
    rw [hvalue 1 (by norm_num), hvalue (1 + q) htq, hG 1 (by norm_num)] at hh
    dsimp [x, G, η] at hh
    rw [← map_sub, hinner] at hh
    have hs := scalar_forward_slack hc θ m γ 1 q
    have hp : 0 < R * Real.exp (-2 * c * 1 - c * q) := mul_pos hR (Real.exp_pos _)
    exact nonneg_of_mul_nonneg_left (by nlinarith) hp
  · intro q hq
    have htq : 0 < 1 + q := by linarith
    have hh := hf.toStronglyConvexObjective.remainder_tangent (x (1 + q)) (x 1)
    rw [hvalue 1 (by norm_num), hvalue (1 + q) htq, hG (1 + q) htq] at hh
    dsimp [x, G, η] at hh
    rw [← map_sub, hinner] at hh
    have hs := scalar_backward_slack hc θ m γ 1 q
    have hp : 0 < R * Real.exp (-2 * c * 1 - c * q) := mul_pos hR (Real.exp_pos _)
    exact nonneg_of_mul_nonneg_left (by nlinarith) hp
  · have hh := hf.remainder_support_nonneg (x 1)
    rw [hvalue 1 (by norm_num), hG 1 (by norm_num)] at hh
    dsimp [x, G, η] at hh
    rw [hinner, scalar_minimizer_inner] at hh
    have ha := atomValue_add_gap (θ := θ) (m := m) (γ := γ) hc
    have hp : 0 < R * Real.exp (-2 * c * 1) := mul_pos hR (Real.exp_pos _)
    have hgap : 0 ≤ atomMinimizerGap θ m c γ :=
      nonneg_of_mul_nonneg_left (by nlinarith) hp
    dsimp [atomMinimizerGap] at hgap
    have hnum := (le_div_iff₀ (show 0 < 2 * c by positivity)).mp hgap
    linarith

/-- The real-linear plane with coordinate vectors a,b. -/
def planeMap (a b : E) : ℂ →L[ℝ] E :=
  Complex.reCLM.smulRight a + Complex.imCLM.smulRight b

omit [CompleteSpace E] in
theorem planeMap_apply (a b : E) (z : ℂ) : planeMap a b z = z.re • a + z.im • b := rfl

omit [CompleteSpace E] in
theorem planeMap_inner {a b : E} (hab : ⟪a, b⟫_ℝ = 0) (hnorm : ‖a‖ = ‖b‖)
    (u w : ℂ) : ⟪planeMap a b u, planeMap a b w⟫_ℝ = ‖a‖ ^ 2 * ⟪u, w⟫_ℝ := by
  have hba : ⟪b, a⟫_ℝ = 0 := by rw [real_inner_comm, hab]
  rw [planeMap_apply, planeMap_apply]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, hab, hba, mul_zero, add_zero, zero_add,
    starRingEnd_apply, star_trivial, ← hnorm]
  simp [real_inner_eq_re_inner, RCLike.inner_apply]
  ring

/-- The position formula in Proposition one, with arbitrary radius. -/
def spiralCurve (c γ : ℝ) (a b : E) (t : ℝ) : E :=
  Real.exp (-c * t) • (Real.cos (γ * t) • a + Real.sin (γ * t) • b)

omit [CompleteSpace E] in
theorem planeMap_scalarSpiral (c γ : ℝ) (a b : E) (t : ℝ) :
    planeMap a b (scalarSpiral c γ t) = spiralCurve c γ a b t := by
  rw [planeMap_apply, scalarSpiral_re, scalarSpiral_im]
  dsimp [spiralCurve]
  module

/-- Proposition one, including the stated consequence for every genuine
objective in F_m on an arbitrary real Hilbert space. -/
theorem no_single_spiral_trajectory {θ m : ℝ} (hθ : 0 < θ) (hm : 0 < m)
    (hgap : θ / 3 < cQ θ m) :
    ∃ csharp : ℝ, θ / 3 < csharp ∧ csharp < cQ θ m ∧
      ∀ (c γ : ℝ) (a b : E) (f : E → ℝ), θ / 3 < c → c ≤ csharp → 0 ≤ γ →
        ⟪a, b⟫_ℝ = 0 → ‖a‖ = ‖b‖ → 0 < ‖a‖ → Objective m f →
        ¬∃ v : ℝ → E, IsSolution θ f (spiralCurve c γ a b) v := by
  obtain ⟨csharp, ha, hb, hno⟩ := exists_oneAtom_obstruction hθ hm hgap
  refine ⟨csharp, ha, hb, ?_⟩
  intro c γ a b f hc hcap hγ hab hnorm hapos hf hsolution
  obtain ⟨v, hsol⟩ := hsolution
  apply hno c γ hc hcap hγ
  have hcpos : 0 < c := by linarith
  have hR : 0 < ‖a‖ ^ 2 := sq_pos_of_pos hapos
  have hcurve : (fun t => planeMap a b (scalarSpiral c γ t)) = spiralCurve c γ a b := by
    funext t
    exact planeMap_scalarSpiral c γ a b t
  apply embedded_spiral_program hf hcpos hR (planeMap a b) (planeMap_inner hab hnorm)
  rwa [hcurve]

end nesterov.Flow
