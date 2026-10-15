import «2606.16671v2».Analysis.SingularBoundary
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Article: 2606.16671v2, Theorem E.3.
Uniqueness of the non-logarithmic branch at a square-root singular endpoint.
Use: `«2606.16671v2».Analysis.singular_sqrt_unique` feeds
`«2606.16671v2».SineJacobi.sineProfile_unique` (The solution and boundary normalization stated in
E.3 determine the profile uniquely).
Proof chain: `«2606.16671v2».SineJacobi.sineProfile_unique` — 2606.16671v2, Theorem E.3; Hard-edge
recurrence, singular ODE, uniqueness and endpoint limits.
Source: mathlib, Mathlib.Analysis.Calculus.MeanValue, Mathlib.Analysis.SpecialFunctions.Sqrt —
Wronskian uniqueness for the bounded singular ODE branch. The needed form is proved here.
-/
namespace «2606.16671v2».Analysis
noncomputable section
open Real Set Filter Topology

/--
Two solutions of `y'' = -q y` with the same normalization `y(t)/√t → 1` at the left singular
endpoint coincide on `(0,1)`, provided the reference solution `f` is strictly positive there.
No regularity of `q` at the endpoint is assumed. The Wronskian is constant. A nonzero Wronskian
would make a rescaled ratio `g/f` have derivative bounded below by a positive multiple of
`1/t`, contradicting its finite endpoint limit. A zero Wronskian makes the ratio constant, and
the normalization fixes that constant to one. Use: `SineJacobi.sineProfile_unique` applies this
lemma to the actual singular profile equation. Article chain: 2606.16671v2, Theorem E.3,
uniqueness of the nonlogarithmic branch. Source: the classical Wronskian uniqueness argument,
with the endpoint divergence proved in `no_positive_logarithmic_derivative`.

Pointwise equality on the specified domain: `EqOn g f (Ioo 0 1)`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities. A vanishing derivative makes the relevant function constant on the
connected interval. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem singular_sqrt_unique {f f' g g' q : ℝ → ℝ}
    (hf : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f' (-q t*f t) t)
    (hg : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt g' (-q t*g t) t)
    (hpos : ∀ t ∈ Ioo (0:ℝ) 1, 0 < f t)
    (hfb : Tendsto (fun t => f t/sqrt t) (𝓝[>] 0) (𝓝 1))
    (hgb : Tendsto (fun t => g t/sqrt t) (𝓝[>] 0) (𝓝 1)) :
    EqOn g f (Ioo 0 1) := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  let W : ℝ → ℝ := fun t => g' t*f t-g t*f' t
  -- The common differential equation cancels both terms in the Wronskian derivative.
  have hW : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt W 0 t := by
    intro t ht
    convert ((hg' t ht).mul (hf t ht)).sub ((hg t ht).mul (hf' t ht)) using 1 ;
      simp ; ring
  obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (convex_Ioo (0:ℝ) 1).isPreconnected
    (fun t ht => (hW t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hW t ht).deriv)
  let r : ℝ → ℝ := fun t => g t/f t
  -- Positivity of f permits division throughout the open interval. Its square
  -- turns the constant Wronskian into the derivative of the solution ratio.
  have hr : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt r (c/(f t)^2) t := by
    intro t ht
    convert (hg t ht).div (hf t ht) (hpos t ht).ne' using 1
    change c/(f t)^2 = W t/(f t)^2
    rw [hc t ht]
  -- Record the convergence hrb with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hrb : Tendsto r (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have h := hgb.div hfb (by norm_num)
    simp only [div_self (by norm_num : (1:ℝ) ≠ 0)] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    dsimp [r]
    exact div_div_div_cancel_right₀ (sqrt_pos.mpr ht).ne' (g t) (f t)
  have hc0 : c = 0 := by
    -- Near zero, f(t)/√t → 1 gives f(t)² ≤ 4t. If c ≠ 0, the derivative of
    -- c*g/f is therefore at least c²/(4t), forcing logarithmic divergence.
    by_contra hn
    have hupper : ∀ᶠ t in 𝓝[>] (0:ℝ), f t/sqrt t < 2 :=
      hfb.eventually_lt_const (by norm_num)
    obtain ⟨b, hb, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hupper
    let B := min b 1
    have hB : 0 < B := lt_min hb (by norm_num)
    have hbnd : ∀ t ∈ Ioo (0:ℝ) B, (f t)^2 ≤ 4*t := by
      intro t ht
      have ht1 : t ∈ Ioo (0:ℝ) 1 := ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩
      have hlt := (div_lt_iff₀ (sqrt_pos.mpr ht.1)).mp
        (hbound ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩)
      nlinarith [sq_sqrt ht.1.le, hpos t ht1, sqrt_nonneg t]
    apply no_positive_logarithmic_derivative hB
      (show 0 < c^2/4 from div_pos (sq_pos_of_ne_zero hn) (by norm_num))
      (u := fun t => c*r t) (u' := fun t => c^2/(f t)^2)
    · intro t ht
      convert (hr t ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩).const_mul c using 1 ; ring
    · intro t ht
      have hp := sq_pos_of_pos (hpos t ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩)
      rw [div_div, div_le_div_iff₀ (mul_pos (by norm_num) ht.1) hp]
      nlinarith [hbnd t ht, sq_nonneg c]
    · simpa using (tendsto_const_nhds (x := c)).mul hrb
  obtain ⟨a, ha⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (convex_Ioo (0:ℝ) 1).isPreconnected
    (fun t ht => (hr t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hr t ht).deriv, hc0, zero_div]; rfl)
  have ha1 : a = 1 := by
    -- The ratio is now constant; its already established right-hand limit is one.
    have he : r =ᶠ[𝓝[>] (0:ℝ)] fun _ => a := by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
      exact ha t ht
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' he.symm) hrb
  intro t ht
  have he := ha t ht
  rw [ha1] at he
  exact (div_eq_one_iff_eq (hpos t ht).ne').mp he

end
end «2606.16671v2».Analysis
