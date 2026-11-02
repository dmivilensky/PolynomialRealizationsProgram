import krylov.LotkaVolterra.GlobalExpandingUniqueness
import krylov.LotkaVolterra.Barrier

/-!
Asymptotically autonomous expanding scalar equations: a bounded trajectory
must converge to the limiting equilibrium. Source: strict first-contact
barriers and a linear-growth contradiction, rather than an assumed omega
limit-set theorem.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

/-- A bounded solution cannot enter a region where its derivative remains
uniformly positive. Strict first contact keeps it there; linear growth
would then contradict the bound. -/
theorem bounded_solution_le_of_positive_rate {v v' : ℝ → ℝ} {T a B η : ℝ}
    (hη : 0 < η) (hd : ∀ t ≥ T, HasDerivAt v (v' t) t)
    (hbound : ∀ t ≥ T, v t ≤ B)
    (hpos : ∀ t ≥ T, a ≤ v t → η ≤ v' t) : ∀ t ≥ T, v t ≤ a := by
  intro t ht
  by_contra! hva
  have hstay (u : ℝ) (hu : t ≤ u) : a < v u := by
    have hh := pair_positive_invariant hu
      (fun r hr ↦ (hd r (ht.trans hr.1)).sub_const a)
      (fun r _ ↦ hasDerivAt_const r (1 : ℝ)) (sub_pos.mpr hva) (by norm_num)
      (fun r hr heq _ ↦ lt_of_lt_of_le hη
        (hpos r (ht.trans hr.1) (by linarith)))
      (fun _ _ heq _ ↦ by norm_num at heq)
    linarith [hh.1]
  let u : ℝ := t + (B - v t + 1) / η
  have htu : t < u := lt_add_of_pos_right _ (div_pos (by linarith [hbound t ht]) hη)
  have hgrow : η * (u - t) ≤ v u - v t := by
    apply (convex_Ici t).mul_sub_le_image_sub_of_le_deriv
      (HasDerivAt.continuousOn fun r hr ↦ hd r (ht.trans hr))
      (fun r hr ↦ (hd r (ht.trans (interior_subset hr))).differentiableAt.differentiableWithinAt)
      (fun r hr ↦ by
        rw [(hd r (ht.trans (interior_subset hr))).deriv]
        exact hpos r (ht.trans (interior_subset hr)) (hstay r (interior_subset hr)).le)
      t (mem_Ici.mpr le_rfl) u (mem_Ici.mpr htu.le) htu.le
  have hid : η * (u - t) = B - v t + 1 := by
    dsimp [u]
    field_simp
    ring
  rw [hid] at hgrow
  linarith [hbound u (ht.trans htu.le)]

/-- Bounded trajectories of a uniformly expanding scalar equation converge
to any limiting equilibrium whose residual tends to zero. -/
theorem bounded_expanding_solution_tendsto {F : ℝ → ℝ → ℝ} {a b c r : ℝ}
    (hc : 0 < c) (hr : r ∈ Icc a b)
    (hF : ∀ t ≥ 0, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      c * (x - y) ^ 2 ≤ (x - y) * (F t x - F t y))
    (hres : Tendsto (fun t ↦ F t r) atTop (𝓝 0))
    {v : ℝ → ℝ}
    (hv : ∀ t ≥ 0, v t ∈ Icc a b ∧ HasDerivAt v (F t (v t)) t) :
    Tendsto v atTop (𝓝 r) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hη : 0 < c * ε / 4 := by positivity
  have hsmall : ∀ᶠ t in atTop, |F t r| < c * ε / 4 := by
    exact (tendsto_order.mp hres.abs).2 _ (by simpa using hη)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hsmall
  let T := max T₀ 0
  have hT (t : ℝ) (ht : T ≤ t) : 0 ≤ t := (le_max_right _ _).trans ht
  have hres' (t : ℝ) (ht : T ≤ t) : -c * ε / 4 < F t r ∧ F t r < c * ε / 4 := by
    have hh := abs_lt.mp (hT₀ t ((le_max_left _ _).trans ht))
    constructor <;> linarith [hh.1, hh.2]
  have hup : ∀ t ≥ T, v t ≤ r + ε / 2 := by
    apply bounded_solution_le_of_positive_rate hη
      (fun t ht ↦ (hv t (hT t ht)).2)
      (fun t ht ↦ (hv t (hT t ht)).1.2)
    intro t ht hvr
    have hd : 0 < v t - r := by linarith
    have hh := hF t (hT t ht) (v t) (hv t (hT t ht)).1 r hr
    have hh' : c * (v t - r) ≤ F t (v t) - F t r := by
      apply (mul_le_mul_iff_right₀ hd).mp
      nlinarith only [hh]
    nlinarith [hres' t ht, mul_nonneg hc.le (show 0 ≤ v t - r - ε / 2 by linarith)]
  have hlow : ∀ t ≥ T, r - ε / 2 ≤ v t := by
    have hh : ∀ t ≥ T, -v t ≤ -r + ε / 2 := by
      apply bounded_solution_le_of_positive_rate hη
        (fun t ht ↦ ((hv t (hT t ht)).2).neg)
        (B := -a) (fun t ht ↦ neg_le_neg (hv t (hT t ht)).1.1)
      intro t ht hvr
      change -r + ε / 2 ≤ -v t at hvr
      have hd : 0 < r - v t := by linarith
      have hg := hF t (hT t ht) r hr (v t) (hv t (hT t ht)).1
      have hg' : c * (r - v t) ≤ F t r - F t (v t) := by
        apply (mul_le_mul_iff_right₀ hd).mp
        nlinarith only [hg]
      nlinarith [hres' t ht, mul_nonneg hc.le (show 0 ≤ r - v t - ε / 2 by linarith)]
    intro t ht
    linarith [hh t ht]
  refine ⟨T, fun t ht ↦ ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hup t ht, hlow t ht]

end
end krylov.LotkaVolterra
