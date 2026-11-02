import krylov.Strings.OptimizerStableOrbits
import krylov.LotkaVolterra.ExitSide

/-!
Article: main_krylov, apC:prop:LV, identification of the full stable set.
Use: every positive original-time orbit converging to the saddle lies on
the constructed analytic graph; the converse is supplied by the actual
global forward orbits of both branches.
Source: the exact linear equation for signed distance from the graph. Its
squared distance is eventually nondecreasing and tends to zero, so vanishes.
This avoids assuming a general stable-manifold theorem.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

namespace SubcriticalGraph
variable {γ : ℝ} (G : SubcriticalGraph γ)

/-- The proved wedge estimate bounds the derivative of this same graph at
the saddle, without selecting a separate local stable-manifold witness. -/
theorem norm_deriv_saddle_le (hγ : 0 < γ) (hγ₁ : γ < 1) :
    |deriv G.σ (saddleU γ)| ≤ γ := by
  have hd := ((G.contDiffAt_one hγ hγ₁ (saddleU_pos hγ₁)).differentiableAt
    (by norm_num)).hasDerivAt
  have hh := hd.le_of_lip' hγ.le (by
    filter_upwards [Ioi_mem_nhds (saddleU_pos hγ₁)] with U hU
    simpa only [Real.norm_eq_abs, G.saddle] using G.saddle_lipschitz_bound hγ₁ hU)
  simpa only [Real.norm_eq_abs] using hh

/-- The exact scalar coefficient of signed displacement from the separating graph. -/
def orbitDifferenceCoefficient (α : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  2 * ((α t).1 + G.σ ((α t).2) - 1 - γ * (α t).2) -
    (α t).2 * deriv G.σ ((α t).2)

/-- The signed distance from the graph solves an exact scalar linear ODE. -/
theorem orbit_difference_hasDerivAt (hγ : 0 < γ) (hγ₁ : γ < 1)
    {α : ℝ → ℝ × ℝ} {t : ℝ} (hα : HasDerivAt α (vectorField γ (α t)) t)
    (hU : 0 < (α t).2) :
    HasDerivAt (fun u ↦ (α u).1 - G.σ ((α u).2))
      (G.orbitDifferenceCoefficient α t * ((α t).1 - G.σ ((α t).2))) t := by
  have hdS : HasDerivAt (fun t ↦ (α t).1)
      (2 * (α t).1 * ((α t).1 - 1 - γ * (α t).2)) t := by
    convert! (hasFDerivAt_fst (𝕜 := ℝ) (p := α t)).comp_hasDerivAt t hα using 1
  have hdU : HasDerivAt (fun t ↦ (α t).2)
      ((α t).2 * ((α t).1 + 1 - (α t).2)) t := by
    convert! (hasFDerivAt_snd (𝕜 := ℝ) (p := α t)).comp_hasDerivAt t hα using 1
  have hGd := ((G.contDiffAt_one hγ hγ₁ hU).differentiableAt (by norm_num)).hasDerivAt
  have hh := hdS.sub (hGd.comp t hdU)
  have heq := G.graph_equation_all hγ₁ hU
  convert hh using 1
  · rfl
  · dsimp [orbitDifferenceCoefficient]
    nlinarith only [heq]

/-- Every actual positive forward orbit tending to the saddle is contained
in the constructed graph, at every nonnegative original time. -/
theorem graph_of_tendsto_saddle (hγ : 0 < γ) (hγ₁ : γ < 1)
    {α : ℝ → ℝ × ℝ} (hα : IsSolutionOn γ α (Ici 0))
    (hp : ∀ t ≥ 0, α t ∈ positiveQuadrant)
    (hlim : Tendsto α atTop (𝓝 (saddlePoint γ))) :
    ∀ t ≥ 0, (α t).1 = G.σ ((α t).2) := by
  let d : ℝ → ℝ := fun t ↦ (α t).1 - G.σ ((α t).2)
  let D : ℝ → ℝ := fun t ↦ d t ^ 2
  have hS : Tendsto (fun t ↦ (α t).1) atTop (𝓝 (saddleS γ)) :=
    continuous_fst.tendsto _ |>.comp hlim
  have hU : Tendsto (fun t ↦ (α t).2) atTop (𝓝 (saddleU γ)) :=
    continuous_snd.tendsto _ |>.comp hlim
  have hG : Tendsto (fun t ↦ G.σ ((α t).2)) atTop (𝓝 (saddleS γ)) := by
    simpa only [G.saddle, Function.comp_def] using (G.continuousAt_saddle hγ₁).tendsto.comp hU
  have hdlim : Tendsto d atTop (𝓝 0) := by simpa only [sub_self] using hS.sub hG
  have hDlim : Tendsto D atTop (𝓝 0) := by simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hdlim.pow 2
  have hdercont : ContinuousAt (deriv G.σ) (saddleU γ) :=
    ((G.contDiffAt_one hγ hγ₁ (saddleU_pos hγ₁)).derivWithin
      (m := 0) (by norm_num)).continuousAt
  have haLim : Tendsto (G.orbitDifferenceCoefficient α) atTop
      (𝓝 (2 * saddleS γ - saddleU γ * deriv G.σ (saddleU γ))) := by
    change Tendsto (fun t ↦ 2 * ((α t).1 + G.σ ((α t).2) - 1 - γ * (α t).2) -
      (α t).2 * deriv G.σ ((α t).2)) atTop
      (𝓝 (2 * saddleS γ - saddleU γ * deriv G.σ (saddleU γ)))
    have hh := (((hS.add hG).sub_const 1).sub (hU.const_mul γ)).const_mul 2 |>.sub
      (hU.mul (hdercont.tendsto.comp hU))
    have he : 2 * (saddleS γ + saddleS γ - 1 - γ * saddleU γ) -
        saddleU γ * deriv G.σ (saddleU γ) =
        2 * saddleS γ - saddleU γ * deriv G.σ (saddleU γ) := by
      linarith [saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)]
    simpa only [Function.comp_def, he] using hh
  have haPos : 0 < 2 * saddleS γ - saddleU γ * deriv G.σ (saddleU γ) := by
    have hder := (le_abs_self (deriv G.σ (saddleU γ))).trans (G.norm_deriv_saddle_le hγ hγ₁)
    have hprod := mul_le_mul_of_nonneg_left hder (saddleU_pos hγ₁).le
    have hrel := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
    nlinarith [saddleS_pos hγ hγ₁]
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp ((tendsto_order.mp haLim).1 0 haPos)
  let T := max T₀ 0
  have hT : 0 ≤ T := le_max_right _ _
  have ha (t : ℝ) (ht : T ≤ t) : 0 ≤ G.orbitDifferenceCoefficient α t :=
    (hT₀ t ((le_max_left _ _).trans ht)).le
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt d
      (G.orbitDifferenceCoefficient α t * d t) t :=
    G.orbit_difference_hasDerivAt hγ hγ₁ (hα t ht) (hp t ht).2
  have hD (t : ℝ) (ht : 0 ≤ t) : HasDerivAt D
      (2 * d t * (G.orbitDifferenceCoefficient α t * d t)) t := by
    convert (hd t ht).pow 2 using 1
    simp only [show (2 - 1 : ℕ) = 1 by decide, pow_one, Nat.cast_ofNat]
  have hmono : MonotoneOn D (Ici T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici T)
      (HasDerivAt.continuousOn (fun t ht ↦ hD t (hT.trans ht)))
      (fun t ht ↦ (hD t (hT.trans (interior_subset ht))).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hD t (hT.trans (interior_subset ht))).deriv]
    have hh := mul_nonneg (ha t (interior_subset ht)) (sq_nonneg (d t))
    nlinarith only [hh]
  have hDT : D T ≤ 0 := by
    apply ge_of_tendsto hDlim
    filter_upwards [eventually_ge_atTop T] with t ht
    exact hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  have hdT : d T = 0 := (sq_eq_zero_iff).mp (le_antisymm hDT (sq_nonneg _))
  obtain ⟨k, hk, hfactor⟩ := G.orbit_difference_factor hγ hγ₁ hT
    (fun t ht ↦ hα t ht.1) (fun t ht ↦ (hp t ht.1).2)
  change d T = d 0 * k at hfactor
  have hd₀ : d 0 = 0 := (mul_eq_zero.mp (by rw [← hfactor, hdT])).resolve_right hk.ne'
  intro t ht
  obtain ⟨k, _, hfactor⟩ := G.orbit_difference_factor hγ hγ₁ ht
    (fun t ht ↦ hα t ht.1) (fun t ht ↦ (hp t ht.1).2)
  change d t = d 0 * k at hfactor
  have hdt : d t = 0 := by simpa only [hd₀, zero_mul] using hfactor
  exact sub_eq_zero.mp hdt

/-- The full positive stable set equals the named graph. Both directions
refer to actual original-time solutions, rather than reparametrized arcs. -/
theorem mem_stable_set_iff (hγ : 0 < γ) (hγ₁ : γ < 1) {z : ℝ × ℝ}
    (hz : z ∈ positiveQuadrant) :
    (∃ α : ℝ → ℝ × ℝ, α 0 = z ∧ IsSolutionOn γ α (Ici 0) ∧
      (∀ t ≥ 0, α t ∈ positiveQuadrant) ∧ Tendsto α atTop (𝓝 (saddlePoint γ))) ↔
      z.1 = G.σ z.2 := by
  constructor
  · rintro ⟨α, hα₀, hα, hp, hlim⟩
    simpa only [hα₀] using G.graph_of_tendsto_saddle hγ hγ₁ hα hp hlim 0 le_rfl
  · intro hzG
    obtain ⟨α, hα₀, hα, hp, _, _, _, hlim⟩ :=
      krylov.Strings.OptimizerQuadratures.exists_global_stable_solution hγ hγ₁ G hz.2
    exact ⟨α, hα₀.trans (Prod.ext hzG.symm rfl), hα, fun t ht ↦ (hp t ht).1, hlim⟩

end SubcriticalGraph
end
end krylov.LotkaVolterra
