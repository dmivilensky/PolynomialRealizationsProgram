import krylov.ContinuumBV.StringPath

/-!
Article: main_krylov, apC:lem:fund, summation of all actual atomic losses.
Use: identify the jumps of the actual clipped Bellman potential with the
finite-impulse losses of the string's own Stieltjes measure, and prove their
unconditional summability. No impulse geometry or summability is assumed.
Source: actual cumulative-integral jump formulas, the invariant state domain,
and countable additivity of the BV Stieltjes vector measure.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open krylov.Strings krylov.ContinuumControl
open scoped Topology NNReal

/-- Actual atomic loss, determined by the true pre-atom physical state and
the singleton mass of the string measure. -/
def actualAtomLoss (M : Mass) (γ : ℝ) (σ φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  impulseLoss γ σ (φ x) (Function.leftLim (integralSlope M.measure φ) x)
    (Function.leftLim (integralEnergy M.measure φ) x) (M.measure.real {x})

/-- The source graph equation applies along the entire straight impulse,
because the actual left state and every mass insertion preserve K≤φp. -/
theorem graph_at_actual_impulse (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    {γ : ℝ} {σ : ℝ → ℝ} (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r)
    {x : ℝ} (hx : x ∈ Ioc 0 (L : ℝ)) :
    ∀ u ∈ Icc 0 (M.measure.real {x}), FeedbackGraphAt γ σ
      (φ x * (Function.leftLim (integralSlope M.measure φ) x + u * φ x) /
        (Function.leftLim (integralEnergy M.measure φ) x + u * φ x ^ 2)) := by
  have hz := boundedVariation_clippedState M hc hm h₀ L
  have hl := leftLim_mem_of_closed hz (isCompact_compactStateDomain M φ L).isClosed
    (fun t _ => clippedState_mem M hc hm h₀ L t) x
  rw [clippedState_leftLim M hc hm h₀ L hx.1 hx.2] at hl
  have hpos := compactStateDomain_positive_ratio M φ L hl
  intro u hu
  apply hgraph
  have hK : 0 < Function.leftLim (integralEnergy M.measure φ) x + u * φ x ^ 2 :=
    add_pos_of_pos_of_nonneg hpos.2.2.1 (mul_nonneg hu.1 (sq_nonneg _))
  apply (le_div_iff₀ hK).2
  have hdom := hl.2
  change Function.leftLim (integralEnergy M.measure φ) x ≤
    φ x * Function.leftLim (integralSlope M.measure φ) x at hdom
  nlinarith

/-- Exact jump of the genuine nonlinear BV potential at every positive
position of the physical window, including its rightmost atom. -/
theorem actual_potential_jump (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : γ ≠ 0)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r)
    {x : ℝ} (hx : x ∈ Ioc 0 (L : ℝ)) :
    Function.rightLim (statePotential γ σ ∘ clippedState M φ L) x -
      Function.leftLim (statePotential γ σ ∘ clippedState M φ L) x =
        -actualAtomLoss M γ σ φ x := by
  have hz := boundedVariation_clippedState M hc hm h₀ L
  have hreg : ∀ w ∈ compactStateDomain M φ L, ContDiffAt ℝ 1 (statePotential γ σ) w := by
    intro w hw
    obtain ⟨hφ, hp, hK, hr⟩ := compactStateDomain_positive_ratio M φ L hw
    exact contDiffAt_statePotential hγ hφ.ne' hp.ne' hK.ne' (hσ _ hr) (hgraph _ hr).positive
  have hl := leftLim_mem_of_closed hz (isCompact_compactStateDomain M φ L).isClosed
    (fun t _ => clippedState_mem M hc hm h₀ L t) x
  have hr := rightLim_mem_of_closed hz (isCompact_compactStateDomain M φ L).isClosed
    (fun t _ => clippedState_mem M hc hm h₀ L t) x
  rw [rightLim_comp hz (hreg _ hr).continuousAt, leftLim_comp hz (hreg _ hl).continuousAt,
    clippedState_rightLim M hc L (Ioc_subset_Icc_self hx),
    clippedState_leftLim M hc hm h₀ L hx.1 hx.2]
  have hd := actual_atom_potential_decrement M hγ hc hm h₀ hx.1
    (graph_at_actual_impulse M hc hm h₀ L hgraph hx)
  dsimp only [statePotential, actualAtomLoss]
  linarith

/-- The entire countable atomic contribution is the negative of the actual
potential's Stieltjes vector measure on those locations. BV and convergence
are conclusions, with no separately supplied jump decomposition. -/
theorem hasSum_actual_atomLoss {ι : Type*} [Countable ι] (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : γ ≠ 0)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r)
    (e : ι → ℝ) (he : Function.Injective e) (hemem : ∀ i, e i ∈ Ioc 0 (L : ℝ)) :
    ∃ hq : BoundedVariationOn (statePotential γ σ ∘ clippedState M φ L) univ,
      HasSum (fun i => actualAtomLoss M γ σ φ (e i)) (-hq.vectorMeasure (range e)) := by
  have hq := boundedVariation_actual_potential M hc hm h₀ L hγ hσ
    (fun r hr => (hgraph r hr).positive)
  refine ⟨hq, ?_⟩
  have hs := (hasSum_potential_jumps hq e he).neg
  simpa only [actual_potential_jump M hc hm h₀ L hγ hσ hgraph (hemem _), neg_neg] using hs

/-- Every countable distinct family of actual atoms has summable exact losses.
The statement also allows non-atomic positions, whose loss is automatically zero. -/
theorem summable_actual_atomLoss {ι : Type*} [Countable ι] (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : γ ≠ 0)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r)
    (e : ι → ℝ) (he : Function.Injective e) (hemem : ∀ i, e i ∈ Ioc 0 (L : ℝ)) :
    Summable (fun i => actualAtomLoss M γ σ φ (e i)) := by
  obtain ⟨_hq, hsum⟩ := hasSum_actual_atomLoss M hc hm h₀ L hγ hσ hgraph e he hemem
  exact hsum.summable

/-- All positive singleton masses form a countable set, by sigma-finiteness
of the actual Stieltjes measure. -/
theorem countable_actual_atoms (M : Mass) : {x : ℝ | 0 < M.measure {x}}.Countable := by
  have : SFinite M.measure := by dsimp [Mass.measure]; infer_instance
  simpa only [id_eq, ofPred_eq_eq_singleton] using
    (Measure.countable_meas_level_set_pos (μ := M.measure) measurable_id)

/-- The full atom set of the source's sum on (0,L]. -/
def actualAtoms (M : Mass) (L : ℝ≥0) : Set ℝ :=
  {x | x ∈ Ioc 0 (L : ℝ) ∧ 0 < M.measure {x}}

/-- Summability applies to all atoms simultaneously, without an externally
supplied enumeration or a finiteness assumption on the number of atoms. -/
theorem summable_all_actual_atomLoss (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : γ ≠ 0)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r) :
    Summable (fun x : actualAtoms M L => actualAtomLoss M γ σ φ x) := by
  have hcount : (actualAtoms M L).Countable :=
    (countable_actual_atoms M).mono (fun _ hx => hx.2)
  let : Countable (actualAtoms M L) := hcount.to_subtype
  exact summable_actual_atomLoss M hc hm h₀ L hγ hσ hgraph Subtype.val
    Subtype.val_injective (fun x => x.property.1)

end
end krylov.ContinuumBV
