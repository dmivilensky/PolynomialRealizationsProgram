import krylov.ContinuumBV.Composition
import krylov.ContinuumControl.Impulse
import Mathlib.Tactic.FunProp

/-!
Article: main_krylov, apC:eq:f and apC:lem:fund, countably many atom losses.
Use: establish C¹ regularity and BV regularity of the actual potential, identify
its jumps by the exact finite-impulse calculation, and justify their summation.
Source: ordinary C¹ calculus, the BV Stieltjes measure, and countable additivity.
The continuous singular part of the nonlinear chain rule is a separate result.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open krylov.ContinuumControl
open scoped Topology

/-- Product state coordinates used for the ordinary C¹ potential. -/
abbrev PotentialState := ℝ × ℝ × ℝ

/-- The actual potential as a scalar function on the physical state space. -/
def statePotential (γ : ℝ) (σ : ℝ → ℝ) (z : PotentialState) : ℝ :=
  stateValue γ σ z.1 z.2.1 z.2.2

/-- C¹ regularity is proved for the actual fractional-power Bellman potential.
No graph differential equation is needed for regularity alone. -/
theorem contDiffAt_statePotential {γ : ℝ} {σ : ℝ → ℝ} {z : PotentialState}
    (hγ : γ ≠ 0) (hφ : z.1 ≠ 0) (hp : z.2.1 ≠ 0) (hK : z.2.2 ≠ 0)
    (hσ : ContDiffAt ℝ 1 σ (z.1 * z.2.1 / z.2.2))
    (hs : 0 < σ (z.1 * z.2.1 / z.2.2)) :
    ContDiffAt ℝ 1 (statePotential γ σ) z := by
  have hφc : ContDiffAt ℝ 1 (fun w : PotentialState => w.1) z := by fun_prop
  have hpc : ContDiffAt ℝ 1 (fun w : PotentialState => w.2.1) z := by fun_prop
  have hKc : ContDiffAt ℝ 1 (fun w : PotentialState => w.2.2) z := by fun_prop
  have hr := (hφc.mul hpc).div hKc hK
  have hsc := hσ.comp z hr
  have hroot := hsc.sqrt (ne_of_gt hs)
  have hrn : z.1 * z.2.1 / z.2.2 ≠ 0 := div_ne_zero (mul_ne_zero hφ hp) hK
  have hden : 2 * γ * (z.1 * z.2.1 / z.2.2) * Real.sqrt (σ (z.1 * z.2.1 / z.2.2)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hγ) hrn)
      (ne_of_gt (Real.sqrt_pos.2 hs))
  exact (hKc.rpow_const_of_ne hK).mul
    (((hr.add hsc).sub contDiffAt_const).div
      ((contDiffAt_const.mul hr).mul hroot) hden)

/-- The actual state potential is BV along every BV physical path staying
in a compact positive state domain where the graph is C¹ and positive. -/
theorem boundedVariation_statePotential {γ : ℝ} {σ : ℝ → ℝ}
    {z : ℝ → PotentialState} {s : Set PotentialState}
    (hγ : γ ≠ 0) (hz : BoundedVariationOn z univ)
    (hc : IsCompact s) (hmap : MapsTo z univ s)
    (hpos : ∀ w ∈ s, 0 < w.1 ∧ 0 < w.2.1 ∧ 0 < w.2.2)
    (hσ : ∀ w ∈ s, ContDiffAt ℝ 1 σ (w.1 * w.2.1 / w.2.2))
    (hσpos : ∀ w ∈ s, 0 < σ (w.1 * w.2.1 / w.2.2)) :
    BoundedVariationOn (statePotential γ σ ∘ z) univ := by
  apply boundedVariation_comp_contDiff hz hc hmap
  intro w hw
  obtain ⟨hφ, hp, hK⟩ := hpos w hw
  exact contDiffAt_statePotential hγ hφ.ne' hp.ne' hK.ne' (hσ w hw) (hσpos w hw)

/-- Every countable family of actual state impulses has summable exact losses.
The proof first establishes BV of W(z), then uses its Stieltjes jumps; the
summability is not assumed as an atomic-decomposition hypothesis.
Article: main_krylov, apC:lem:fund, justification of the atom sum. -/
theorem summable_impulseLoss_of_bv {ι : Type*} [Countable ι]
    {γ : ℝ} {σ : ℝ → ℝ} {z : ℝ → PotentialState} {s : Set PotentialState}
    (hγ : γ ≠ 0) (hz : BoundedVariationOn z univ)
    (hc : IsCompact s) (hmap : MapsTo z univ s)
    (hpos : ∀ w ∈ s, 0 < w.1 ∧ 0 < w.2.1 ∧ 0 < w.2.2)
    (hσ : ∀ w ∈ s, ContDiffAt ℝ 1 σ (w.1 * w.2.1 / w.2.2))
    (hσpos : ∀ w ∈ s, 0 < σ (w.1 * w.2.1 / w.2.2))
    (e : ι → ℝ) (he : Function.Injective e) (φ p K m : ι → ℝ)
    (hleft : ∀ i, Function.leftLim z (e i) = (φ i, p i, K i))
    (hright : ∀ i, Function.rightLim z (e i) =
      (φ i, p i + m i * φ i, K i + m i * φ i ^ 2))
    (hm : ∀ i, 0 ≤ m i)
    (hgraph : ∀ i, ∀ u ∈ Icc 0 (m i),
      FeedbackGraphAt γ σ (φ i * (p i + u * φ i) / (K i + u * φ i ^ 2))) :
    Summable (fun i => impulseLoss γ σ (φ i) (p i) (K i) (m i)) := by
  have hq := boundedVariation_statePotential hγ hz hc hmap hpos hσ hσpos
  have hregular : ∀ w ∈ s, ContDiffAt ℝ 1 (statePotential γ σ) w := by
    intro w hw
    obtain ⟨hφ, hp, hK⟩ := hpos w hw
    exact contDiffAt_statePotential hγ hφ.ne' hp.ne' hK.ne' (hσ w hw) (hσpos w hw)
  have hjump : ∀ i, Function.rightLim (statePotential γ σ ∘ z) (e i) -
      Function.leftLim (statePotential γ σ ∘ z) (e i) =
        -impulseLoss γ σ (φ i) (p i) (K i) (m i) := by
    intro i
    have hlmem := leftLim_mem_of_closed hz hc.isClosed hmap (e i)
    have hrmem := rightLim_mem_of_closed hz hc.isClosed hmap (e i)
    rw [rightLim_comp hz (hregular _ hrmem).continuousAt,
      leftLim_comp hz (hregular _ hlmem).continuousAt, hright, hleft]
    have hlpos : 0 < φ i ∧ 0 < p i ∧ 0 < K i := by
      simpa only [hleft i] using hpos _ hlmem
    have hdec := impulse_potential_decrement hγ hlpos.1 hlpos.2.1 hlpos.2.2
      (hm i) (hgraph i)
    dsimp only [statePotential]
    linarith
  have hsum := (hasSum_potential_jumps hq e he).summable.neg
  simpa only [hjump, neg_neg] using hsum

end
end krylov.ContinuumBV
