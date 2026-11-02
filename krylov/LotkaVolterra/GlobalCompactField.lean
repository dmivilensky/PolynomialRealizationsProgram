import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
Uniform bounds and Lipschitz constants on a compact parameter rectangle.
This standard compactness argument avoids deriving unnecessarily explicit
constants for the rational saddle equation. Source: the extreme-value and
mean-value theorems in mathlib.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal

theorem exists_uniform_bounds_on_rectangle
    {F D : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ ↦ F p.1 p.2) (Icc a b ×ˢ Icc c d))
    (hD : ContinuousOn (fun p : ℝ × ℝ ↦ D p.1 p.2) (Icc a b ×ˢ Icc c d))
    (hd : ∀ p ∈ Icc a b, ∀ x ∈ Icc c d, HasDerivAt (F p) (D p x) x) :
    ∃ L K : ℝ≥0, (∀ p ∈ Icc a b, ∀ x ∈ Icc c d, ‖F p x‖ ≤ L) ∧
      ∀ p ∈ Icc a b, LipschitzOnWith K (F p) (Icc c d) := by
  have hcompact : IsCompact (Icc a b ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨L, hL⟩ := hcompact.bddAbove_image hc.norm
  obtain ⟨K, hK⟩ := hcompact.bddAbove_image hD.norm
  refine ⟨Real.toNNReal L, Real.toNNReal K, ?_, fun p hp ↦ ?_⟩
  · intro p hp x hx
    exact (hL ⟨(p, x), ⟨hp, hx⟩, rfl⟩).trans (Real.le_coe_toNNReal _)
  · apply (convex_Icc c d).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx ↦ (hd p hp x hx).hasDerivWithinAt)
    intro x hx
    have hh : ‖D p x‖ ≤ (Real.toNNReal K : ℝ) :=
      (hK ⟨(p, x), ⟨hp, hx⟩, rfl⟩).trans (Real.le_coe_toNNReal _)
    exact_mod_cast hh

end
end krylov.LotkaVolterra
