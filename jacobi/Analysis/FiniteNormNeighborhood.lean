import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
Article: jacobi, Lemma E.1.
Use: the original finitely many Bessel branches and their pairwise differences are combined with the proved uniform tail geometry in Lemma E.1.
-/
namespace jacobi.Analysis
noncomputable section
open Filter
open scoped Topology

/-- Finitely many actual continuous nonzero complex values retain one positive norm lower bound on a common neighborhood.
Use: the original finitely many Bessel branches and their pairwise differences are combined with the proved uniform tail geometry in Lemma E.1.
Article: jacobi, Lemma E.1.
Source: the elementary finite minimum and continuity argument.
Proof: minimize the actual center norms over the finite nonempty index type. Half this positive minimum is below every original center norm; each continuous norm stays above it nearby, and finiteness intersects those genuine neighborhoods. -/
theorem finite_norm_neighborhood {ι : Type*} [Finite ι] [Nonempty ι]
    {f : ι → ℂ → ℂ} {a0 : ℂ} (hc : ∀ i,ContinuousAt (f i) a0) (hn : ∀ i,f i a0≠0) :
    ∃ d : ℝ,0<d ∧ ∀ᶠ a in 𝓝 a0,∀ i,d≤‖f i a‖ := by
  -- The minimum is taken only over the actual finite family of genuine center values.
  obtain ⟨i0,hmin⟩ := Finite.exists_min (fun i => ‖f i a0‖)
  have hp : 0<‖f i0 a0‖ := norm_pos_iff.mpr (hn i0)
  refine ⟨‖f i0 a0‖/2,half_pos hp,eventually_all.mpr (fun i => ?_)⟩
  exact ((hc i).norm.eventually_const_lt ((half_lt_self hp).trans_le (hmin i))).mono (fun _ h => h.le)

end
end jacobi.Analysis
