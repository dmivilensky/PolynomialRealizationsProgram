import krylov.Methods.ObservedRules
import krylov.Stability.WeightedCompactTaylor
import krylov.Stability.HomogeneousTaylor

/-!
Article: main_krylov, lem:U(a,c,d), smooth finite observed-program remainders.
Use: obtain compact Taylor and homogeneous-cone bounds for actual finite
oracle programs directly from their primitive observed coefficient hypotheses.
Source: the actual query-program smoothness induction and the proved compact
integral Taylor theorem; openness uses finite-order ContDiffAt.eventually.
-/

namespace krylov.Stability
noncomputable section
open Set krylov.Methods
open scoped Topology
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- The actual output of every smooth finite observed-coefficient oracle program has compact-uniform weighted Taylor bounds.
Use: derives the general smooth finite-program instance of lem:U from coefficient regularity rather than assuming a cycle expansion.
Article: main_krylov, def:classes and lem:U(a,d).
Proof: real query induction establishes C^r at every compact reference from
only primitive operator/data smoothness and actual coefficient smoothness.
Finite-order regularity has an open locus; the genuine compact weighted
integral Taylor theorem applies on its interior. -/
theorem observedProgram_compact_taylor {m : ℕ} (P : ObservedProgram E m)
    (A : X → ℕ → E →L[ℝ] E) (data : X → Fin m → E) (offset r : ℕ)
    (e : X → ℝ) (K : Set X) (hK : IsCompact K)
    (hA : ∀ x∈K, ∀ j, ContDiffAt ℝ r (fun p => A p j) x)
    (hd : ∀ x∈K, ContDiffAt ℝ r data x)
    (hP : ∀ x∈K, P.RegularAt r (A x) (data x) offset)
    (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) :
    let Φ := fun p => P.run (A p) (data p) offset
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ‖Φ (x+h)-taylorPolynomial Φ k x h‖≤C*‖h‖^k*e x := by
  -- The smooth locus is derived for the true output, not supplied as a trajectory premise.
  let Φ := fun p => P.run (A p) (data p) offset
  let U := interior {x | ContDiffAt ℝ r Φ x}
  have hΦ : ∀ x∈K, ContDiffAt ℝ r Φ x := fun x hx =>
    P.run_contDiffAt A data x offset (hA x hx) (hd x hx) (hP x hx)
  have hsub : K⊆U := fun x hx => mem_interior_iff_mem_nhds.mpr ((hΦ x hx).eventually (by simp))
  apply compact_weighted_taylor Φ e r U K isOpen_interior hK hsub _ he hepos
  intro x hx
  have ht : ContDiffAt ℝ r Φ x := interior_subset hx
  exact ht.contDiffWithinAt

end
end krylov.Stability
