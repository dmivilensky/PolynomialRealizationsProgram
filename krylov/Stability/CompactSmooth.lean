import krylov.Stability.WeightedCompactTaylor

/-!
Article: main_krylov, lem:U(a), finite-order smooth compact reference maps.
Use: apply the proved compact integral Taylor theorem to actual outputs
whose finite-order regularity has been derived at every true reference.
Source: finite-order ContDiffAt.eventually and the existing genuine compact Taylor tube.
-/

namespace krylov.Stability
noncomputable section
open Set
open scoped Topology
variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Genuine finite-order smoothness at every compact reference yields one actual Taylor tube and constant for all orders through r.
Use: actual C² trial methods need no analytic regularity or supplied global smooth domain.
Article: main_krylov, lem:U(a,d).
Proof: finite-order smoothness persists on a true neighborhood of each
reference. Its open locus contains the compact reference set and supplies
the actual smooth domain to the proved compact integral Taylor theorem. -/
theorem compact_smooth_taylor (f : X → F) (r : ℕ) (K : Set X) (hK : IsCompact K)
    (hf : ∀ x∈K, ContDiffAt ℝ r f x) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ‖f (x+h)-taylorPolynomial f k x h‖≤C*‖h‖^k := by
  -- The open domain is derived from true finite-order output regularity at real references.
  let U := interior {x | ContDiffAt ℝ r f x}
  have hsub : K⊆U := fun x hx => mem_interior_iff_mem_nhds.mpr ((hf x hx).eventually (by simp))
  apply compact_taylor_remainders f r U K isOpen_interior hK hsub
  intro x hx
  have ht : ContDiffAt ℝ r f x := interior_subset hx
  exact ht.contDiffWithinAt

/-- The actual finite-order compact Taylor tube admits a genuine positive continuous reference-error factor.
Use: true C² XRFC outputs inherit the same weighted compact-reference convention as FC and RFC.
Article: main_krylov, lem:U(a,d).
Proof: the true finite-order smooth locus gives an actual open domain;
the existing compact weighted Taylor theorem absorbs the genuine positive
reference-error weight by its attained compact minimum. -/
theorem compact_smooth_weighted_taylor (f : X → F) (e : X → ℝ) (r : ℕ) (K : Set X)
    (hK : IsCompact K) (hf : ∀ x∈K, ContDiffAt ℝ r f x)
    (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ‖f (x+h)-taylorPolynomial f k x h‖≤C*‖h‖^k*e x := by
  -- Finite smoothness, rather than an analytic trial assumption, supplies the real common tube.
  let U := interior {x | ContDiffAt ℝ r f x}
  have hsub : K⊆U := fun x hx => mem_interior_iff_mem_nhds.mpr ((hf x hx).eventually (by simp))
  apply compact_weighted_taylor f e r U K isOpen_interior hK hsub _ he hepos
  intro x hx
  have ht : ContDiffAt ℝ r f x := interior_subset hx
  exact ht.contDiffWithinAt

end
end krylov.Stability
