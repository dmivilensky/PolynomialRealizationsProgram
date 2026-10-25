import polyak.Boundary.P5.Spectrum
import polyak.Boundary.P5.LocalBounds
import polyak.Boundary.P5.LocalPrefix

/-!
Article: Theorem p5local, feasibility of the actual central two-atom spectrum.
Use: the finite prefix and the uniform infinite tail meet at lag 24.
-/
noncomputable section
namespace polyak.Boundary.P5
open Spectral Filter
open scoped Topology

/-- Article: the concrete prefix and tail imply every original spectral inequality. -/
theorem feasibleU_of_tail_prefix (Z : Coordinates) {h t : ℝ}
    (hx : -1≤branchX h Z ∧ branchX h Z≤1) (hy : -1≤Z 2 ∧ Z 2≤1)
    (hb : TailBounds h (branchU h Z) (h*Z 3) (h*Z 4) ⟨branchX h Z,hx⟩ ⟨Z 2,hy⟩)
    (ht : t≠0) (hcosh : Real.cosh t=1+h)
    (hprefix : ∀ n : ℕ, 1≤n → n<24 → ∀ σ : ℝ, (σ= -1 ∨ σ=1) →
      0≤actualPrimal h Z n σ) :
    FeasibleU (branchU h Z) t
      (twoAtomSpectrum (h*Z 3) hb.p_nonneg hb.p_le_one ⟨branchX h Z,hx⟩ ⟨Z 2,hy⟩)
      (h*Z 4/Real.sinh t) := by
  apply feasibleU_twoAtom_of_normalized (h*Z 3) hb.p_nonneg hb.p_le_one
    ⟨branchX h Z,hx⟩ ⟨Z 2,hy⟩ (branchU h Z) t (h*Z 4) ht
  · have hs := hb.star_gt
    rw [abs_charge_cosh hcosh] at hs
    linarith
  · intro n hn σ hσ
    rw [hcosh]
    by_cases hn24 : n<24
    · simpa only [actualPrimal,branchU,branchX,mul_assoc] using hprefix n hn hn24 σ hσ
    · exact (normalized_twoAtom_pos hb n (by omega) σ hσ.symm).le

/-- Article: the actual analytic P5 branch has a genuine feasible probability spectrum. -/
theorem eventually_localBranch_feasible :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∃ ν : Spectrum,
      FeasibleU (branchU h (localBranch h)) (Real.arcosh (1+h)) ν
        (h*localBranch h 4/Real.sinh (Real.arcosh (1+h))) := by
  filter_upwards [eventually_tailBounds localBranch_analyticAt.continuousAt localBranch_zero,
    eventually_branch_primal_prefix] with h hb hprefix
  obtain ⟨hx,hy,hb⟩ := hb
  have ht : 0<Real.arcosh (1+h) := Real.arcosh_pos (by linarith [hb.h_pos])
  have hcosh : Real.cosh (Real.arcosh (1+h))=1+h := Real.cosh_arcosh (by linarith [hb.h_pos])
  exact ⟨_,feasibleU_of_tail_prefix (localBranch h) hx hy hb ht.ne' hcosh hprefix⟩

end polyak.Boundary.P5
