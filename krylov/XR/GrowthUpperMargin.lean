import krylov.XR.GrowthRitzMonotone
import krylov.XR.LocalMemory

/-!
Article: main_krylov, thm:XR, the real running upper-bound hypothesis.
Use: turn a strict upper estimate computed by an actual ModelStep into
the strict cached bound used by the source floor theorem. Actual stopping
is excluded by accepted convergence to a distinct limit, without assuming
nonzero cached gradients. The rejected-probe second update is included.
-/
namespace krylov.XR
noncomputable section
open Filter Topology
variable {n : ℕ}

theorem outerAdvance_bounds_some_of_model (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) (hg : S.gradient ≠ 0)
    (b : ℝ × ℝ) (hb : (algorithmModel P S).bounds = some b) :
    ∃ c, (outerAdvance P n (algorithmModel P) f G S).bounds = some c ∧ b.2 ≤ c.2 := by
  classical
  unfold outerAdvance
  rw [ite_eq_right hg]
  unfold outerSearch
  dsimp only
  split
  · exact ⟨b, hb, le_rfl⟩
  · exact algorithmModel_bounds_some P (firstProbeState (algorithmModel P) f G S) b hb

/-- A literal stopped state would force the accepted limit to be this
same point; original G1's distinctness therefore excludes every stop. -/
theorem algorithmRun_gradient_ne_zero_of_distinct_limit (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center) (k : ℕ) :
    (algorithmRun P f G x₀ bounds k).gradient ≠ 0 := by
  classical
  intro hz
  let S := algorithmRun P f G x₀ bounds k
  have hfix (j : ℕ) : algorithmRun P f G x₀ bounds (k+j) = S := by
    induction j with
    | zero => rfl
    | succ j ih =>
      change outerAdvance P n (algorithmModel P) f G (algorithmRun P f G x₀ bounds (k+j)) = S
      rw [ih]
      exact ite_eq_left hz
  have ht : Tendsto (fun j => (algorithmRun P f G x₀ bounds (k+j)).point) atTop (𝓝 center) := by
    have hh := hconv.comp (tendsto_add_atTop_nat k)
    change Tendsto (fun j => (algorithmRun P f G x₀ bounds (j+k)).point) atTop (𝓝 center) at hh
    simpa only [Nat.add_comm] using hh
  have hc : Tendsto (fun j => (algorithmRun P f G x₀ bounds (k+j)).point) atTop (𝓝 S.point) := by
    simpa only [hfix] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => S.point) atTop (𝓝 S.point))
  exact hne k (tendsto_nhds_unique hc ht)

/-- The paper's actual ModelStep upper margin supplies a true cached
strict margin one accepted iteration later, regardless of a rejected probe. -/
theorem algorithmRun_cache_upper_margin (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold) (k : ℕ)
    (hstrict : threshold < boundsUpper (algorithmModel P (algorithmRun P f G x₀ bounds k)).bounds) :
    ∃ b, (algorithmRun P f G x₀ bounds (k+1)).bounds = some b ∧ threshold < b.2 := by
  let S := algorithmRun P f G x₀ bounds k
  have hsome : ∃ b, (algorithmModel P S).bounds = some b ∧ threshold < b.2 := by
    cases hb : (algorithmModel P S).bounds with
    | none =>
      change threshold < boundsUpper (algorithmModel P S).bounds at hstrict
      rw [hb] at hstrict
      change threshold < 0 at hstrict
      exact (not_lt_of_ge hthreshold hstrict).elim
    | some b =>
      change threshold < boundsUpper (algorithmModel P S).bounds at hstrict
      rw [hb] at hstrict
      exact ⟨b, rfl, hstrict⟩
  obtain ⟨b, hb, hmargin⟩ := hsome
  obtain ⟨c, hc, hbc⟩ := outerAdvance_bounds_some_of_model P f G S
    (algorithmRun_gradient_ne_zero_of_distinct_limit P f G x₀ center bounds hconv hne k) b hb
  exact ⟨c, hc, hmargin.trans_le hbc⟩

end
end krylov.XR
