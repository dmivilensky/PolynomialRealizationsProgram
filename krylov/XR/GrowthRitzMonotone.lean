import krylov.XR.GrowthRitz

/-!
Article: main_krylov, proof of thm:XR, persistent strict upper margin.
Use: once the real running bound has been set, both ModelSteps preserve
it and can only increase its upper endpoint. Thus one strict upper margin
at a real iterate persists uniformly, including after a rejected probe.
Source: the literal max update, with no spectral accuracy hypothesis.
-/
namespace krylov.XR
noncomputable section
variable {n : ℕ}

theorem algorithmModel_bounds_some (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) (b : ℝ × ℝ) (hb : S.bounds = some b) :
    ∃ c, (algorithmModel P S).bounds = some c ∧ b.2 ≤ c.2 := by
  classical
  rw [algorithmModel_bounds]
  split
  · exact ⟨b, hb, le_rfl⟩
  · simp only [updateBounds, hb]
    exact ⟨_, rfl, le_max_left _ _⟩

theorem outerSearch_bounds_some (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) (b : ℝ × ℝ) (hb : S.bounds = some b) :
    ∃ c, (outerSearch (algorithmModel P) f G P.armijo S).bounds = some c ∧ b.2 ≤ c.2 := by
  classical
  obtain ⟨c, hc, hbc⟩ := algorithmModel_bounds_some P S b hb
  unfold outerSearch
  dsimp only
  split
  · exact ⟨c, hc, hbc⟩
  · have hp : (firstProbeState (algorithmModel P) f G S).bounds = some c := hc
    obtain ⟨d, hd, hcd⟩ := algorithmModel_bounds_some P
      (firstProbeState (algorithmModel P) f G S) c hp
    exact ⟨d, hd, hbc.trans hcd⟩

theorem outerAdvance_bounds_some (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) (b : ℝ × ℝ) (hb : S.bounds = some b) :
    ∃ c, (outerAdvance P n (algorithmModel P) f G S).bounds = some c ∧ b.2 ≤ c.2 := by
  classical
  unfold outerAdvance
  split
  · exact ⟨b, hb, le_rfl⟩
  · exact outerSearch_bounds_some P f G S b hb

/-- A single actually set running upper bound gives a uniform lower bound
for every later running endpoint. -/
theorem algorithmRun_bounds_some_monotone (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (K : ℕ)
    (b : ℝ × ℝ) (hb : (algorithmRun P f G x₀ bounds K).bounds = some b) :
    ∀ k, K ≤ k → ∃ c, (algorithmRun P f G x₀ bounds k).bounds = some c ∧ b.2 ≤ c.2 := by
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction j with
  | zero => exact ⟨b, hb, le_rfl⟩
  | succ j ih =>
    obtain ⟨c, hc, hbc⟩ := ih
    obtain ⟨d, hd, hcd⟩ := outerAdvance_bounds_some P f G
      (algorithmRun P f G x₀ bounds (K+j)) c hc
    exact ⟨d, hd, hbc.trans hcd⟩

/-- A real strict upper bound on the stored running estimate remains a
uniform strict class margin at every later actual ModelStep. -/
theorem algorithmRun_model_upper_margin (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (K : ℕ)
    (b : ℝ × ℝ) (hb : (algorithmRun P f G x₀ bounds K).bounds = some b) :
    ∀ k, K ≤ k → ∃ c,
      (algorithmModel P (algorithmRun P f G x₀ bounds k)).bounds = some c ∧ b.2 ≤ c.2 := by
  intro k hk
  obtain ⟨c, hc, hbc⟩ := algorithmRun_bounds_some_monotone P f G x₀ bounds K b hb k hk
  obtain ⟨d, hd, hcd⟩ := algorithmModel_bounds_some P (algorithmRun P f G x₀ bounds k) c hc
  exact ⟨d, hd, hbc.trans hcd⟩

end
end krylov.XR
