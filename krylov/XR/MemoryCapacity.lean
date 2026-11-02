import krylov.XR.Execution

/-!
Article: main_krylov, alg:xr and thm:grow, actual capacity bookkeeping.
Use: prove the literal halving/additive-growth state remains in its original
capacity interval and its clean counter never reaches its trigger value.
Source: elementary natural-number arithmetic applied to the displayed rule.
-/

namespace krylov.XR
noncomputable section

/-- The actual memory rule preserves the configured capacity interval. -/
theorem updateCapacity_interval (P : Parameters) (dimension cap clean p o j : ℕ)
    (hlo : P.initialCapacity ≤ cap) (hhi : cap ≤ P.maximumCapacity) :
    P.initialCapacity ≤ (updateCapacity P dimension cap clean p o j).1 ∧
      (updateCapacity P dimension cap clean p o j).1 ≤ P.maximumCapacity := by
  unfold updateCapacity
  split_ifs <;> (try dsimp only) <;> (try split_ifs) <;> (try dsimp only) <;> constructor <;> omega

/-- The clean counter resets at its trigger, rather than overshooting it. -/
theorem updateCapacity_clean_lt (P : Parameters) (dimension cap clean p o j : ℕ)
    (hq : 0 < P.cleanPeriod) (hclean : clean < P.cleanPeriod) :
    (updateCapacity P dimension cap clean p o j).2 < P.cleanPeriod := by
  unfold updateCapacity
  split_ifs <;> (try dsimp only) <;> (try split_ifs) <;> (try dsimp only) <;> omega

/-- On a full clean first-trial iteration the literal next counter/capacity
is exactly the printed additive-growth update. -/
theorem updateCapacity_clean (P : Parameters) (dimension cap clean : ℕ) :
    updateCapacity P dimension cap clean (min cap dimension) 0 1 =
      if clean + 1 = P.cleanPeriod then
        (min (cap + P.initialCapacity) P.maximumCapacity, 0)
      else (cap, clean + 1) := by
  simp [updateCapacity]

end
end krylov.XR
