import krylov.XR.MemorySuffix

/-!
Article: main_krylov, proof of thm:grow, actual one-step memory forgetting.
Use: prove finite forgetting for the real suffix/probe/accepted-pair control
flow. Goodness refers to actual observed segments; no model accuracy or
eventual branch decision is a certificate stored by the executor.
Source: the proved chronological suffix identities and exact bad-prefix
potential, with one genuinely new positive accepted observation per step.
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuinely good optional rejected probe does not enlarge the old bad
prefix, whether or not its actual positive-curvature guard stores it. -/
theorem firstGoodSuffix_appendPositive (Q : PairObservation E → Prop)
    (W : List (PairObservation E)) (P : PairObservation E) (hP : Q P) :
    firstGoodSuffix Q (appendPositive W P) = firstGoodSuffix Q W := by
  classical
  unfold appendPositive
  split
  · exact firstGoodSuffix_append_good Q W P hP
  · rfl

/-- An optional genuine good probe cannot increase the forgetting
potential when there is one free physical observation slot. -/
theorem forgettingPotential_appendPositive_le (capacity : ℕ) (Q : PairObservation E → Prop)
    (W : List (PairObservation E)) (P : PairObservation E) (hP : Q P) (hlen : W.length < capacity) :
    forgettingPotential capacity Q (appendPositive W P) ≤ forgettingPotential capacity Q W := by
  classical
  unfold appendPositive
  split
  · have h := forgettingPotential_append_good capacity Q W P hP hlen
    omega
  · exact le_rfl

/-- Literal one-probe search preserves the old-prefix order and cannot
postpone forgetting while any old bad observation remains. -/
theorem outerSearch_forgetting (model : State E → ModelResult E) (bound : ℕ)
    (hdrop : ∀ S : State E, ∃ o, (model S).pairs = S.pairs.drop o)
    (hmodel : ∀ S : State E, (model S).pairs.length ≤ bound)
    (f : E → ℝ) (G : E → E) (sigma : ℝ) (S : State E)
    (Q : PairObservation E → Prop) (hlen : S.pairs.length ≤ bound + 1)
    (hprobe : Q (observedTrialPair f G S ((model S).safeDirection S))) :
    firstGoodSuffix Q (outerSearch model f G sigma S).pairs ≤ firstGoodSuffix Q S.pairs ∧
      (firstGoodSuffix Q (outerSearch model f G sigma S).pairs ≠ 0 →
        forgettingPotential (bound + 1) Q (outerSearch model f G sigma S).pairs ≤
          forgettingPotential (bound + 1) Q S.pairs) := by
  classical
  let M₀ := model S
  let P₀ := observedTrialPair f G S (M₀.safeDirection S)
  let S₁ := { M₀.updateState S with pairs := appendPositive M₀.pairs P₀ }
  obtain ⟨o₀, ho₀⟩ := hdrop S
  have hbad₀ : firstGoodSuffix Q M₀.pairs ≤ firstGoodSuffix Q S.pairs := by
    rw [ho₀, firstGoodSuffix_drop]
    omega
  have hpotential₀ (hbad : firstGoodSuffix Q M₀.pairs ≠ 0) :
      forgettingPotential (bound + 1) Q M₀.pairs = forgettingPotential (bound + 1) Q S.pairs := by
    rw [ho₀] at hbad ⊢
    exact forgettingPotential_drop_of_bad _ Q S.pairs hlen o₀ hbad
  unfold outerSearch
  dsimp only
  split
  · exact ⟨hbad₀, fun hbad => (hpotential₀ hbad).le⟩
  · obtain ⟨o₁, ho₁⟩ := hdrop S₁
    have hprobeGood : Q P₀ := hprobe
    have hbadProbe : firstGoodSuffix Q S₁.pairs = firstGoodSuffix Q M₀.pairs :=
      firstGoodSuffix_appendPositive Q M₀.pairs P₀ hprobeGood
    have hlen₀ : M₀.pairs.length < bound + 1 := Nat.lt_succ_of_le (hmodel S)
    have hlen₁ : S₁.pairs.length ≤ bound + 1 :=
      (appendPositive_length_le M₀.pairs P₀).trans (Nat.add_le_add_right (hmodel S) 1)
    have hbad₁ : firstGoodSuffix Q (model S₁).pairs ≤ firstGoodSuffix Q M₀.pairs := by
      rw [ho₁, firstGoodSuffix_drop, ← hbadProbe]
      omega
    refine ⟨hbad₁.trans hbad₀, ?_⟩
    intro hbad
    change firstGoodSuffix Q (model S₁).pairs ≠ 0 at hbad
    change forgettingPotential (bound + 1) Q (model S₁).pairs ≤ _
    have hbadOld : firstGoodSuffix Q M₀.pairs ≠ 0 := by omega
    have heq : forgettingPotential (bound + 1) Q (model S₁).pairs =
        forgettingPotential (bound + 1) Q S₁.pairs := by
      rw [ho₁] at hbad ⊢
      exact forgettingPotential_drop_of_bad _ Q S₁.pairs hlen₁ o₁ hbad
    exact heq.le.trans ((forgettingPotential_appendPositive_le _ Q M₀.pairs P₀ hprobeGood hlen₀).trans
      (hpotential₀ hbadOld).le)

/-- A real nonstationary outer step with a new good positive accepted
pair strictly lowers the old-data potential whenever any bad data remain.
The actual rejected probe and anchor transport are included. -/
theorem outerAdvance_forgetting (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (bound : ℕ)
    (hdrop : ∀ S : State E, ∃ o, (model S).pairs = S.pairs.drop o)
    (hmodel : ∀ S : State E, (model S).pairs.length ≤ bound)
    (f : E → ℝ) (G : E → E) (S : State E) (hne : S.gradient ≠ 0)
    (Q : PairObservation E → Prop) (hlen : S.pairs.length ≤ bound + 1)
    (htransport : ∀ a u, Q (a.transport u) ↔ Q a)
    (hprobe : Q (observedTrialPair f G S ((model S).safeDirection S)))
    (haccepted : Q (observedTrialPair f G S
      ((outerSearch model f G P.armijo S).length • (outerSearch model f G P.armijo S).direction)))
    (hpositive : positivePair (observedTrialPair f G S
      ((outerSearch model f G P.armijo S).length • (outerSearch model f G P.armijo S).direction))) :
    firstGoodSuffix Q (outerAdvance P dimension model f G S).pairs ≤ firstGoodSuffix Q S.pairs ∧
      (firstGoodSuffix Q (outerAdvance P dimension model f G S).pairs ≠ 0 →
        forgettingPotential (bound + 1) Q (outerAdvance P dimension model f G S).pairs + 1 ≤
          forgettingPotential (bound + 1) Q S.pairs) := by
  classical
  let R := outerSearch model f G P.armijo S
  let step := R.length • R.direction
  let pair := observedTrialPair f G S step
  have hsearch := outerSearch_forgetting model bound hdrop hmodel f G P.armijo S Q hlen hprobe
  have hlenR : R.pairs.length < bound + 1 := Nat.lt_succ_of_le
    (outerSearch_pairs_length_le model bound hmodel f G P.armijo S)
  have hnew : appendPositive R.pairs pair = R.pairs ++ [pair] := by
    unfold appendPositive
    exact ite_eq_left hpositive
  have hpairs : (outerAdvance P dimension model f G S).pairs =
      (R.pairs ++ [pair]).map (fun a => a.transport step) := by
    simp only [outerAdvance, ite_eq_right hne]
    change (appendPositive R.pairs pair).map _ = _
    rw [hnew]
  have hbad : firstGoodSuffix Q (outerAdvance P dimension model f G S).pairs =
      firstGoodSuffix Q R.pairs := by
    rw [hpairs, firstGoodSuffix_map Q _ _ (fun a => htransport a step),
      firstGoodSuffix_append_good Q R.pairs pair haccepted]
  refine ⟨hbad.le.trans hsearch.1, ?_⟩
  intro hstill
  have hstillR : firstGoodSuffix Q R.pairs ≠ 0 := by rwa [hbad] at hstill
  have hpot : forgettingPotential (bound + 1) Q (outerAdvance P dimension model f G S).pairs + 1 =
      forgettingPotential (bound + 1) Q R.pairs := by
    rw [hpairs, forgettingPotential_map _ Q _ _ (fun a => htransport a step)]
    exact forgettingPotential_append_good _ Q R.pairs pair haccepted hlenR
  exact hpot.le.trans (hsearch.2 hstillR)

end
end krylov.XR
