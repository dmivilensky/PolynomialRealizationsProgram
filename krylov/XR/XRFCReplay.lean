import krylov.XR.XRFCFunction

/-!
Article: main_krylov, lem:xr-local, exact finite-branch replay.
Use: identify each literal accepted XR update with the genuine full-memory
scalar XRFC or XRFC-F update once its actual local decisions are proved
stable. The same actual computed trial rule is used on both sides.
Source: exact data-only ModelStep decomposition and real endpoint updates.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace
variable {n : ℕ}

/-- The literal spectral-bound projection is its update from the actual
retained pairs; this identity makes no successful-test assumption. -/
theorem algorithmModel_bounds (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
    (algorithmModel P S).bounds =
      if (algorithmModel P S).pairs.length = 0 then S.bounds
      else updateBounds P.inflation S.bounds (algorithmModel P S).pairs := by
  rfl

/-- The scalar gate is exactly inactive on the whole true value model
when all genuinely observed oversized-term inequalities hold. -/
theorem storedValueModel_eq_exact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (W : List (PairObservation E))
    (hgate : ∀ i : Fin W.length,
      |12 * storedSplit W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2) :
    storedValueModel W = storedExactValueModel W := by
  unfold storedValueModel storedExactValueModel
  congr 1
  apply congrArg diagonal
  funext i
  exact storedValueTerm_eq_raw W i (hgate i)

/-- On the true value-gate branch XR selects exactly the model used by
the full-memory scalar virtual executor. -/
theorem selectedModel_eq_fullVirtual (P : Parameters)
    (W : List (PairObservation (EuclideanSpace ℝ (Fin n))))
    (hvalues : P.valuesEnabled = true →
      (∀ i : Fin W.length, |12 * storedSplit W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2) ∧
        correctedWindowPasses P.windowThreshold W) :
    selectedModel P W = fullVirtualSelectedModel P W := by
  classical
  cases he : P.valuesEnabled with
  | false => simp only [fullVirtualSelectedModel, he, Bool.false_eq_true, ite_false, selectedModel_values_off P he]
  | true =>
    have hv := hvalues he
    rw [selectedModel, ite_eq_left ⟨he, hv.2⟩, storedValueModel_eq_exact W hv.1]
    simp only [fullVirtualSelectedModel, he, ite_true]

/-- A complete retained history with the same real scalar gates has
exactly the same computed candidate as the full-memory virtual rule. -/
theorem algorithmModel_direction_eq_fullVirtual (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n)))
    (hret : (algorithmModel P S).pairs = S.pairs)
    (hvalues : P.valuesEnabled = true →
      (∀ i : Fin S.pairs.length, |12 * storedSplit S.pairs i * (S.pairs.get i).valueDefect| ≤
        storedPairing S.pairs i i / 2) ∧ correctedWindowPasses P.windowThreshold S.pairs) :
    (algorithmModel P S).direction = fullVirtualStep P (algorithmTrialParameter P) S := by
  classical
  by_cases hp : S.pairs.length = 0
  · have hp' : (algorithmModel P S).pairs.length = 0 := by rw [hret]; exact hp
    rw [algorithmModel_empty_direction P S hp']
    exact (ite_eq_left hp).symm
  · have hp' : (algorithmModel P S).pairs.length ≠ 0 := by rw [hret]; exact hp
    have hu := algorithmModel_direction_decomposition P S hp'
    rw [hret, selectedModel_eq_fullVirtual P S.pairs hvalues] at hu
    rw [hu]
    exact (ite_eq_right hp).symm

/-- The exact candidate dictionary also applies whenever equality of the
two actually selected matrices has been established directly, as on
quadratic data where every value defect vanishes. -/
theorem algorithmModel_direction_eq_fullVirtual_of_model (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n)))
    (hret : (algorithmModel P S).pairs = S.pairs)
    (hmodel : selectedModel P S.pairs = fullVirtualSelectedModel P S.pairs) :
    (algorithmModel P S).direction = fullVirtualStep P (algorithmTrialParameter P) S := by
  classical
  by_cases hp : S.pairs.length = 0
  · have hp' : (algorithmModel P S).pairs.length = 0 := by rw [hret]; exact hp
    rw [algorithmModel_empty_direction P S hp']
    exact (ite_eq_left hp).symm
  · have hp' : (algorithmModel P S).pairs.length ≠ 0 := by rw [hret]; exact hp
    have hu := algorithmModel_direction_decomposition P S hp'
    rw [hret, hmodel] at hu
    rw [hu]
    exact (ite_eq_right hp).symm

/-- Exact one-step genuine scalar replay on the locally stable branch,
including the actual function values, pair anchors and clean counters. -/
theorem outerAdvance_eq_fullVirtualAdvance (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) (hg : S.gradient ≠ 0)
    (hret : (algorithmModel P S).pairs = S.pairs)
    (hpairs : (algorithmModel P S).pairsBeforeTest = S.pairs.length)
    (hdeleted : (algorithmModel P S).deletedByTest = 0)
    (hvalues : P.valuesEnabled = true →
      (∀ i : Fin S.pairs.length, |12 * storedSplit S.pairs i * (S.pairs.get i).valueDefect| ≤
        storedPairing S.pairs i i / 2) ∧ correctedWindowPasses P.windowThreshold S.pairs)
    (hinactive : (algorithmModel P S).safeDirection S = (algorithmModel P S).direction)
    (haccept : Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1)
    (hpositive : positivePair (observedTrialPair f G S ((algorithmModel P S).safeDirection S))) :
    outerAdvance P n (algorithmModel P) f G S =
      fullVirtualAdvance P (algorithmTrialParameter P) f G S := by
  classical
  have hstep := algorithmModel_direction_eq_fullVirtual P S hret hvalues
  have hbounds : (algorithmModel P S).bounds = fullVirtualBounds P S := by
    rw [algorithmModel_bounds, hret]
    rfl
  rw [outerAdvance, ite_eq_right hg, outerSearch_first_accepted _ _ _ _ S haccept]
  dsimp only
  rw [one_smul, appendPositive, ite_eq_left hpositive]
  simp only [hinactive, hstep, hret, hpairs, hdeleted, hbounds, fullVirtualAdvance]

end
end krylov.XR
