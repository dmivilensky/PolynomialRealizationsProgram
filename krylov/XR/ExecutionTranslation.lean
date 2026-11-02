import krylov.XR.QuadraticExecution

/-!
Article: main_krylov, thm:XR, independence of the coordinate origin.
Use: translate the actual cached state, including the anchors of rejected
and accepted probes. The quotient backtracking and all observed matrix
tests are unchanged. Source: affine translation of endpoint observations;
no smoothness or successful model test is required by these identities.
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Translation changes only the physical anchor of a stored observation. -/
def PairObservation.shift (b : E) (a : PairObservation E) : PairObservation E :=
  { a with anchor := a.anchor + b }

/-- Translate the physical state and every cached observation anchor. -/
def State.shift (b : E) (S : State E) : State E :=
  { S with point := S.point + b, pairs := S.pairs.map (PairObservation.shift b) }

/-- A model result carries the same direction and translated anchors. -/
def ModelResult.shift (b : E) (M : ModelResult E) : ModelResult E :=
  { M with pairs := M.pairs.map (PairObservation.shift b) }

/-- Translation of an inner-search result preserves its real step length. -/
def SearchResult.shift (b : E) (R : SearchResult E) : SearchResult E :=
  { R with pairs := R.pairs.map (PairObservation.shift b) }

theorem shift_transport (b s : E) (a : PairObservation E) :
    (a.transport s).shift b = (a.shift b).transport s := rfl

theorem appendPositive_shift (b : E) (W : List (PairObservation E))
    (a : PairObservation E) :
    appendPositive (W.map (PairObservation.shift b)) (a.shift b) =
      (appendPositive W a).map (PairObservation.shift b) := by
  classical
  simp only [appendPositive, positivePair, PairObservation.shift]
  by_cases h : 0 < inner ℝ a.step a.image <;> simp [h, PairObservation.shift]

theorem observedTrialPair_shift (b : E) (f : E → ℝ) (G : E → E)
    (S : State E) (s : E) :
    observedTrialPair (fun x => f (x - b)) (fun x => G (x - b)) (S.shift b) s =
      (observedTrialPair f G S s).shift b := by
  have hp : S.point + b + s - b = S.point + s := by abel
  simp only [observedTrialPair, State.shift, PairObservation.shift, hp]

theorem accepted_shift (b : E) (f : E → ℝ) (sigma : ℝ) (x g u : E) (t : ℝ) :
    Accepted (fun z => f (z - b)) sigma (x + b) g u t ↔
      Accepted f sigma x g u t := by
  have hp : x + b + t • u - b = x + t • u := by abel
  simp only [Accepted, trialQuotient, hp, add_sub_cancel_right]

theorem trialQuotient_shift (b : E) (f : E → ℝ) (x g u : E) (t : ℝ) :
    trialQuotient (fun z => f (z - b)) (x + b) g u t =
      trialQuotient f x g u t := by
  have hp : x + b + t • u - b = x + t • u := by abel
  simp only [trialQuotient, hp, add_sub_cancel_right]

theorem backtrackingSteps_shift (b : E) (f : E → ℝ) (x g u : E) (j : ℕ) :
    backtrackingSteps (fun z => f (z - b)) (x + b) g u j =
      backtrackingSteps f x g u j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [backtrackingSteps, ih, trialQuotient_shift]

theorem backtrackingIndex_shift (b : E) (f : E → ℝ) (sigma : ℝ) (x g u : E) :
    backtrackingIndex (fun z => f (z - b)) sigma (x + b) g u =
      backtrackingIndex f sigma x g u := by
  classical
  unfold backtrackingIndex
  simp only [backtrackingSteps_shift, accepted_shift]

omit [InnerProductSpace ℝ E] in
theorem model_updateState_shift (b : E) (M : ModelResult E) (S : State E) :
    (M.shift b).updateState (S.shift b) = (M.updateState S).shift b := rfl

/-- The actual rejected-probe search commutes with translation, including
its second ModelStep, quotient sequence and chosen first accepted index. -/
theorem rawOuterSearch_shift (b : E) (model : State E → ModelResult E)
    (hmodel : ∀ S, model (S.shift b) = (model S).shift b)
    (f : E → ℝ) (G : E → E) (sigma : ℝ) (S : State E) :
    rawOuterSearch model (fun x => f (x - b)) (fun x => G (x - b)) sigma (S.shift b) =
      (rawOuterSearch model f G sigma S).shift b := by
  classical
  unfold rawOuterSearch
  rw [hmodel]
  simp only [ModelResult.shift, State.shift, accepted_shift]
  by_cases ha : Accepted f sigma S.point S.gradient (model S).direction 1
  · simp only [ha, ite_true, SearchResult.shift]
  · simp only [ha, ite_false]
    have hobs := observedTrialPair_shift b f G S (model S).direction
    have hm : model
        { ((model S).shift b).updateState (S.shift b) with
          pairs := appendPositive ((model S).shift b).pairs
            ((observedTrialPair f G S (model S).direction).shift b) } =
        (model { (model S).updateState S with
          pairs := appendPositive (model S).pairs
            (observedTrialPair f G S (model S).direction) }).shift b := by
      convert hmodel { (model S).updateState S with
        pairs := appendPositive (model S).pairs
          (observedTrialPair f G S (model S).direction) } using 2
      simp only [State.shift, ModelResult.shift, ModelResult.updateState,
        appendPositive_shift]
    simp only [State.shift, ModelResult.shift, ModelResult.updateState] at hobs hm ⊢
    rw [hobs, hm]
    simp only [backtrackingIndex_shift, backtrackingSteps_shift, SearchResult.shift]

/-- One complete raw outer update commutes with translation. -/
theorem rawOuterAdvance_shift (b : E) (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E)
    (hmodel : ∀ S, model (S.shift b) = (model S).shift b)
    (f : E → ℝ) (G : E → E) (S : State E) :
    rawOuterAdvance P dimension model (fun x => f (x - b)) (fun x => G (x - b))
      (S.shift b) = (rawOuterAdvance P dimension model f G S).shift b := by
  classical
  by_cases hg : S.gradient = 0
  · simp only [rawOuterAdvance, show (S.shift b).gradient = S.gradient from rfl,
      hg, ite_true]
  · simp only [rawOuterAdvance, show (S.shift b).gradient = S.gradient from rfl,
      hg, ite_false]
    rw [rawOuterSearch_shift b model hmodel]
    simp only [SearchResult.shift]
    rw [observedTrialPair_shift, appendPositive_shift]
    simp only [State.shift, List.map_map, Function.comp_def, shift_transport]
    have hp : ∀ s : E, S.point + b + s - b = S.point + s := by intro s; abel
    simp only [hp]
    congr 1
    abel

/-- All raw states, including stopped states, are translated exactly. -/
theorem rawRun_shift (b : E) (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E)
    (hmodel : ∀ S, model (S.shift b) = (model S).shift b)
    (f : E → ℝ) (G : E → E) (S : State E) (k : ℕ) :
    rawRun P dimension model (fun x => f (x - b)) (fun x => G (x - b))
      (S.shift b) k = (rawRun P dimension model f G S k).shift b := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rawRun, ih, rawOuterAdvance_shift, rawRun]; exact hmodel

end
end krylov.XR
