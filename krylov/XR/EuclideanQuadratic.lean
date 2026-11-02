import krylov.XR.EuclideanGlobal
import krylov.XR.EuclideanMemory
import krylov.XR.QuadraticTranslation

/-!
Article: main_krylov, thm:XR and cor:xrF, exact quadratic split independence.
Use: actual quadratic endpoint defects vanish on every retained pair and
rejected probe. Therefore the Euclidean and model-metric ModelSteps, full
safeguarded executions and raw executions agree literally, for arbitrary
capacity, initial point and acceptance/backtracking outcomes.
Source: exact quadratic trapezoid cancellation and genuine executor induction.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
set_option maxHeartbeats 800000

/-- At zero actual defects both Euclidean and model-metric selected
matrices are exactly the ordinary latest-information matrix. -/
theorem selectedEuclideanModel_eq_of_zero_defects (P : Parameters) (x : E)
    (W : List (PairObservation E)) (hz : ∀ a ∈ W, a.valueDefect = 0) :
    selectedEuclideanModel P x W = selectedModel P W := by
  classical
  have hd (i : Fin W.length) : (W.get i).valueDefect = 0 := hz _ (List.get_mem W i)
  have he : euclideanStoredValueModel x W = storedModel W := by
    have ht : euclideanStoredValueTerm x W = 0 := by
      funext i
      dsimp only [euclideanStoredValueTerm]
      rw [hd i]
      simp
    simp only [euclideanStoredValueModel, ht, Matrix.diagonal_zero', sub_zero]
  have ho : storedValueModel W = storedModel W := by
    have ht : storedValueTerm W = 0 := by
      funext i
      dsimp only [storedValueTerm]
      rw [hd i]
      simp
    simp only [storedValueModel, ht, Matrix.diagonal_zero', sub_zero]
  unfold selectedEuclideanModel selectedModel
  split_ifs <;> simp only [he, ho]

/-- Both actual ModelSteps agree on every memory of zero scalar defects,
including totalized singular off-domain branches and all saved counters. -/
theorem euclideanAlgorithmModel_eq_of_zero_defects (P : Parameters) (S : State E)
    (hz : ∀ a ∈ S.pairs, a.valueDefect = 0) : euclideanAlgorithmModel P S = algorithmModel P S := by
  let W := (rankWindow n S).drop (modelDeletion P (rankWindow n S))
  have hW : ∀ a ∈ W, a.valueDefect = 0 := fun a ha => hz a (algorithmModel_pair_mem P S a ha)
  have ht := selectedEuclideanModel_eq_of_zero_defects P S.point W hW
  dsimp only [W] at ht
  unfold euclideanAlgorithmModel algorithmModel
  dsimp only
  simp only [ht]
  rfl

/-- The native computed trial scalars also agree on the real zero-defect
memory, so the original quadratic nonzero-trial condition is unchanged. -/
theorem euclideanTrialParameter_eq_of_zero_defects (P : Parameters) (S : State E)
    (hz : ∀ a ∈ S.pairs, a.valueDefect = 0) : euclideanTrialParameter P S = algorithmTrialParameter P S := by
  have hm := euclideanAlgorithmModel_eq_of_zero_defects P S hz
  have hs := selectedEuclideanModel_eq_of_zero_defects P S.point (algorithmModel P S).pairs
    (fun a ha => hz a (algorithmModel_pair_mem P S a ha))
  unfold euclideanTrialParameter algorithmTrialParameter
  rw [hm]
  dsimp only
  simp only [hs]
  rfl

/-- Every arbitrary accepted/rejected stored event is also identical
when its real cached defects vanish; its acceptance rule is unrestricted. -/
theorem euclideanRawObservationEvent_eq_of_zero_defects (P : Parameters) (f : E → ℝ) (G : E → E)
    (S : State E) (hz : ∀ a ∈ S.pairs, a.valueDefect = 0) (length : ℝ) (move : Bool) :
    rawObservationEvent (euclideanAlgorithmModel P) f G length move S =
      rawObservationEvent (algorithmModel P) f G length move S := by
  unfold rawObservationEvent
  rw [euclideanAlgorithmModel_eq_of_zero_defects P S hz]

/-- Exact trapezoid cancellation transfers from a genuine oracle pair
to every faithful cached observation, independent of its anchor transport. -/
theorem faithful_defect_zero_of_observePair (f : E → ℝ) (G : E → E)
    (hz : ∀ x s, (observePair f G x s).valueDefect = 0)
    (x : E) (a : PairObservation E) (ha : PairFaithful f G x a) : a.valueDefect = 0 := by
  rw [ha.2.1, ha.1]
  exact hz a.anchor a.step

/-- The actual cached first trial has zero defect whenever the source's
true endpoint trapezoid is exact. -/
theorem observedTrialPair_zero_of_observePair (f : E → ℝ) (G : E → E)
    (hz : ∀ x s, (observePair f G x s).valueDefect = 0) (S : State E)
    (hf : S.value = f S.point) (hg : S.gradient = G S.point) (s : E) :
    (observedTrialPair f G S s).valueDefect = 0 := by
  simpa only [observedTrialPair, observePair, hf, hg] using hz S.point s

/-- The full real one-probe search agrees for both splits, including
its rejected-probe ModelStep and all quotient backtracking evaluations. -/
theorem euclideanOuterSearch_eq_of_zero_defects (P : Parameters) (f : E → ℝ) (G : E → E)
    (hz : ∀ x s, (observePair f G x s).valueDefect = 0) (S : State E)
    (hf : S.value = f S.point) (hg : S.gradient = G S.point)
    (hS : ∀ a ∈ S.pairs, a.valueDefect = 0) :
    outerSearch (euclideanAlgorithmModel P) f G P.armijo S = outerSearch (algorithmModel P) f G P.armijo S := by
  classical
  have he₀ := euclideanAlgorithmModel_eq_of_zero_defects P S hS
  let M := algorithmModel P S
  let u := M.safeDirection S
  let S₁ := { M.updateState S with pairs := appendPositive M.pairs (observedTrialPair f G S u) }
  have hM : ∀ a ∈ M.pairs, a.valueDefect = 0 := fun a ha => hS a (algorithmModel_pair_mem P S a ha)
  have hp : (observedTrialPair f G S u).valueDefect = 0 := observedTrialPair_zero_of_observePair f G hz S hf hg u
  have he₁ := euclideanAlgorithmModel_eq_of_zero_defects P S₁ (appendPositive_all _ _ _ hM hp)
  unfold outerSearch
  rw [he₀]
  dsimp only
  split
  · rfl
  · rw [he₁]

/-- The complete actual outer step agrees, including observations,
anchor transport, capacity and clean counter update. -/
theorem euclideanOuterAdvance_eq_of_zero_defects (P : Parameters) (f : E → ℝ) (G : E → E)
    (hz : ∀ x s, (observePair f G x s).valueDefect = 0) (S : State E)
    (hf : S.value = f S.point) (hg : S.gradient = G S.point)
    (hS : ∀ a ∈ S.pairs, a.valueDefect = 0) :
    outerAdvance P n (euclideanAlgorithmModel P) f G S = outerAdvance P n (algorithmModel P) f G S := by
  classical
  unfold outerAdvance
  rw [euclideanOuterSearch_eq_of_zero_defects P f G hz S hf hg hS]

/-- Deterministic causal replay uses equality only at actual visited
outer states; the concrete model's large algebraic formula stays opaque. -/
theorem split_run_congr_visits (P : Parameters) (dimension : ℕ)
    (m₁ m₂ : State E → ModelResult E) (f : E → ℝ) (G : E → E) (S₀ : State E)
    (hstep : ∀ j, outerAdvance P dimension m₁ f G (run P dimension m₂ f G S₀ j) =
      outerAdvance P dimension m₂ f G (run P dimension m₂ f G S₀ j)) (k : ℕ) :
    run P dimension m₁ f G S₀ k = run P dimension m₂ f G S₀ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [run, run, ih]
    exact hstep k

/-- Zero genuine trapezoid defects force literal equality of the whole
actual split executions from any initial point and any memory parameters. -/
theorem euclideanAlgorithmRun_eq_of_zero_trapezoid (P : Parameters) (f : E → ℝ) (G : E → E)
    (hz : ∀ x s, (observePair f G x s).valueDefect = 0) (x₀ : E) (bounds : SpectralBounds) (k : ℕ) :
    euclideanAlgorithmRun P f G x₀ bounds k = algorithmRun P f G x₀ bounds k := by
  apply split_run_congr_visits P n (euclideanAlgorithmModel P) (algorithmModel P) f G
    (algorithmInitialState P f G x₀ bounds) _ k
  intro j
  have hc := run_cache_constants P n (algorithmModel P) f G
    (algorithmInitialState P f G x₀ bounds) rfl rfl j
  exact euclideanOuterAdvance_eq_of_zero_defects P f G hz _ hc.1 hc.2.1
    (fun a ha => faithful_defect_zero_of_observePair f G hz _ a
      (algorithmRun_pairs_faithful P f G x₀ bounds j a ha))

/-- Every true scalar quadratic has exactly zero observed trapezoid
error, for every pair and every anchor. -/
theorem quadratic_observePair_zero (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (g : E) (constant : ℝ) (x s : E) :
    (observePair (quadraticObjective Q g constant) (quadraticGradient Q g) x s).valueDefect = 0 := by
  apply faithful_quadratic_defect Q hQ g constant x
  simp only [PairFaithful, observePair, sub_self, inner_zero_right, and_self]

/-- Exact equality of Euclidean and model-metric literal quadratic
executions from an arbitrary initial point, with no acceptance assumptions. -/
theorem euclideanAlgorithmRun_quadratic_eq (P : Parameters) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (g : E) (constant : ℝ) (x₀ : E)
    (bounds : SpectralBounds) (k : ℕ) :
    euclideanAlgorithmRun P (quadraticObjective Q g constant) (quadraticGradient Q g) x₀ bounds k =
      algorithmRun P (quadraticObjective Q g constant) (quadraticGradient Q g) x₀ bounds k :=
  euclideanAlgorithmRun_eq_of_zero_trapezoid P _ _ (quadratic_observePair_zero Q hQ g constant) x₀ bounds k

/-- Translation of the scalar source preserves exact trapezoid data. -/
theorem observePair_zero_translate (f : E → ℝ) (G : E → E)
    (hz : ∀ x s, (observePair f G x s).valueDefect = 0) (b : E) :
    ∀ x s, (observePair (fun z => f (z-b)) (fun z => G (z-b)) x s).valueDefect = 0 := by
  intro x s
  have hs : x+s-b = (x-b)+s := by abel
  simpa only [observePair, hs] using hz (x-b) s

/-- Literal split independence also holds for every translated true
quadratic source; its starting point is unrestricted. -/
theorem euclideanAlgorithmRun_translated_quadratic_eq (P : Parameters) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (g : E) (constant : ℝ) (b x₀ : E)
    (bounds : SpectralBounds) (k : ℕ) :
    euclideanAlgorithmRun P (fun x => quadraticObjective Q g constant (x-b))
      (fun x => quadraticGradient Q g (x-b)) x₀ bounds k =
      algorithmRun P (fun x => quadraticObjective Q g constant (x-b))
        (fun x => quadraticGradient Q g (x-b)) x₀ bounds k :=
  euclideanAlgorithmRun_eq_of_zero_trapezoid P _ _
    (observePair_zero_translate _ _ (quadratic_observePair_zero Q hQ g constant) b) x₀ bounds k

/-- Faithfulness for the raw executor follows from its exact real-event
decomposition, including both the rejected and accepted observations. -/
theorem rawAlgorithmRun_pair_faithfulness (P : Parameters) (f : E → ℝ) (G : E → E)
    (x₀ : E) (bounds : SpectralBounds) (k : ℕ) :
    ∀ a ∈ (rawAlgorithmRun P f G x₀ bounds k).pairs,
      PairFaithful f G (rawAlgorithmRun P f G x₀ bounds k).point a := by
  induction k with
  | zero => simp [rawAlgorithmRun, rawRun, algorithmInitialState, initialState]
  | succ k ih =>
    let S := rawAlgorithmRun P f G x₀ bounds k
    have hc := rawRun_cache P n (algorithmModel P) f G (algorithmInitialState P f G x₀ bounds) rfl rfl k
    have hm := fun S hS => algorithmModel_faithful P f G S hS
    change ∀ a ∈ (rawOuterAdvance P n (algorithmModel P) f G S).pairs,
      PairFaithful f G (rawOuterAdvance P n (algorithmModel P) f G S).point a
    rw [rawOuterAdvance_event_decomposition]
    split_ifs with hstop
    · exact ih
    · dsimp only
      split
      · exact rawObservationEvent_faithful (algorithmModel P) f G hm 1 true S hc.1 hc.2 ih
      · let probe := rawObservationEvent (algorithmModel P) f G 1 false S
        have hp := rawObservationEvent_faithful (algorithmModel P) f G hm 1 false S hc.1 hc.2 ih
        have hpc := rawObservationEvent_cache (algorithmModel P) f G 1 false S hc.1 hc.2
        exact rawObservationEvent_faithful (algorithmModel P) f G hm _ true probe hpc.1 hpc.2 hp

/-- Disabling (G) changes no aspect of exact split independence, including
all rejected probes, resets, backtracking, and saved capacity counters. -/
theorem euclideanRawOuterSearch_eq_of_zero_defects (P : Parameters) (f : E → ℝ) (G : E → E)
    (hz : ∀ x s, (observePair f G x s).valueDefect = 0) (S : State E)
    (hf : S.value = f S.point) (hg : S.gradient = G S.point)
    (hS : ∀ a ∈ S.pairs, a.valueDefect = 0) :
    rawOuterSearch (euclideanAlgorithmModel P) f G P.armijo S = rawOuterSearch (algorithmModel P) f G P.armijo S := by
  classical
  have he₀ := euclideanAlgorithmModel_eq_of_zero_defects P S hS
  let M := algorithmModel P S
  let u := M.direction
  let S₁ := { M.updateState S with pairs := appendPositive M.pairs (observedTrialPair f G S u) }
  have hM : ∀ a ∈ M.pairs, a.valueDefect = 0 := fun a ha => hS a (algorithmModel_pair_mem P S a ha)
  have hp : (observedTrialPair f G S u).valueDefect = 0 := observedTrialPair_zero_of_observePair f G hz S hf hg u
  have he₁ := euclideanAlgorithmModel_eq_of_zero_defects P S₁ (appendPositive_all _ _ _ hM hp)
  unfold rawOuterSearch
  rw [he₀]
  dsimp only
  split
  · rfl
  · rw [he₁]

/-- The actual Euclidean split executor with the safeguard disabled. -/
def rawEuclideanAlgorithmRun (P : Parameters) (f : E → ℝ) (G : E → E)
    (x₀ : E) (bounds : SpectralBounds := none) : ℕ → State E :=
  rawRun P n (euclideanAlgorithmModel P) f G (algorithmInitialState P f G x₀ bounds)

/-- Raw causal replay is equally independent of the concrete model
implementation once the two visited outer steps have been identified. -/
theorem split_rawRun_congr_visits (P : Parameters) (dimension : ℕ)
    (m₁ m₂ : State E → ModelResult E) (f : E → ℝ) (G : E → E) (S₀ : State E)
    (hstep : ∀ j, rawOuterAdvance P dimension m₁ f G (rawRun P dimension m₂ f G S₀ j) =
      rawOuterAdvance P dimension m₂ f G (rawRun P dimension m₂ f G S₀ j)) (k : ℕ) :
    rawRun P dimension m₁ f G S₀ k = rawRun P dimension m₂ f G S₀ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rawRun, rawRun, ih]
    exact hstep k

/-- Both raw algorithms agree on every exact-trapezoid source for all
capacities and arbitrary initial points. No flag or acceptance is assumed. -/
theorem rawEuclideanAlgorithmRun_eq_of_zero_trapezoid (P : Parameters) (f : E → ℝ) (G : E → E)
    (hz : ∀ x s, (observePair f G x s).valueDefect = 0) (x₀ : E) (bounds : SpectralBounds) (k : ℕ) :
    rawEuclideanAlgorithmRun P f G x₀ bounds k = rawAlgorithmRun P f G x₀ bounds k := by
  apply split_rawRun_congr_visits P n (euclideanAlgorithmModel P) (algorithmModel P) f G
    (algorithmInitialState P f G x₀ bounds) _ k
  intro j
  have hc := rawRun_cache P n (algorithmModel P) f G (algorithmInitialState P f G x₀ bounds) rfl rfl j
  have hs : ∀ a ∈ (rawAlgorithmRun P f G x₀ bounds j).pairs, a.valueDefect = 0 :=
    fun a ha => faithful_defect_zero_of_observePair f G hz _ a
      (rawAlgorithmRun_pair_faithfulness P f G x₀ bounds j a ha)
  unfold rawOuterAdvance
  rw [euclideanRawOuterSearch_eq_of_zero_defects P f G hz _ hc.1 hc.2 hs]

/-- Exact raw quadratic execution equality, including the original
arbitrary translated source and arbitrary starting point. Existing full
CG identities and the before-first-deletion theorem therefore apply. -/
theorem rawEuclideanAlgorithmRun_translated_quadratic_eq (P : Parameters) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (g : E) (constant : ℝ) (b x₀ : E)
    (bounds : SpectralBounds) (k : ℕ) :
    rawEuclideanAlgorithmRun P (fun x => quadraticObjective Q g constant (x-b))
      (fun x => quadraticGradient Q g (x-b)) x₀ bounds k =
      rawAlgorithmRun P (fun x => quadraticObjective Q g constant (x-b))
        (fun x => quadraticGradient Q g (x-b)) x₀ bounds k :=
  rawEuclideanAlgorithmRun_eq_of_zero_trapezoid P _ _
    (observePair_zero_translate _ _ (quadratic_observePair_zero Q hQ g constant) b) x₀ bounds k

end
end krylov.XR
