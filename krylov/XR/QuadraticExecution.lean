import krylov.XR.AlgorithmModel

/-!
Article: main_krylov, thm:XR, the literal executor with (G) disabled.
Use: quadratic identities concern this original unsafeguarded algorithm,
including its real rejected probe, reset and subsequent backtracking.
The same data-only ModelStep, observations, capacity rule and quotient
backtracking are used by the globally safeguarded executor. Source: alg:xr.
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual one-probe search with the safeguard disabled. -/
def rawOuterSearch (model : State E → ModelResult E) (f : E → ℝ) (G : E → E)
    (sigma : ℝ) (S : State E) : SearchResult E := by
  classical
  let M₀ := model S
  let u₀ := M₀.direction
  exact if Accepted f sigma S.point S.gradient u₀ 1 then
    ⟨M₀.pairs, M₀.bounds, u₀, 1, 1, M₀.pairsBeforeTest, M₀.deletedByTest⟩
  else
    let P := observedTrialPair f G S u₀
    let S₁ := { M₀.updateState S with pairs := appendPositive M₀.pairs P }
    let M₁ := model S₁
    let u₁ := M₁.direction
    let j := backtrackingIndex f sigma S.point S.gradient u₁
    ⟨M₁.pairs, M₁.bounds, u₁, backtrackingSteps f S.point S.gradient u₁ j,
      j + 2, M₀.pairsBeforeTest, M₀.deletedByTest⟩

/-- The real outer update without (G), preserving the literal probe and
capacity semantics rather than identifying this run with XRFC by definition. -/
def rawOuterAdvance (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E) (S : State E) : State E := by
  classical
  exact if S.gradient = 0 then S else
    let R := rawOuterSearch model f G P.armijo S
    let s := R.length • R.direction
    let W := appendPositive R.pairs (observedTrialPair f G S s)
    let cap := updateCapacity P dimension S.capacity S.cleanCount R.firstPairs
      R.firstDeleted R.evaluations
    { S with
      point := S.point + s
      value := f (S.point + s)
      gradient := G (S.point + s)
      pairs := W.map (fun pair => pair.transport s)
      bounds := R.bounds
      capacity := cap.1
      cleanCount := cap.2 }

/-- Actual recursive unsafeguarded XR, stopped only at an observed zero
gradient. Its scalar trial rule and all query points are computed. -/
def rawRun (P : Parameters) (dimension : ℕ) (model : State E → ModelResult E)
    (f : E → ℝ) (G : E → E) (S₀ : State E) : ℕ → State E
  | 0 => S₀
  | k + 1 => rawOuterAdvance P dimension model f G (rawRun P dimension model f G S₀ k)

/-- The complete concrete algorithm in the no-(G) case of thm:XR. -/
def rawAlgorithmRun {n : ℕ} (P : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds := none) :
    ℕ → State (EuclideanSpace ℝ (Fin n)) :=
  rawRun P n (algorithmModel P) f G (algorithmInitialState P f G x₀ bounds)

/-- Actual scalar and gradient caching is exact in the raw executor as
well, independently of any convergence or model-domain theorem. -/
theorem rawOuterAdvance_cache (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E) (S : State E)
    (hf : S.value = f S.point) (hg : S.gradient = G S.point) :
    (rawOuterAdvance P dimension model f G S).value =
        f (rawOuterAdvance P dimension model f G S).point ∧
      (rawOuterAdvance P dimension model f G S).gradient =
        G (rawOuterAdvance P dimension model f G S).point := by
  classical
  unfold rawOuterAdvance
  split
  · exact ⟨hf, hg⟩
  · exact ⟨rfl, rfl⟩

/-- Every raw recursive state contains the real endpoint values and
gradient even if its first rejected probe was stored. -/
theorem rawRun_cache (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E) (S₀ : State E)
    (hf : S₀.value = f S₀.point) (hg : S₀.gradient = G S₀.point) (i : ℕ) :
    let S := rawRun P dimension model f G S₀ i
    S.value = f S.point ∧ S.gradient = G S.point := by
  induction i with
  | zero => exact ⟨hf, hg⟩
  | succ i ih => exact rawOuterAdvance_cache P dimension model f G _ ih.1 ih.2

/-- If both actually visited model directions satisfy (G), the safeguarded
and unsafeguarded one-probe searches coincide, including rejection/reset. -/
theorem rawOuterSearch_eq (model : State E → ModelResult E) (f : E → ℝ) (G : E → E)
    (sigma : ℝ) (S : State E)
    (h₀ : GradientRelated S.descentConstant S.normConstant S.gradient (model S).direction)
    (h₁ : let M := model S
      let S₁ := { M.updateState S with
        pairs := appendPositive M.pairs (observedTrialPair f G S M.direction) }
      GradientRelated S₁.descentConstant S₁.normConstant S₁.gradient (model S₁).direction) :
    rawOuterSearch model f G sigma S = outerSearch model f G sigma S := by
  classical
  have he₀ : (model S).safeDirection S = (model S).direction :=
    safeguard_eq_of_gradientRelated _ _ _ _ _ h₀
  let S₁ := { (model S).updateState S with
    pairs := appendPositive (model S).pairs (observedTrialPair f G S (model S).direction) }
  have he₁ : (model S₁).safeDirection S₁ = (model S₁).direction :=
    safeguard_eq_of_gradientRelated _ _ _ _ _ h₁
  unfold rawOuterSearch outerSearch
  dsimp only
  rw [he₀]
  split
  · rfl
  · rw [he₁]

end
end krylov.XR
