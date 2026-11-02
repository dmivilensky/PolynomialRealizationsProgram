import krylov.XR.QuadraticTrial

/-!
Article: main_krylov, thm:XR, quadratic oracle-event semantics.
Use: expose each actually stored probe/accepted observation of the literal
executor. A rejected probe leaves the cache/anchor fixed; an accepted event
transports all anchor pairings. Arbitrary accept/reject decisions are
allowed, as in the theorem, and no flag or output property is a state field.
Source: alg:xr and the prescribed one-rejected-probe update.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One real stored oracle event: query the actual computed raw model
direction, append its positive observed secant, and move the anchor exactly
when this query is accepted. Capacity is an outer-loop operation. -/
def rawObservationEvent (model : State E → ModelResult E) (f : E → ℝ) (G : E → E)
    (length : ℝ) (move : Bool) (S : State E) : State E :=
  let M := model S
  let s := length • M.direction
  let W := appendPositive M.pairs (observedTrialPair f G S s)
  if move then
    { M.updateState S with
      point := S.point + s
      value := f (S.point + s)
      gradient := G (S.point + s)
      pairs := W.map (fun P => P.transport s) }
  else { M.updateState S with pairs := W }

/-- Actual data remain faithful at a rejected or accepted stored event.
The proof uses real oracle evaluations and exact anchor transport. -/
theorem rawObservationEvent_faithful (model : State E → ModelResult E)
    (f : E → ℝ) (G : E → E)
    (hmodel : ∀ S : State E, (∀ a ∈ S.pairs, PairFaithful f G S.point a) →
      ∀ a ∈ (model S).pairs, PairFaithful f G S.point a)
    (length : ℝ) (move : Bool) (S : State E)
    (hf : S.value = f S.point) (hg : S.gradient = G S.point)
    (hS : ∀ a ∈ S.pairs, PairFaithful f G S.point a) :
    ∀ a ∈ (rawObservationEvent model f G length move S).pairs,
      PairFaithful f G (rawObservationEvent model f G length move S).point a := by
  have hw := appendPositive_all (model S).pairs
    (observedTrialPair f G S (length • (model S).direction)) _
    (hmodel S hS) (observedTrialPair_faithful f G S hf hg _)
  cases move
  · exact hw
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact PairFaithful.transport f G S.point _ b (hw b hb)

/-- Actual cache equations are preserved at every stored event. -/
theorem rawObservationEvent_cache (model : State E → ModelResult E)
    (f : E → ℝ) (G : E → E) (length : ℝ) (move : Bool) (S : State E)
    (hf : S.value = f S.point) (hg : S.gradient = G S.point) :
    let S' := rawObservationEvent model f G length move S
    S'.value = f S'.point ∧ S'.gradient = G S'.point := by
  cases move
  · exact ⟨hf, hg⟩
  · exact ⟨rfl, rfl⟩

/-- With m₀=mmax=n the literal outer capacity update keeps full memory,
regardless of rejection count or clean-counter state. -/
theorem updateCapacity_full (P : Parameters) (n nu p o evaluations : ℕ)
    (hinitial : P.initialCapacity = n) (hmaximum : P.maximumCapacity = n) :
    (updateCapacity P n n nu p o evaluations).1 = n := by
  unfold updateCapacity
  split_ifs <;> (try dsimp only) <;> (try split_ifs) <;>
    (try dsimp only) <;> simp only [hinitial, hmaximum] <;> omega

end
end krylov.XR
