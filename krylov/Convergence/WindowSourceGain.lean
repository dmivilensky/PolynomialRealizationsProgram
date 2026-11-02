import krylov.Convergence.WindowSelectedExecution

/-!
Article: main_krylov, thm:grow and cor:xrF, original incoming independence.
Use: carry the original physical least-column gain of the actual retained
memory to the true consecutive accepted window. Source: faithful endpoint
records and the derived chronological full-window phase; no canonical gain
or independently postulated sliding-window condition is introduced.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Filter Topology krylov.XR krylov.Methods
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Static chronological endpoint records preserve the original synthesis
inequality, including the dependent finite length of a real stored list. -/
theorem gain_chronological_records {p : ℕ} (f : E → ℝ) (G : E → E)
    (W : List (PairObservation E)) (x : ℕ → E) (k : ℕ)
    (h : staticObservations W=List.ofFn (fun i : Fin p=>
      observePair f G (x (k+i.val)) (x (k+i.val+1)-x (k+i.val))))
    {σ : ℝ} (hgain : ∀ c : Fin W.length → ℝ,
      σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (storedSteps W)) c‖^2)
    (c : Fin p → ℝ) :
    σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (windowStep x k)) c‖^2 := by
  have hlen : W.length=p := by
    simpa only [staticObservations,List.length_map,List.length_ofFn] using congrArg List.length h
  subst p
  have hs : storedSteps W=windowStep x k := by
    funext i
    exact congrArg PairObservation.step (staticObservations_get W _ h i)
  rw [←hs]
  exact hgain c

/-- Original incoming independence for a literal source-driven XR run
becomes independence of the actual consecutive accepted full windows. -/
theorem source_full_window_gain {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (D : GrowthSource P f G H x₀ center bounds) (hP : P.Valid n)
    (hoff : P.valuesEnabled=false) (hmax : P.maximumCapacity=n) :
    ∀ᶠ k in atTop,∀ c : Fin n → ℝ,
      D.sigma^2*‖WithLp.toLp 2 c‖^2≤
        ‖combine (unitWindow (windowStep (fun j=>(algorithmRun P f G x₀ bounds j).point) k)) c‖^2 := by
  obtain ⟨K₁,hK₁⟩ := source_full_observation_chronology P f G H x₀ center bounds D hP hoff hmax
  obtain ⟨K₂,hK₂⟩ := D.clean_phase hP hoff
  filter_upwards [eventually_ge_atTop (max D.gainStart (max K₁ K₂))] with k hk c
  apply gain_chronological_records f G _ _ k (hK₁ k (by omega)) _ c
  rw [(hK₂ (k+n) (by omega)).1]
  exact D.gain (k+n) (by omega)

/-- The same original incoming gain is preserved when value correction
is enabled; the successful phase is derived from the selected-model source. -/
theorem selected_source_full_window_gain {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (D : SelectedGrowthSource P f G H x₀ center bounds) (hP : P.Valid n)
    (hmax : P.maximumCapacity=n) :
    ∀ᶠ k in atTop,∀ c : Fin n → ℝ,
      D.sigma^2*‖WithLp.toLp 2 c‖^2≤
        ‖combine (unitWindow (windowStep (fun j=>(algorithmRun P f G x₀ bounds j).point) k)) c‖^2 := by
  obtain ⟨K₁,hK₁⟩ := selected_source_full_observation_chronology P f G H x₀ center bounds D hP hmax
  obtain ⟨K₂,hK₂⟩ := D.clean_phase hP
  filter_upwards [eventually_ge_atTop (max D.gainStart (max K₁ K₂))] with k hk c
  apply gain_chronological_records f G _ _ k (hK₁ k (by omega)) _ c
  rw [(hK₂ (k+n) (by omega)).1]
  exact D.gain (k+n) (by omega)

end
end krylov.Convergence
