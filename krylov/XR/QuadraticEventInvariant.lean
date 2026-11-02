import krylov.XR.QuadraticEvents

/-!
Article: main_krylov, thm:XR, genuine stored-event induction.
Use: prove the independent full Krylov window on actual data-only model
queries, for arbitrary nonzero trial scalars and arbitrary accepted/rejected
decisions. The certificate below is a proved mathematical invariant, not a
field of the executor. In particular rejected probes change the observed
flag while leaving the current point fixed. Source: the proved true CG
Galerkin solve and elementary independent-span extension.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Mathematical invariant of the actual quadratic stored-event prefix. -/
structure QuadraticEventInvariant (Q : E →L[ℝ] E) (g₀ : E) (constant : ℝ)
    (S : State E) (k : ℕ) : Prop where
  value : S.value = quadraticObjective Q g₀ constant S.point
  gradient : S.gradient = quadraticGradient Q g₀ S.point
  faithful : ∀ a ∈ S.pairs,
    PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) S.point a
  independent : LinearIndependent ℝ (storedSteps S.pairs)
  flag : Submodule.span ℝ (range (storedSteps S.pairs)) = directionFlag Q g₀ k
  point_mem : S.point ∈ Submodule.span ℝ (range (storedSteps S.pairs))
  count : S.pairs.length = k

/-- Actual empty initialization satisfies the quadratic flag invariant. -/
theorem quadraticEventInvariant_initial (P : Parameters) (Q : E →L[ℝ] E)
    (g₀ : E) (constant initialStep : ℝ) (bounds : SpectralBounds) :
    QuadraticEventInvariant Q g₀ constant
      (initialState P (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 initialStep bounds) 0 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl⟩
  · simp only [initialState, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  · change LinearIndependent ℝ (storedSteps ([] : List (PairObservation E)))
    let emptyIndex : IsEmpty (Fin ([] : List (PairObservation E)).length) := ⟨fun i => Fin.elim0 i⟩
    exact linearIndependent_empty_type
  · rw [directionFlag_zero]
    change Submodule.span ℝ (range (storedSteps ([] : List (PairObservation E)))) = ⊥
    have he : range (storedSteps ([] : List (PairObservation E))) = ∅ := by
      ext x
      constructor
      · rintro ⟨i, _⟩
        exact Fin.elim0 i
      · exact False.elim
    rw [he, Submodule.span_empty]
  · exact Submodule.zero_mem _

/-- Each actual stored quadratic query adds exactly one Krylov direction,
whether it is rejected or accepted. All secants/caches and the invariant
are derived from the real oracle event, not assumed to follow CG. -/
theorem quadraticEventInvariant_step {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ) (S : State (EuclideanSpace ℝ (Fin n)))
    (k : ℕ) (hk : k < n) (hg : ∀ i ≤ k, CG.gradient Q g₀ i ≠ 0)
    (hS : QuadraticEventInvariant Q g₀ constant S k) (hcap : k ≤ S.capacity)
    (length : ℝ) (hlength : length ≠ 0) (move : Bool)
    (htrial : algorithmTrialParameter P S ≠ 0) :
    QuadraticEventInvariant Q g₀ constant
      (rawObservationEvent (algorithmModel P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀) length move S) (k + 1) := by
  let f := quadraticObjective Q g₀ constant
  let G := quadraticGradient Q g₀
  let step := length • (algorithmModel P S).direction
  let pair := observedTrialPair f G S step
  have hcapacity : S.pairs.length ≤ min S.capacity n := by rw [hS.count]; omega
  have hret := quadratic_model_retains P Q hQ hpos g₀ constant S hS.faithful hS.independent hcapacity
  have hx : S.point ∈ directionFlag Q g₀ k := hS.flag ▸ hS.point_mem
  have hu := quadratic_actual_trial P Q hQ hpos g₀ constant S k
    (fun i hi => hg i hi.le) hS.gradient hS.faithful hS.independent hS.flag hS.point_mem hS.count hcapacity
  have hstep : step = length • ((CG.displacement Q g₀ k - S.point) +
      algorithmTrialParameter P S • CG.direction Q g₀ k) := by rw [← hu]
  have hnew : step ∉ directionFlag Q g₀ k := by
    rw [hstep]
    exact quadratic_observed_step_new Q hQ hpos g₀ k (fun i hi => hg i hi.le) (hg k le_rfl)
      S.point hx _ _ htrial hlength
  have hnonzero : step ≠ 0 := by
    intro hz
    exact hnew (hz ▸ (directionFlag Q g₀ k).zero_mem)
  have happend : appendPositive (algorithmModel P S).pairs pair = S.pairs ++ [pair] := by
    rw [hret.1]
    exact appendPositive_quadratic Q hpos g₀ f S hS.gradient S.pairs step hnonzero
  have hind : LinearIndependent ℝ (storedSteps (S.pairs ++ [pair])) := by
    apply storedSteps_append_independent _ _ hS.independent
    change step ∉ _
    rwa [hS.flag]
  have hflag : Submodule.span ℝ (range (storedSteps (S.pairs ++ [pair]))) =
      directionFlag Q g₀ (k + 1) := by
    rw [storedSteps_append_range, Submodule.span_insert, hS.flag]
    change (ℝ ∙ step) ⊔ directionFlag Q g₀ k = _
    rw [hstep]
    exact quadratic_observed_step_flag Q g₀ k S.point hx _ _ htrial hlength
  have hcache := rawObservationEvent_cache (algorithmModel P) f G length move S hS.value hS.gradient
  have hfaithful := rawObservationEvent_faithful (algorithmModel P) f G
    (fun S' hS' => algorithmModel_faithful P f G S' hS') length move S hS.value hS.gradient hS.faithful
  refine ⟨hcache.1, hcache.2, hfaithful, ?_, ?_, ?_, ?_⟩
  · cases move
    · change LinearIndependent ℝ (storedSteps (appendPositive (algorithmModel P S).pairs pair))
      rw [happend]
      exact hind
    · change LinearIndependent ℝ (storedSteps ((appendPositive (algorithmModel P S).pairs pair).map
        (fun P => P.transport step)))
      rw [happend]
      exact storedSteps_transport_independent _ step hind
  · cases move
    · change Submodule.span ℝ (range (storedSteps (appendPositive (algorithmModel P S).pairs pair))) = _
      rw [happend]
      exact hflag
    · change Submodule.span ℝ (range (storedSteps ((appendPositive (algorithmModel P S).pairs pair).map
        (fun P => P.transport step)))) = _
      rw [happend, storedSteps_transport]
      exact hflag
  · have hold : S.point ∈ Submodule.span ℝ (range (storedSteps (S.pairs ++ [pair]))) := by
      apply (Submodule.span_mono (by rw [storedSteps_append_range]; exact Set.subset_insert _ _)) hS.point_mem
    have hstepmem : step ∈ Submodule.span ℝ (range (storedSteps (S.pairs ++ [pair]))) :=
      Submodule.subset_span (by rw [storedSteps_append_range]; exact Or.inl rfl)
    cases move
    · change S.point ∈ Submodule.span ℝ (range (storedSteps (appendPositive (algorithmModel P S).pairs pair)))
      rw [happend]
      exact hold
    · change S.point + step ∈ Submodule.span ℝ (range (storedSteps
        ((appendPositive (algorithmModel P S).pairs pair).map (fun P => P.transport step))))
      rw [happend, storedSteps_transport]
      exact Submodule.add_mem _ hold hstepmem
  · cases move
    · change (appendPositive (algorithmModel P S).pairs pair).length = k + 1
      rw [happend, List.length_append, List.length_singleton, hS.count]
    · change ((appendPositive (algorithmModel P S).pairs pair).map
        (fun P => P.transport step)).length = k + 1
      rw [List.length_map, happend, List.length_append, List.length_singleton, hS.count]

end
end krylov.XR
