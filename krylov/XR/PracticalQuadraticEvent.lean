import krylov.XR.PracticalQuadraticTrial

/-!
# Fresh-secant quadratic stored events

Theorem 7.1 (`thm:XR`): the actual fresh-secant ModelStep inherits the
proved Krylov induction for nonzero computed trial scalars. Accepted and
rejected oracle observations retain their genuine caches and transported
secants. The full-window query is proved separately from its Armijo
acceptance. Raw outer recursion below uses the executor's totalized search
index; its algebraic identities do not assert search existence for an
arbitrary trial policy. Source: the generic quadratic event/flag argument.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Reference
open scoped InnerProductSpace
/-- Each actual stored quadratic query adds exactly one Krylov direction,
whether it is rejected or accepted. All secants/caches and the invariant
are derived from the real oracle event, not assumed to follow CG. -/
theorem practicalQuadraticEventInvariant_step {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ) (S : State (EuclideanSpace ℝ (Fin n)))
    (k : ℕ) (hk : k < n) (hg : ∀ i ≤ k, CG.gradient Q g₀ i ≠ 0)
    (hS : QuadraticEventInvariant Q g₀ constant S k) (hcap : k ≤ S.capacity)
    (length : ℝ) (hlength : length ≠ 0) (move : Bool)
    (htrial : practicalTrialParameter P S ≠ 0) :
    QuadraticEventInvariant Q g₀ constant
      (rawObservationEvent (practicalModel P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀) length move S) (k + 1) := by
  let f := quadraticObjective Q g₀ constant
  let G := quadraticGradient Q g₀
  let step := length • (practicalModel P S).direction
  let pair := observedTrialPair f G S step
  have hcapacity : S.pairs.length ≤ min S.capacity n := by rw [hS.count]; omega
  have hret := practical_quadratic_model_retains P Q hQ hpos g₀ constant S hS.faithful hS.independent hcapacity
  have hx : S.point ∈ directionFlag Q g₀ k := hS.flag ▸ hS.point_mem
  have hu := practical_quadratic_actual_trial P Q hQ hpos g₀ constant S k
    (fun i hi => hg i hi.le) hS.gradient hS.faithful hS.independent hS.flag hS.point_mem hS.count hcapacity
  have hstep : step = length • ((CG.displacement Q g₀ k - S.point) +
      practicalTrialParameter P S • CG.direction Q g₀ k) := by rw [← hu]
  have hnew : step ∉ directionFlag Q g₀ k := by
    rw [hstep]
    exact quadratic_observed_step_new Q hQ hpos g₀ k (fun i hi => hg i hi.le) (hg k le_rfl)
      S.point hx _ _ htrial hlength
  have hnonzero : step ≠ 0 := by
    intro hz
    exact hnew (hz ▸ (directionFlag Q g₀ k).zero_mem)
  have happend : appendPositive (practicalModel P S).pairs pair = S.pairs ++ [pair] := by
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
  have hcache := rawObservationEvent_cache (practicalModel P) f G length move S hS.value hS.gradient
  have hfaithful := rawObservationEvent_faithful (practicalModel P) f G
    (fun S' hS' => practicalModel_faithful P f G S' hS') length move S hS.value hS.gradient hS.faithful
  refine ⟨hcache.1, hcache.2, hfaithful, ?_, ?_, ?_, ?_⟩
  · cases move
    · change LinearIndependent ℝ (storedSteps (appendPositive (practicalModel P S).pairs pair))
      rw [happend]
      exact hind
    · change LinearIndependent ℝ (storedSteps ((appendPositive (practicalModel P S).pairs pair).map
        (fun P => P.transport step)))
      rw [happend]
      exact storedSteps_transport_independent _ step hind
  · cases move
    · change Submodule.span ℝ (range (storedSteps (appendPositive (practicalModel P S).pairs pair))) = _
      rw [happend]
      exact hflag
    · change Submodule.span ℝ (range (storedSteps ((appendPositive (practicalModel P S).pairs pair).map
        (fun P => P.transport step)))) = _
      rw [happend, storedSteps_transport]
      exact hflag
  · have hold : S.point ∈ Submodule.span ℝ (range (storedSteps (S.pairs ++ [pair]))) := by
      apply (Submodule.span_mono (by rw [storedSteps_append_range]; exact Set.subset_insert _ _)) hS.point_mem
    have hstepmem : step ∈ Submodule.span ℝ (range (storedSteps (S.pairs ++ [pair]))) :=
      Submodule.subset_span (by rw [storedSteps_append_range]; exact Or.inl rfl)
    cases move
    · change S.point ∈ Submodule.span ℝ (range (storedSteps (appendPositive (practicalModel P S).pairs pair)))
      rw [happend]
      exact hold
    · change S.point + step ∈ Submodule.span ℝ (range (storedSteps
        ((appendPositive (practicalModel P S).pairs pair).map (fun P => P.transport step))))
      rw [happend, storedSteps_transport]
      exact Submodule.add_mem _ hold hstepmem
  · cases move
    · change (appendPositive (practicalModel P S).pairs pair).length = k + 1
      rw [happend, List.length_append, List.length_singleton, hS.count]
    · change ((appendPositive (practicalModel P S).pairs pair).map
        (fun P => P.transport step)).length = k + 1
      rw [List.length_map, happend, List.length_append, List.length_singleton, hS.count]

end
end krylov.XR
