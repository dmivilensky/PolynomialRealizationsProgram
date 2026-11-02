import krylov.Convergence.EuclideanFullValueExecution
import krylov.XR.EuclideanGrowth

/-!
Article: main_krylov, cor:xrF, literal source-driven SS1-F phase.
Use: derive exact chronological retained observations from original selected
G1--G4, substitute the derived real value gates, and identify the actual
trajectory with the genuine SS1-F recursive executor and observable split.
Source: the actual selected-model clean phase, cached oracle invariants,
and elementary full-window chronological flushing. No successful-phase
or desired error recurrence is assumed.
-/

namespace krylov.Convergence
noncomputable section
open Matrix krylov.XR Filter Topology
open scoped InnerProductSpace

/-- Original selected-model source data force the actual static full-window
records to be exactly the last actual accepted endpoint observations. -/
theorem euclidean_source_full_observation_chronology {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (D : EuclideanGrowthSource P f G H x₀ center bounds) (hP : P.Valid n)
    (hmax : P.maximumCapacity=n) :
    ∃ K,∀ k,K≤k →
      staticObservations (euclideanAlgorithmModel P (euclideanAlgorithmRun P f G x₀ bounds (k+n))).pairs=
        List.ofFn (fun i : Fin n=>observePair f G (euclideanAlgorithmRun P f G x₀ bounds (k+i.val)).point
          ((euclideanAlgorithmRun P f G x₀ bounds (k+i.val+1)).point-
            (euclideanAlgorithmRun P f G x₀ bounds (k+i.val)).point)) := by
  let S := euclideanAlgorithmRun P f G x₀ bounds
  obtain ⟨K₁,hK₁⟩ := D.clean_pair_update hP
  obtain ⟨K₂,hK₂⟩ := D.eventually_maximum_window hP
  obtain ⟨K₃,hK₃⟩ := D.clean_phase hP
  let K := max K₁ (max K₂ K₃)
  have hret (k : ℕ) (hk : K≤k) :
      (euclideanAlgorithmModel P (S k)).pairs=retainNewest n (S k).pairs := by
    rw [(hK₃ k (by omega)).1]
    change retainNewest (min (S k).capacity n) (S k).pairs=_
    rw [(hK₂ k (by omega)).1,hmax,min_self]
  have hlen (k : ℕ) (hk : K≤k) : n≤(S k).pairs.length := by
    have hh := (hK₂ k (by omega)).2.1
    change (euclideanAlgorithmModel P (S k)).pairs.length=P.maximumCapacity at hh
    rw [hret k hk,retainNewest_length,hmax] at hh
    omega
  have hstep (k : ℕ) (hk : K≤k) : ∃ u : EuclideanSpace ℝ (Fin n),
      (S (k+1)).point=(S k).point+u ∧
      (S (k+1)).pairs=(retainNewest n (S k).pairs++[observedTrialPair f G (S k) u]).map
        (fun a=>a.transport u) := by
    have hh := hK₁ k (by omega)
    refine ⟨(euclideanAlgorithmModel P (S k)).direction,hh.1,?_⟩
    have hr : incomingWindow (S k)=retainNewest n (S k).pairs := by
      change retainNewest (min (S k).capacity n) (S k).pairs=_
      rw [(hK₂ k (by omega)).1,hmax,min_self]
    have hhpair := hh.2
    change (S (k+1)).pairs=(incomingWindow (S k)++[observedTrialPair f G (S k)
      (euclideanAlgorithmModel P (S k)).direction]).map (fun a=>a.transport (euclideanAlgorithmModel P (S k)).direction) at hhpair
    rw [hr] at hhpair
    exact hhpair
  refine ⟨K,fun k hk=>?_⟩
  rw [hret (k+n) (by omega)]
  apply clean_observation_window_flush f G S n K _ hlen hstep k hk
  intro j _hj
  have hc := run_cache_constants P n (euclideanAlgorithmModel P) f G
    (algorithmInitialState P f G x₀ bounds) rfl rfl j
  exact ⟨hc.1,hc.2.1⟩


/-- Original G1--G4 for the actual selected model force the literal XR-F
full-window recurrence, with every accepted point and split coming from
real endpoint observations. Both value gates are derived from the source. -/
theorem euclidean_source_full_ss1F_recursion {n : ℕ} (P : Parameters)
    (hon : P.valuesEnabled=true)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1))) (bounds : SpectralBounds)
    (D : EuclideanGrowthSource P f G H x₀ center bounds) (hP : P.Valid (n+1))
    (hmax : P.maximumCapacity=n+1) :
    ∃ K,∀ k,K≤k →
      (euclideanAlgorithmRun P f G x₀ bounds (k+n+2)).point=
        ss1FWindowRule f G ss1FEuclideanSplit
          (fun i : Fin (n+2)=>(euclideanAlgorithmRun P f G x₀ bounds (k+i.val)).point) := by
  let S := euclideanAlgorithmRun P f G x₀ bounds
  let x := fun k=>(S k).point
  obtain ⟨K₁,hK₁⟩ := euclidean_source_full_observation_chronology P f G H x₀ center bounds D hP hmax
  obtain ⟨K₂,hK₂⟩ := D.eventually_maximum_window hP
  obtain ⟨K₃,hK₃⟩ := D.clean_pair_update hP
  obtain ⟨K₄,hK₄⟩ := D.corrected_gates hP hon
  refine ⟨max K₁ (max K₂ (max K₃ K₄)),fun k hk=>?_⟩
  let W := (euclideanAlgorithmModel P (S (k+n+1))).pairs
  have hfull : W.length=n+1 := by
    simpa only [hmax] using (hK₂ (k+n+1) (by omega)).2.1
  have hrecords : staticObservations W=List.ofFn (fun i : Fin W.length=>
      observePair f G (x (k+i.val)) (x (k+i.val+1)-x (k+i.val))) := by
    have hc : staticObservations W=List.ofFn (fun i : Fin (n+1)=>
        observePair f G (x (k+i.val)) (x (k+i.val+1)-x (k+i.val))) := by
      simpa only [W,S,x,Nat.add_assoc] using hK₁ k (by omega)
    have he := List.ofFn_congr hfull (fun i : Fin W.length=>
      observePair f G (x (k+i.val)) (x (k+i.val+1)-x (k+i.val)))
    simp only [Fin.val_cast] at he
    exact hc.trans he.symm
  have hcache : (S (k+n+1)).gradient=G (S (k+n+1)).point :=
    (run_cache_constants P (n+1) (euclideanAlgorithmModel P) f G
      (algorithmInitialState P f G x₀ bounds) rfl rfl (k+n+1)).2.1
  have hfaith : ∀ a∈W,PairFaithful f G (S (k+n+1)).point a := by
    intro a ha
    exact euclideanAlgorithmRun_pairs_faithful P f G x₀ bounds (k+n+1) a
      (euclideanAlgorithmModel_pair_mem P (S (k+n+1)) a ha)
  have hsteps (i : Fin W.length) : storedSteps W i≠0 := by
    have hp := euclideanAlgorithmRun_pairs_positive P f G x₀ bounds (k+n+1) (W.get i)
      (euclideanAlgorithmModel_pair_mem P (S (k+n+1)) _ (List.get_mem _ i))
    exact positivePair_step_ne_zero _ hp
  have hpoint := (hK₃ (k+n+1) (by omega)).1
  change x (k+n+1+1)=x (k+n+1)+(euclideanAlgorithmModel P (S (k+n+1))).direction at hpoint
  have hgates := hK₄ (k+n+1) (by omega)
  have hraw := euclidean_algorithm_full_chronological_ss1FWindowRule P hon f G (S (k+n+1)) x k rfl hfull
    hcache hfaith hsteps hgates.1 hgates.2.1 hrecords
  rw [show k+n+2=k+n+1+1 by omega]
  exact hpoint.trans hraw

/-- A genuine selected-model XR-F source with full maximum capacity has an
actual accepted tail equal to the SS1-F recursive execution, with the
observable Euclidean split and its own actual accepted seed window. -/
theorem euclidean_source_full_eq_ss1FSequence {n : ℕ} (P : Parameters)
    (hon : P.valuesEnabled=true)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1))) (bounds : SpectralBounds)
    (D : EuclideanGrowthSource P f G H x₀ center bounds) (hP : P.Valid (n+1))
    (hmax : P.maximumCapacity=n+1) :
    ∃ K,∀ j,(euclideanAlgorithmRun P f G x₀ bounds (K+j)).point=
      ss1FSequence f G ss1FEuclideanSplit
        (fun i : Fin (n+2)=>(euclideanAlgorithmRun P f G x₀ bounds (K+i.val)).point) j := by
  obtain ⟨K,hK⟩ := euclidean_source_full_ss1F_recursion P hon f G H x₀ center bounds D hP hmax
  exact ⟨K,slidingSequence_shift_eq (ss1FWindowRule f G ss1FEuclideanSplit)
    (fun k=>(euclideanAlgorithmRun P f G x₀ bounds k).point) K hK⟩

end
end krylov.Convergence
