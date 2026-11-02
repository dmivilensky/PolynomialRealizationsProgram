import krylov.XR.PracticalGrowthFull
import krylov.Convergence.WindowSourceGain
import krylov.Convergence.WindowNativeValueRate

/-!
# Chronological SS1 and SS1-F dictionaries for practical XR

Article Theorem 7.3 and Corollary 7.4. After the source-derived full-memory
transition, the accepted points are the literal sliding secant executions.
This file reuses exact record flushing and index-cast lemmas; it does not
postulate either a desired query equation or an error recurrence.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods
open scoped InnerProductSpace
variable {n : ℕ}

/-- Selected practical observations remain genuine at the actual anchor. -/
theorem practicalModel_faithful (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n)))
    (hS : ∀ a ∈ S.pairs, PairFaithful f G S.point a) :
    ∀ a ∈ (practicalModel P S).pairs, PairFaithful f G S.point a :=
  fun a ha => hS a (practicalModel_pair_mem P S a ha)

/-- At full memory the actual practical ordinary query is SS1. -/
theorem practical_full_ss1Point (P : Parameters) (hoff : P.valuesEnabled = false)
    (S : State (EuclideanSpace ℝ (Fin n))) (hn : 0 < n)
    (hfull : (practicalModel P S).pairs.length = n) :
    S.point + (practicalModel P S).direction =
      krylov.Convergence.ss1Point (storedSteps (practicalModel P S).pairs)
        (storedImages (practicalModel P S).pairs) S.gradient S.point := by
  rw [practicalModel_full P S hn hfull, selectedModel_values_off P hoff]
  rfl

/-- At full memory the practical corrected query is the raw SS1-F map
when its actual scalar and Hermitian gates have been derived. -/
theorem practical_full_ss1FPoint (P : Parameters) (hon : P.valuesEnabled = true)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) (hn : 0 < n)
    (hfull : (practicalModel P S).pairs.length = n) (hg : S.gradient = G S.point)
    (hW : ∀ a ∈ (practicalModel P S).pairs, PairFaithful f G S.point a)
    (hgate : ∀ i : Fin (practicalModel P S).pairs.length,
      |12 * storedSplit (practicalModel P S).pairs i * ((practicalModel P S).pairs.get i).valueDefect| ≤
        storedPairing (practicalModel P S).pairs i i / 2)
    (hpass : correctedWindowPasses P.windowThreshold (practicalModel P S).pairs) :
    S.point + (practicalModel P S).direction =
      krylov.Convergence.ss1FPoint f G (storedAnchors (practicalModel P S).pairs)
        (storedSteps (practicalModel P S).pairs) (storedSplit (practicalModel P S).pairs) S.point := by
  have hselected : selectedModel P (practicalModel P S).pairs = storedValueModel (practicalModel P S).pairs :=
    ite_eq_left ⟨hon, hpass⟩
  rw [practicalModel_full P S hn hfull, hselected,
    storedValueModel_eq_actual f G S.point _ hW hgate, hg]
  rfl

end
end krylov.XR

namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.XR krylov.Functions krylov.Methods Filter Topology
open scoped InnerProductSpace
set_option maxHeartbeats 800000

/-- The actual full XR-F candidate, on an actual chronological accepted
window, is literally the genuine SS1-F window rule with the observable
split policy. All gates refer to its real cached data. -/
theorem practical_full_chronological_ss1FWindowRule {n : ℕ} (P : Parameters)
    (hon : P.valuesEnabled=true)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (S : State (EuclideanSpace ℝ (Fin (n+1))))
    (x : ℕ → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ)
    (hx : S.point=x (k+n+1))
    (hfull : (practicalModel P S).pairs.length=n+1)
    (hg : S.gradient=G S.point)
    (hfaith : ∀ a∈(practicalModel P S).pairs,PairFaithful f G S.point a)
    (hden : ∀ i,storedPairing (practicalModel P S).pairs i i≠0)
    (hgate : ∀ i,|12*storedSplit (practicalModel P S).pairs i*
      ((practicalModel P S).pairs.get i).valueDefect|≤storedPairing (practicalModel P S).pairs i i/2)
    (hpass : correctedWindowPasses P.windowThreshold (practicalModel P S).pairs)
    (hrecords : staticObservations (practicalModel P S).pairs=List.ofFn
      (fun i : Fin (practicalModel P S).pairs.length=>
        observePair f G (x (k+i.val)) (x (k+i.val+1)-x (k+i.val)))) :
    S.point+(practicalModel P S).direction=
      ss1FWindowRule f G (ss1FObservedSplit G) (fun i : Fin (n+2)=>x (k+i.val)) := by
  let W := (practicalModel P S).pairs
  have hp := practical_full_ss1FPoint P hon f G S (by omega) hfull hg hfaith hgate hpass
  rw [ss1FPoint_chronological_records f G W x k S.point hrecords hfaith hden,hx] at hp
  rw [ss1FPoint_fin_cast hfull] at hp
  change S.point+(practicalModel P S).direction=
    ss1FPoint f G (fun i : Fin (n+1)=>x (k+i.val))
      (fun i=>x (k+i.val+1)-x (k+i.val))
      (fun i=>covectorSplit (innerSL ℝ (G (x (k+i.val+1))-G (x (k+i.val))))
        (x (k+i.val)) (x (k+i.val+1)-x (k+i.val)) (x (k+n+1))) (x (k+n+1))
  rw [hx]
  simpa only [windowAnchor,windowStep,windowImage,Fin.val_cast] using hp


/-- Original selected-model source data force the actual static full-window
records to be exactly the last actual accepted endpoint observations. -/
theorem practical_source_full_observation_chronology {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (D : PracticalGrowthSource P f G H x₀ center) (hP : P.Valid n)
    (hmax : P.maximumCapacity=n) :
    ∃ K,∀ k,K≤k →
      staticObservations (practicalModel P (practicalRun P f G x₀ (k+n))).pairs=
        List.ofFn (fun i : Fin n=>observePair f G (practicalRun P f G x₀ (k+i.val)).point
          ((practicalRun P f G x₀ (k+i.val+1)).point-
            (practicalRun P f G x₀ (k+i.val)).point)) := by
  let S := practicalRun P f G x₀
  obtain ⟨K₁,hK₁⟩ := D.clean_pair_update hP
  obtain ⟨K₂,hK₂⟩ := D.eventually_maximum_window hP
  obtain ⟨K₃,hK₃⟩ := D.clean_phase hP
  let K := max K₁ (max K₂ K₃)
  have hret (k : ℕ) (hk : K≤k) :
      (practicalModel P (S k)).pairs=retainNewest n (S k).pairs := by
    rw [(hK₃ k (by omega)).1]
    change retainNewest (min (S k).capacity n) (S k).pairs=_
    rw [(hK₂ k (by omega)).1,hmax,min_self]
  have hlen (k : ℕ) (hk : K≤k) : n≤(S k).pairs.length := by
    have hh := (hK₂ k (by omega)).2.1
    change (practicalModel P (S k)).pairs.length=P.maximumCapacity at hh
    rw [hret k hk,retainNewest_length,hmax] at hh
    omega
  have hstep (k : ℕ) (hk : K≤k) : ∃ u : EuclideanSpace ℝ (Fin n),
      (S (k+1)).point=(S k).point+u ∧
      (S (k+1)).pairs=(retainNewest n (S k).pairs++[observedTrialPair f G (S k) u]).map
        (fun a=>a.transport u) := by
    have hh := hK₁ k (by omega)
    refine ⟨(practicalModel P (S k)).direction,hh.1,?_⟩
    have hr : incomingWindow (S k)=retainNewest n (S k).pairs := by
      change retainNewest (min (S k).capacity n) (S k).pairs=_
      rw [(hK₂ k (by omega)).1,hmax,min_self]
    have hhpair := hh.2
    change (S (k+1)).pairs=(incomingWindow (S k)++[observedTrialPair f G (S k)
      (practicalModel P (S k)).direction]).map (fun a=>a.transport (practicalModel P (S k)).direction) at hhpair
    rw [hr] at hhpair
    exact hhpair
  refine ⟨K,fun k hk=>?_⟩
  rw [hret (k+n) (by omega)]
  apply clean_observation_window_flush f G S n K _ hlen hstep k hk
  intro j _hj
  have hc := run_cache_constants P n (practicalModel P) f G
    (algorithmInitialState P f G x₀ none) rfl rfl j
  exact ⟨hc.1,hc.2.1⟩


/-- Original G1--G4 for the actual selected model force the literal XR-F
full-window recurrence, with every accepted point and split coming from
real endpoint observations. Both value gates are derived from the source. -/
theorem practical_source_full_ss1F_recursion {n : ℕ} (P : Parameters)
    (hon : P.valuesEnabled=true)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1)))
    (D : PracticalGrowthSource P f G H x₀ center) (hP : P.Valid (n+1))
    (hmax : P.maximumCapacity=n+1) :
    ∃ K,∀ k,K≤k →
      (practicalRun P f G x₀ (k+n+2)).point=
        ss1FWindowRule f G (ss1FObservedSplit G)
          (fun i : Fin (n+2)=>(practicalRun P f G x₀ (k+i.val)).point) := by
  let S := practicalRun P f G x₀
  let x := fun k=>(S k).point
  obtain ⟨K₁,hK₁⟩ := practical_source_full_observation_chronology P f G H x₀ center D hP hmax
  obtain ⟨K₂,hK₂⟩ := D.eventually_maximum_window hP
  obtain ⟨K₃,hK₃⟩ := D.clean_pair_update hP
  obtain ⟨K₄,hK₄⟩ := D.corrected_gates hP hon
  refine ⟨max K₁ (max K₂ (max K₃ K₄)),fun k hk=>?_⟩
  let W := (practicalModel P (S (k+n+1))).pairs
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
    (run_cache_constants P (n+1) (practicalModel P) f G
      (algorithmInitialState P f G x₀ none) rfl rfl (k+n+1)).2.1
  have hfaith : ∀ a∈W,PairFaithful f G (S (k+n+1)).point a :=
    practicalModel_faithful P f G (S (k+n+1)) (practicalRun_pairs_faithful P f G x₀ (k+n+1))
  have hden (i : Fin W.length) : storedPairing W i i≠0 := by
    have hp := practicalRun_pairs_positive P f G x₀ (k+n+1) (W.get i)
      (practicalModel_pair_mem P (S (k+n+1)) _ (List.get_mem _ i))
    exact ne_of_gt hp
  have hpoint := (hK₃ (k+n+1) (by omega)).1
  change x (k+n+1+1)=x (k+n+1)+(practicalModel P (S (k+n+1))).direction at hpoint
  have hgates := hK₄ (k+n+1) (by omega)
  have hraw := practical_full_chronological_ss1FWindowRule P hon f G (S (k+n+1)) x k rfl hfull
    hcache hfaith hden hgates.1 hgates.2.1 hrecords
  rw [show k+n+2=k+n+1+1 by omega]
  exact hpoint.trans hraw

/-- A genuine selected-model XR-F source with full maximum capacity has an
actual accepted tail equal to the SS1-F recursive execution, with the
observable covector split and its own actual accepted seed window. -/
theorem practical_source_full_eq_ss1FSequence {n : ℕ} (P : Parameters)
    (hon : P.valuesEnabled=true)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1)))
    (D : PracticalGrowthSource P f G H x₀ center) (hP : P.Valid (n+1))
    (hmax : P.maximumCapacity=n+1) :
    ∃ K,∀ j,(practicalRun P f G x₀ (K+j)).point=
      ss1FSequence f G (ss1FObservedSplit G)
        (fun i : Fin (n+2)=>(practicalRun P f G x₀ (K+i.val)).point) j := by
  obtain ⟨K,hK⟩ := practical_source_full_ss1F_recursion P hon f G H x₀ center D hP hmax
  exact ⟨K,slidingSequence_shift_eq (ss1FWindowRule f G (ss1FObservedSplit G))
    (fun k=>(practicalRun P f G x₀ k).point) K hK⟩


/-- Under the original source hypotheses, the full-memory XR update is
literally the actual SS1 map on the last accepted chronological window. -/
theorem practical_source_full_ss1_recursion {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1)))
    (D : PracticalGrowthSource P f G H x₀ center) (hP : P.Valid (n+1))
    (hoff : P.valuesEnabled=false) (hmax : P.maximumCapacity=n+1) :
    ∃ K,∀ k,K≤k →
      (practicalRun P f G x₀ (k+n+2)).point=
        ss1WindowRule G (fun i : Fin (n+2)=>(practicalRun P f G x₀ (k+i.val)).point) := by
  let S := practicalRun P f G x₀
  let x := fun k=>(S k).point
  obtain ⟨K₁,hK₁⟩ := practical_source_full_observation_chronology P f G H x₀ center D hP hmax
  obtain ⟨K₂,hK₂⟩ := D.eventually_maximum_window hP
  obtain ⟨K₃,hK₃⟩ := D.clean_pair_update hP
  refine ⟨max K₁ (max K₂ K₃),fun k hk=>?_⟩
  let W := (practicalModel P (S (k+n+1))).pairs
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
  have hcache : (S (k+n+1)).gradient=G (x (k+n+1)) := by
    exact (run_cache_constants P (n+1) (practicalModel P) f G
      (algorithmInitialState P f G x₀ none) rfl rfl (k+n+1)).2.1
  have hpoint := (hK₃ (k+n+1) (by omega)).1
  change x (k+n+1+1)=x (k+n+1)+(practicalModel P (S (k+n+1))).direction at hpoint
  have hraw := practical_full_ss1Point P hoff (S (k+n+1)) (by omega) hfull
  rw [hcache,ss1Point_chronological_records f G W x k hrecords] at hraw
  have hraw' : x (k+n+1)+(practicalModel P (S (k+n+1))).direction=
      ss1Point (windowStep (n:=n+1) x k) (windowImage G x k) (G (x (k+n+1))) (x (k+n+1)) := by
    rw [ss1Point_fin_cast hfull] at hraw
    change x (k+n+1)+(practicalModel P (S (k+n+1))).direction=
      ss1Point (fun i : Fin (n+1)=>x (k+i.val+1)-x (k+i.val))
        (fun i=>G (x (k+i.val+1))-G (x (k+i.val))) (G (x (k+n+1))) (x (k+n+1))
    simpa only [windowStep,windowImage,Fin.val_cast] using hraw
  rw [show k+n+2=k+n+1+1 by omega]
  exact hpoint.trans hraw'

/-- A concrete XR source with full capacity has an actual tail equal to
the genuine SS1 recursive executor, initialized with its own observed
accepted points. This closes the algorithm-to-method dictionary. -/
theorem practical_source_full_eq_ss1Sequence {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1)))
    (D : PracticalGrowthSource P f G H x₀ center) (hP : P.Valid (n+1))
    (hoff : P.valuesEnabled=false) (hmax : P.maximumCapacity=n+1) :
    ∃ K,∀ j,(practicalRun P f G x₀ (K+j)).point=
      ss1Sequence G (fun i : Fin (n+2)=>(practicalRun P f G x₀ (K+i.val)).point) j := by
  obtain ⟨K,hK⟩ := practical_source_full_ss1_recursion P f G H x₀ center D hP hoff hmax
  exact ⟨K,slidingSequence_shift_eq (ss1WindowRule G)
    (fun k=>(practicalRun P f G x₀ k).point) K hK⟩


/-- The same original incoming gain is preserved when value correction
is enabled; the successful phase is derived from the selected-model source. -/
theorem practical_source_full_window_gain {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (D : PracticalGrowthSource P f G H x₀ center) (hP : P.Valid n)
    (hmax : P.maximumCapacity=n) :
    ∀ᶠ k in atTop,∀ c : Fin n → ℝ,
      D.sigma^2*‖WithLp.toLp 2 c‖^2≤
        ‖combine (unitWindow (windowStep (fun j=>(practicalRun P f G x₀ j).point) k)) c‖^2 := by
  obtain ⟨K₁,hK₁⟩ := practical_source_full_observation_chronology P f G H x₀ center D hP hmax
  obtain ⟨K₂,hK₂⟩ := D.clean_phase hP
  filter_upwards [eventually_ge_atTop (max D.gainStart (max K₁ K₂))] with k hk c
  apply gain_chronological_records f G _ _ k (hK₁ k (by omega)) _ c
  rw [(hK₂ (k+n) (by omega)).1]
  exact D.gain (k+n) (by omega)

end
end krylov.Convergence
