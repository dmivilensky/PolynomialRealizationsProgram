import krylov.XR.EuclideanPracticalFull
import krylov.Convergence.EuclideanFullValueExecution
import krylov.Convergence.EuclideanWindowExecution

/-!
# Chronological SS1-F dictionary for Euclidean practical XR-F

Article: Corollary 7.4 [cor:xrF] of krylov.tex.
The local source forces a clean full window and its real value gates. The
accepted trajectory is then identified with the literal Euclidean SS1-F
recursion, using its genuine cached endpoint records and observed seed.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant krylov.Functions
open scoped InnerProductSpace

/-- Selected practical observations are faithful at the actual anchor. -/
theorem euclideanPracticalModel_faithful {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n)))
    (hS : ∀ a ∈ S.pairs, PairFaithful f G S.point a) :
    ∀ a ∈ (euclideanPracticalModel P S).pairs, PairFaithful f G S.point a :=
  fun a ha => hS a (euclideanPracticalModel_pair_mem P S a ha)

/-- The full actual corrected XR branch is precisely the data-only SS1-F
query, after source estimates have forced both genuine value gates. -/
theorem euclideanPractical_full_ss1FPoint {n : ℕ} (P : Parameters) (hon : P.valuesEnabled = true)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) (hn : 0 < n)
    (hfull : (euclideanPracticalModel P S).pairs.length = n) (hg : S.gradient = G S.point)
    (hW : ∀ a ∈ (euclideanPracticalModel P S).pairs, PairFaithful f G S.point a)
    (hgate : ∀ i : Fin (euclideanPracticalModel P S).pairs.length,
      |12 * euclideanStoredSplit S.point (euclideanPracticalModel P S).pairs i * ((euclideanPracticalModel P S).pairs.get i).valueDefect| ≤
        storedPairing (euclideanPracticalModel P S).pairs i i / 2)
    (hpass : euclideanCorrectedWindowPasses P.windowThreshold S.point (euclideanPracticalModel P S).pairs) :
    S.point + (euclideanPracticalModel P S).direction =
      krylov.Convergence.ss1FPoint f G (storedAnchors (euclideanPracticalModel P S).pairs)
        (storedSteps (euclideanPracticalModel P S).pairs) (euclideanStoredSplit S.point (euclideanPracticalModel P S).pairs) S.point  := by
  have hselected : selectedEuclideanModel P S.point (euclideanPracticalModel P S).pairs =
      euclideanStoredValueModel S.point (euclideanPracticalModel P S).pairs := ite_eq_left ⟨hon, hpass⟩
  rw [euclideanPracticalModel_full P S hn hfull, hselected,
    euclideanStoredValueModel_eq_actual f G S.point _ hW hgate, hg]
  rfl

end
end krylov.XR

namespace krylov.Convergence
noncomputable section
open Matrix krylov.XR krylov.Functions
open scoped InnerProductSpace
/-- The actual full XR-F candidate, on an actual chronological accepted
window, is literally the genuine SS1-F window rule with the observable
split policy. All gates refer to its real cached data. -/
theorem euclideanPractical_full_chronological_ss1FWindowRule {n : ℕ} (P : Parameters)
    (hon : P.valuesEnabled=true)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (S : State (EuclideanSpace ℝ (Fin (n+1))))
    (x : ℕ → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ)
    (hx : S.point=x (k+n+1))
    (hfull : (euclideanPracticalModel P S).pairs.length=n+1)
    (hg : S.gradient=G S.point)
    (hfaith : ∀ a∈(euclideanPracticalModel P S).pairs,PairFaithful f G S.point a)
    (hsteps : ∀ i,storedSteps (euclideanPracticalModel P S).pairs i≠0)
    (hgate : ∀ i,|12*euclideanStoredSplit S.point (euclideanPracticalModel P S).pairs i*
      ((euclideanPracticalModel P S).pairs.get i).valueDefect|≤storedPairing (euclideanPracticalModel P S).pairs i i/2)
    (hpass : euclideanCorrectedWindowPasses P.windowThreshold S.point (euclideanPracticalModel P S).pairs)
    (hrecords : staticObservations (euclideanPracticalModel P S).pairs=List.ofFn
      (fun i : Fin (euclideanPracticalModel P S).pairs.length=>
        observePair f G (x (k+i.val)) (x (k+i.val+1)-x (k+i.val)))) :
    S.point+(euclideanPracticalModel P S).direction=
      ss1FWindowRule f G ss1FEuclideanSplit (fun i : Fin (n+2)=>x (k+i.val)) := by
  let W := (euclideanPracticalModel P S).pairs
  have hp := euclideanPractical_full_ss1FPoint P hon f G S (by omega) hfull hg hfaith hgate hpass
  rw [euclidean_ss1FPoint_chronological_records f G W x k S.point hrecords hfaith hsteps,hx] at hp
  rw [ss1FPoint_fin_cast hfull] at hp
  change S.point+(euclideanPracticalModel P S).direction=
    ss1FPoint f G (fun i : Fin (n+1)=>x (k+i.val))
      (fun i=>x (k+i.val+1)-x (k+i.val))
      (fun i=>innerSplit (x (k+i.val)) (x (k+i.val+1)-x (k+i.val)) (x (k+n+1))) (x (k+n+1))
  rw [hx]
  simpa only [windowAnchor,windowStep,windowImage,Fin.val_cast] using hp

end
end krylov.Convergence

namespace krylov.Convergence
noncomputable section
open Matrix krylov.XR Filter Topology
open scoped InnerProductSpace

/-- Original selected-model source data force the actual static full-window
records to be exactly the last actual accepted endpoint observations. -/
theorem euclideanPractical_source_full_observation_chronology {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (D : EuclideanPracticalGrowthSource P f G H x₀ center) (hP : P.Valid n)
    (hmax : P.maximumCapacity=n) :
    ∃ K,∀ k,K≤k →
      staticObservations (euclideanPracticalModel P (euclideanPracticalRun P f G x₀ (k+n))).pairs=
        List.ofFn (fun i : Fin n=>observePair f G (euclideanPracticalRun P f G x₀ (k+i.val)).point
          ((euclideanPracticalRun P f G x₀ (k+i.val+1)).point-
            (euclideanPracticalRun P f G x₀ (k+i.val)).point)) := by
  let S := euclideanPracticalRun P f G x₀
  obtain ⟨K₁,hK₁⟩ := D.clean_pair_update hP
  obtain ⟨K₂,hK₂⟩ := D.eventually_maximum_window hP
  obtain ⟨K₃,hK₃⟩ := D.clean_phase hP
  let K := max K₁ (max K₂ K₃)
  have hret (k : ℕ) (hk : K≤k) :
      (euclideanPracticalModel P (S k)).pairs=retainNewest n (S k).pairs := by
    rw [(hK₃ k (by omega)).1]
    change retainNewest (min (S k).capacity n) (S k).pairs=_
    rw [(hK₂ k (by omega)).1,hmax,min_self]
  have hlen (k : ℕ) (hk : K≤k) : n≤(S k).pairs.length := by
    have hh := (hK₂ k (by omega)).2.1
    change (euclideanPracticalModel P (S k)).pairs.length=P.maximumCapacity at hh
    rw [hret k hk,retainNewest_length,hmax] at hh
    omega
  have hstep (k : ℕ) (hk : K≤k) : ∃ u : EuclideanSpace ℝ (Fin n),
      (S (k+1)).point=(S k).point+u ∧
      (S (k+1)).pairs=(retainNewest n (S k).pairs++[observedTrialPair f G (S k) u]).map
        (fun a=>a.transport u) := by
    have hh := hK₁ k (by omega)
    refine ⟨(euclideanPracticalModel P (S k)).direction,hh.1,?_⟩
    have hr : incomingWindow (S k)=retainNewest n (S k).pairs := by
      change retainNewest (min (S k).capacity n) (S k).pairs=_
      rw [(hK₂ k (by omega)).1,hmax,min_self]
    have hhpair := hh.2
    change (S (k+1)).pairs=(incomingWindow (S k)++[observedTrialPair f G (S k)
      (euclideanPracticalModel P (S k)).direction]).map (fun a=>a.transport (euclideanPracticalModel P (S k)).direction) at hhpair
    rw [hr] at hhpair
    exact hhpair
  refine ⟨K,fun k hk=>?_⟩
  rw [hret (k+n) (by omega)]
  apply clean_observation_window_flush f G S n K _ hlen hstep k hk
  intro j _hj
  have hc := run_cache_constants P n (euclideanPracticalModel P) f G
    (algorithmInitialState P f G x₀ none) rfl rfl j
  exact ⟨hc.1,hc.2.1⟩


/-- Original G1--G4 for the actual selected model force the literal XR-F
full-window recurrence, with every accepted point and split coming from
real endpoint observations. Both value gates are derived from the source. -/
theorem euclideanPractical_source_full_ss1F_recursion {n : ℕ} (P : Parameters)
    (hon : P.valuesEnabled=true)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1)))
    (D : EuclideanPracticalGrowthSource P f G H x₀ center) (hP : P.Valid (n+1))
    (hmax : P.maximumCapacity=n+1) :
    ∃ K,∀ k,K≤k →
      (euclideanPracticalRun P f G x₀ (k+n+2)).point=
        ss1FWindowRule f G ss1FEuclideanSplit
          (fun i : Fin (n+2)=>(euclideanPracticalRun P f G x₀ (k+i.val)).point) := by
  let S := euclideanPracticalRun P f G x₀
  let x := fun k=>(S k).point
  obtain ⟨K₁,hK₁⟩ := euclideanPractical_source_full_observation_chronology P f G H x₀ center D hP hmax
  obtain ⟨K₂,hK₂⟩ := D.eventually_maximum_window hP
  obtain ⟨K₃,hK₃⟩ := D.clean_pair_update hP
  obtain ⟨K₄,hK₄⟩ := D.corrected_gates hP hon
  refine ⟨max K₁ (max K₂ (max K₃ K₄)),fun k hk=>?_⟩
  let W := (euclideanPracticalModel P (S (k+n+1))).pairs
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
    (run_cache_constants P (n+1) (euclideanPracticalModel P) f G
      (algorithmInitialState P f G x₀ none) rfl rfl (k+n+1)).2.1
  have hfaith : ∀ a∈W,PairFaithful f G (S (k+n+1)).point a := by
    intro a ha
    exact euclideanPracticalRun_pairs_faithful P f G x₀ (k+n+1) a
      (euclideanPracticalModel_pair_mem P (S (k+n+1)) a ha)
  have hsteps (i : Fin W.length) : storedSteps W i≠0 := by
    have hp := euclideanPracticalRun_pairs_positive P f G x₀ (k+n+1) (W.get i)
      (euclideanPracticalModel_pair_mem P (S (k+n+1)) _ (List.get_mem _ i))
    exact positivePair_step_ne_zero _ hp
  have hpoint := (hK₃ (k+n+1) (by omega)).1
  change x (k+n+1+1)=x (k+n+1)+(euclideanPracticalModel P (S (k+n+1))).direction at hpoint
  have hgates := hK₄ (k+n+1) (by omega)
  have hraw := euclideanPractical_full_chronological_ss1FWindowRule P hon f G (S (k+n+1)) x k rfl hfull
    hcache hfaith hsteps hgates.1 hgates.2.1 hrecords
  rw [show k+n+2=k+n+1+1 by omega]
  exact hpoint.trans hraw

/-- A genuine selected-model XR-F source with full maximum capacity has an
actual accepted tail equal to the SS1-F recursive execution, with the
observable Euclidean split and its own actual accepted seed window. -/
theorem euclideanPractical_source_full_eq_ss1FSequence {n : ℕ} (P : Parameters)
    (hon : P.valuesEnabled=true)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1)))
    (D : EuclideanPracticalGrowthSource P f G H x₀ center) (hP : P.Valid (n+1))
    (hmax : P.maximumCapacity=n+1) :
    ∃ K,∀ j,(euclideanPracticalRun P f G x₀ (K+j)).point=
      ss1FSequence f G ss1FEuclideanSplit
        (fun i : Fin (n+2)=>(euclideanPracticalRun P f G x₀ (K+i.val)).point) j := by
  obtain ⟨K,hK⟩ := euclideanPractical_source_full_ss1F_recursion P hon f G H x₀ center D hP hmax
  exact ⟨K,slidingSequence_shift_eq (ss1FWindowRule f G ss1FEuclideanSplit)
    (fun k=>(euclideanPracticalRun P f G x₀ k).point) K hK⟩

end
end krylov.Convergence
