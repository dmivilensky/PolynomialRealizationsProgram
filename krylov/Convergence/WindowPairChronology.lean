import krylov.Convergence.WindowChronology
import krylov.XR.GrowthSource

/-!
Article: main_krylov, thm:grow and cor:xrF, literal memory chronology.
Use: erase only the transported anchor pairing, which is independently
known to be faithful, and prove that all remaining observations are exactly
the last actual accepted observations. Source: the proved clean append
transition of XR and elementary full-window list flushing.
-/

namespace krylov.Convergence
noncomputable section
open krylov.XR
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Static endpoint observations, before the separate current-anchor
pairing is transported. All true values and gradient secants are retained. -/
def staticObservation (a : PairObservation E) : PairObservation E :=
  {a with anchorPairing:=0}

/-- The static data of a genuine stored list. -/
def staticObservations (W : List (PairObservation E)) : List (PairObservation E) :=
  W.map staticObservation

theorem staticObservations_transport (W : List (PairObservation E)) (u : E) :
    staticObservations (W.map (fun a=>a.transport u))=staticObservations W := by
  simp only [staticObservations,List.map_map]
  congr 1

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem staticObservations_retain (W : List (PairObservation E)) (m : ℕ) :
    staticObservations (retainNewest m W)=
      (staticObservations W).drop ((staticObservations W).length-m) := by
  simp only [staticObservations,retainNewest,List.map_drop,List.length_map]

/- An equality of actual chronological static records determines each
real cached endpoint record, without any choice of representative. -/
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem staticObservations_get (W : List (PairObservation E))
    (q : Fin W.length → PairObservation E) (h : staticObservations W=List.ofFn q)
    (i : Fin W.length) : staticObservation (W.get i)=q i := by
  have hh := congrArg (fun L : List (PairObservation E)=>L[i.val]?) h
  simpa only [staticObservations,List.getElem?_map,List.getElem?_eq_getElem i.isLt,
    Option.map_some,List.getElem?_ofFn,dite_eq_left i.isLt,Option.some.injEq,List.get_eq_getElem] using hh

/-- The actual step and image arrays of a flushed chronological window
are exactly the arrays of the genuine consecutive accepted points. -/
theorem ss1Point_chronological_records (f : E → ℝ) (G : E → E)
    (W : List (PairObservation E)) (x : ℕ → E) (k : ℕ)
    (h : staticObservations W=List.ofFn (fun i : Fin W.length=>
      observePair f G (x (k+i.val)) (x (k+i.val+1)-x (k+i.val)))) (g z : E) :
    ss1Point (storedSteps W) (storedImages W) g z=
      ss1Point (windowStep (n:=W.length) x k) (windowImage G x k) g z := by
  have hs : storedSteps W=windowStep x k := by
    funext i
    exact congrArg PairObservation.step (staticObservations_get W _ h i)
  have hy : storedImages W=windowImage G x k := by
    funext i
    have hh := congrArg PairObservation.image (staticObservations_get W _ h i)
    simpa only [staticObservation,observePair,storedImages,windowImage,add_sub_cancel] using hh
  rw [hs,hy]

/-- Relabeling a finite observed array by an equality of lengths leaves
the genuine SS1 physical query exactly unchanged. -/
theorem ss1Point_fin_cast {m n : ℕ} (h : m=n) (s y : Fin m → E) (g x : E) :
    ss1Point s y g x=ss1Point (fun i : Fin n=>s (Fin.cast h.symm i))
      (fun i=>y (Fin.cast h.symm i)) g x := by
  subst n
  rfl

/-- Flush the actual observed records of a clean finite-capacity execution.
The premises describe its literal list transition, never an error rate. -/
theorem clean_observation_window_flush (f : E → ℝ) (G : E → E)
    (S : ℕ → State E) (m K : ℕ)
    (hcache : ∀ k,K≤k → (S k).value=f (S k).point ∧(S k).gradient=G (S k).point)
    (hlen : ∀ k,K≤k → m≤(S k).pairs.length)
    (hstep : ∀ k,K≤k → ∃ u : E,(S (k+1)).point=(S k).point+u ∧
      (S (k+1)).pairs=(retainNewest m (S k).pairs++[observedTrialPair f G (S k) u]).map
        (fun a=>a.transport u))
    (k : ℕ) (hk : K≤k) :
    staticObservations (retainNewest m (S (k+m)).pairs)=
      List.ofFn (fun i : Fin m=>observePair f G (S (k+i.val)).point
        ((S (k+i.val+1)).point-(S (k+i.val)).point)) := by
  let L := fun j=>staticObservations (S j).pairs
  let a := fun j=>observePair f G (S j).point ((S (j+1)).point-(S j).point)
  have hlen' : ∀ j,K≤j → m≤(L j).length := by
    intro j hj
    simpa only [L,staticObservations,List.length_map] using hlen j hj
  have hstep' : ∀ j,K≤j → L (j+1)=(L j).drop ((L j).length-m)++[a j] := by
    intro j hj
    obtain ⟨u,hpoint,hpairs⟩ := hstep j hj
    have hc := hcache j hj
    change staticObservations (S (j+1)).pairs=_
    rw [hpairs,staticObservations_transport]
    simp only [staticObservations,List.map_append,List.map_cons,List.map_nil]
    rw [←staticObservations,staticObservations_retain]
    congr 1
    dsimp only [a,staticObservation,observedTrialPair,observePair]
    rw [hpoint,add_sub_cancel_left,hc.1,hc.2]
  rw [staticObservations_retain]
  exact chronological_window_flush L a m K hlen' hstep' k hk

/-- Original G1--G4 source data force the concrete full-memory algorithm's
retained endpoint records to be precisely one full window of its actual
accepted observations. No clean-phase premise is left in this theorem. -/
theorem source_full_observation_chronology {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (D : GrowthSource P f G H x₀ center bounds) (hP : P.Valid n)
    (hoff : P.valuesEnabled=false) (hmax : P.maximumCapacity=n) :
    ∃ K,∀ k,K≤k →
      staticObservations (algorithmModel P (algorithmRun P f G x₀ bounds (k+n))).pairs=
        List.ofFn (fun i : Fin n=>observePair f G (algorithmRun P f G x₀ bounds (k+i.val)).point
          ((algorithmRun P f G x₀ bounds (k+i.val+1)).point-
            (algorithmRun P f G x₀ bounds (k+i.val)).point)) := by
  let S := algorithmRun P f G x₀ bounds
  obtain ⟨K₁,hK₁⟩ := D.clean_pair_update hP hoff
  obtain ⟨K₂,hK₂⟩ := D.eventually_maximum_window hP hoff
  obtain ⟨K₃,hK₃⟩ := D.clean_phase hP hoff
  let K := max K₁ (max K₂ K₃)
  have hret (k : ℕ) (hk : K≤k) :
      (algorithmModel P (S k)).pairs=retainNewest n (S k).pairs := by
    rw [(hK₃ k (by omega)).1]
    change retainNewest (min (S k).capacity n) (S k).pairs=_
    rw [(hK₂ k (by omega)).1,hmax,min_self]
  have hlen (k : ℕ) (hk : K≤k) : n≤(S k).pairs.length := by
    have hh := (hK₂ k (by omega)).2.1
    change (algorithmModel P (S k)).pairs.length=P.maximumCapacity at hh
    rw [hret k hk,retainNewest_length,hmax] at hh
    omega
  have hstep (k : ℕ) (hk : K≤k) : ∃ u : EuclideanSpace ℝ (Fin n),
      (S (k+1)).point=(S k).point+u ∧
      (S (k+1)).pairs=(retainNewest n (S k).pairs++[observedTrialPair f G (S k) u]).map
        (fun a=>a.transport u) := by
    have hh := hK₁ k (by omega)
    refine ⟨(algorithmModel P (S k)).direction,hh.1,?_⟩
    have hr : incomingWindow (S k)=retainNewest n (S k).pairs := by
      change retainNewest (min (S k).capacity n) (S k).pairs=_
      rw [(hK₂ k (by omega)).1,hmax,min_self]
    have hhpair := hh.2
    change (S (k+1)).pairs=(incomingWindow (S k)++[observedTrialPair f G (S k)
      (algorithmModel P (S k)).direction]).map (fun a=>a.transport (algorithmModel P (S k)).direction) at hhpair
    rw [hr] at hhpair
    exact hhpair
  refine ⟨K,fun k hk=>?_⟩
  rw [hret (k+n) (by omega)]
  apply clean_observation_window_flush f G S n K _ hlen hstep k hk
  intro j _hj
  have hc := run_cache_constants P n (algorithmModel P) f G
    (algorithmInitialState P f G x₀ bounds) rfl rfl j
  exact ⟨hc.1,hc.2.1⟩

end
end krylov.Convergence
