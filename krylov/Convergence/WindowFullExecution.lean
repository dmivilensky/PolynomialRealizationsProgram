import krylov.Convergence.WindowPairChronology

/-!
Article: main_krylov, thm:grow, literal full-window SS1 phase.
Use: identify the actual source-driven full-memory XR trajectory with the
existing genuine recursive SS1 executor. Every prefix cleanup, first-trial
acceptance, stored observation and cached gradient is supplied by the
actual algorithm source theorems. Source: chronological window flushing
and deterministic recursion; no desired rate recurrence is assumed.
-/

namespace krylov.Convergence
noncomputable section
open Matrix krylov.XR Filter Topology
open scoped InnerProductSpace

/-- Uniqueness of a finite-history sliding execution on any actual tail.
This is solely an equality of two deterministic recursions. -/
theorem slidingSequence_shift_eq {E : Type*} {n : ℕ}
    (rule : (Fin (n+2) → E) → E) (x : ℕ → E) (K : ℕ)
    (hstep : ∀ k,K≤k → x (k+n+2)=rule (fun i=>x (k+i.val))) (j : ℕ) :
    x (K+j)=slidingSequence rule (fun i=>x (K+i.val)) j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj : j<n+2
    · rw [slidingSequence,dite_eq_left hj]
    · rw [slidingSequence,dite_eq_right hj]
      have hje : n+2≤j := by omega
      rw [show K+j=(K+(j-(n+2)))+n+2 by omega,hstep _ (by omega)]
      congr 1
      funext i
      have hi : j-(n+2)+i.val<j := by omega
      simpa only [Nat.add_assoc] using ih (j-(n+2)+i.val) hi

/-- Under the original source hypotheses, the full-memory XR update is
literally the actual SS1 map on the last accepted chronological window. -/
theorem source_full_ss1_recursion {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1))) (bounds : SpectralBounds)
    (D : GrowthSource P f G H x₀ center bounds) (hP : P.Valid (n+1))
    (hoff : P.valuesEnabled=false) (hmax : P.maximumCapacity=n+1) :
    ∃ K,∀ k,K≤k →
      (algorithmRun P f G x₀ bounds (k+n+2)).point=
        ss1WindowRule G (fun i : Fin (n+2)=>(algorithmRun P f G x₀ bounds (k+i.val)).point) := by
  let S := algorithmRun P f G x₀ bounds
  let x := fun k=>(S k).point
  obtain ⟨K₁,hK₁⟩ := source_full_observation_chronology P f G H x₀ center bounds D hP hoff hmax
  obtain ⟨K₂,hK₂⟩ := D.eventually_maximum_window hP hoff
  obtain ⟨K₃,hK₃⟩ := D.clean_pair_update hP hoff
  refine ⟨max K₁ (max K₂ K₃),fun k hk=>?_⟩
  let W := (algorithmModel P (S (k+n+1))).pairs
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
    exact (run_cache_constants P (n+1) (algorithmModel P) f G
      (algorithmInitialState P f G x₀ bounds) rfl rfl (k+n+1)).2.1
  have hpoint := (hK₃ (k+n+1) (by omega)).1
  change x (k+n+1+1)=x (k+n+1)+(algorithmModel P (S (k+n+1))).direction at hpoint
  have hraw := algorithm_full_ss1Point P hoff (S (k+n+1)) (by omega) hfull
  rw [hcache,ss1Point_chronological_records f G W x k hrecords] at hraw
  have hraw' : x (k+n+1)+(algorithmModel P (S (k+n+1))).direction=
      ss1Point (windowStep (n:=n+1) x k) (windowImage G x k) (G (x (k+n+1))) (x (k+n+1)) := by
    rw [ss1Point_fin_cast hfull] at hraw
    change x (k+n+1)+(algorithmModel P (S (k+n+1))).direction=
      ss1Point (fun i : Fin (n+1)=>x (k+i.val+1)-x (k+i.val))
        (fun i=>G (x (k+i.val+1))-G (x (k+i.val))) (G (x (k+n+1))) (x (k+n+1))
    simpa only [windowStep,windowImage,Fin.val_cast] using hraw
  rw [show k+n+2=k+n+1+1 by omega]
  exact hpoint.trans hraw'

/-- A concrete XR source with full capacity has an actual tail equal to
the genuine SS1 recursive executor, initialized with its own observed
accepted points. This closes the algorithm-to-method dictionary. -/
theorem source_full_eq_ss1Sequence {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1))) (bounds : SpectralBounds)
    (D : GrowthSource P f G H x₀ center bounds) (hP : P.Valid (n+1))
    (hoff : P.valuesEnabled=false) (hmax : P.maximumCapacity=n+1) :
    ∃ K,∀ j,(algorithmRun P f G x₀ bounds (K+j)).point=
      ss1Sequence G (fun i : Fin (n+2)=>(algorithmRun P f G x₀ bounds (K+i.val)).point) j := by
  obtain ⟨K,hK⟩ := source_full_ss1_recursion P f G H x₀ center bounds D hP hoff hmax
  exact ⟨K,slidingSequence_shift_eq (ss1WindowRule G)
    (fun k=>(algorithmRun P f G x₀ bounds k).point) K hK⟩

end
end krylov.Convergence
