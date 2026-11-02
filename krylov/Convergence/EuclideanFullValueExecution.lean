import krylov.Convergence.SS1FEuclideanPhysicalRate
import krylov.XR.EuclideanDictionary

/-!
Article: main_krylov, cor:xrF, actual Euclidean chronological window.
Use: identify the real accepted endpoint records and the literal computed
full model query with the Euclidean SS1-F window rule. The gate and full
phase are derived independently by the original-source activation proof.
Source: actual cached anchors/steps and genuine observed value models.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.XR krylov.Functions
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- After a chronological flush, the actual cached anchors, secants and
splits give precisely the original observable SS1-F map. -/
theorem euclidean_ss1FPoint_chronological_records (f : E → ℝ) (G : E → E)
    (W : List (PairObservation E)) (x : ℕ → E) (k : ℕ) (z : E)
    (h : staticObservations W=List.ofFn (fun i : Fin W.length=>
      observePair f G (x (k+i.val)) (x (k+i.val+1)-x (k+i.val))))
    (_hfaith : ∀ a∈W,PairFaithful f G z a)
    (hsteps : ∀ i,storedSteps W i≠0) :
    ss1FPoint f G (storedAnchors W) (storedSteps W) (euclideanStoredSplit z W) z=
      ss1FPoint f G (windowAnchor (n:=W.length) x k) (windowStep x k)
        (fun i=>innerSplit (windowAnchor x k i) (windowStep x k i) z) z := by
  have ha : storedAnchors W=windowAnchor x k := by
    funext i
    exact congrArg PairObservation.anchor (staticObservations_get W _ h i)
  have hs : storedSteps W=windowStep x k := by
    funext i
    exact congrArg PairObservation.step (staticObservations_get W _ h i)
  have hl : euclideanStoredSplit z W=(fun i=>innerSplit
      (windowAnchor x k i) (windowStep x k i) z) := by
    funext i
    rw [euclideanStoredSplit_eq_innerSplit z W i (hsteps i),ha,hs]
  rw [ha,hs,hl]

/-- The actual full XR-F candidate, on an actual chronological accepted
window, is literally the genuine SS1-F window rule with the observable
split policy. All gates refer to its real cached data. -/
theorem euclidean_algorithm_full_chronological_ss1FWindowRule {n : ℕ} (P : Parameters)
    (hon : P.valuesEnabled=true)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (S : State (EuclideanSpace ℝ (Fin (n+1))))
    (x : ℕ → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ)
    (hx : S.point=x (k+n+1))
    (hfull : (euclideanAlgorithmModel P S).pairs.length=n+1)
    (hg : S.gradient=G S.point)
    (hfaith : ∀ a∈(euclideanAlgorithmModel P S).pairs,PairFaithful f G S.point a)
    (hsteps : ∀ i,storedSteps (euclideanAlgorithmModel P S).pairs i≠0)
    (hgate : ∀ i,|12*euclideanStoredSplit S.point (euclideanAlgorithmModel P S).pairs i*
      ((euclideanAlgorithmModel P S).pairs.get i).valueDefect|≤storedPairing (euclideanAlgorithmModel P S).pairs i i/2)
    (hpass : euclideanCorrectedWindowPasses P.windowThreshold S.point (euclideanAlgorithmModel P S).pairs)
    (hrecords : staticObservations (euclideanAlgorithmModel P S).pairs=List.ofFn
      (fun i : Fin (euclideanAlgorithmModel P S).pairs.length=>
        observePair f G (x (k+i.val)) (x (k+i.val+1)-x (k+i.val)))) :
    S.point+(euclideanAlgorithmModel P S).direction=
      ss1FWindowRule f G ss1FEuclideanSplit (fun i : Fin (n+2)=>x (k+i.val)) := by
  let W := (euclideanAlgorithmModel P S).pairs
  have hp := euclideanAlgorithm_full_ss1FPoint P hon f G S (by omega) hfull hg hfaith hgate hpass
  rw [euclidean_ss1FPoint_chronological_records f G W x k S.point hrecords hfaith hsteps,hx] at hp
  rw [ss1FPoint_fin_cast hfull] at hp
  change S.point+(euclideanAlgorithmModel P S).direction=
    ss1FPoint f G (fun i : Fin (n+1)=>x (k+i.val))
      (fun i=>x (k+i.val+1)-x (k+i.val))
      (fun i=>innerSplit (x (k+i.val)) (x (k+i.val+1)-x (k+i.val)) (x (k+n+1))) (x (k+n+1))
  rw [hx]
  simpa only [windowAnchor,windowStep,windowImage,Fin.val_cast] using hp

end
end krylov.Convergence
