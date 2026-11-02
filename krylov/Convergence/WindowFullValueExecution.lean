import krylov.Convergence.WindowFullExecution
import krylov.XR.CorrectedDictionary

/-!
Article: main_krylov, cor:xrF, chronological value-model dictionary.
Use: identify the literal cached covector split with a policy computed from
accepted points and gradients, and identify the actual full XR-F query with
the genuine SS1-F executor. Source: faithful cached observations and the
proved literal corrected-model dictionary; the source gate activation is
proved separately by the actual XR local analysis.
-/

namespace krylov.Convergence
noncomputable section
open Matrix krylov.XR krylov.Functions
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- SS1-F's original model-metric split as a literal observable window
policy: only the two endpoint gradients and actual current point enter. -/
def ss1FObservedSplit {n : ℕ} (G : E → E) (q : Fin (n+2) → E) (i : Fin (n+1)) : ℝ :=
  covectorSplit (innerSL ℝ (G (q i.succ)-G (q i.castSucc)))
    (q i.castSucc) (q i.succ-q i.castSucc) (q (Fin.last (n+1)))

/-- An equality of index lengths is solely a relabeling of the true
observed value model, and leaves its actual physical query unchanged. -/
theorem ss1FPoint_fin_cast {m n : ℕ} (h : m=n) (f : E → ℝ) (G : E → E)
    (a s : Fin m → E) (l : Fin m → ℝ) (x : E) :
    ss1FPoint f G a s l x=ss1FPoint f G (fun i : Fin n=>a (Fin.cast h.symm i))
      (fun i=>s (Fin.cast h.symm i)) (fun i=>l (Fin.cast h.symm i)) x := by
  subst n
  rfl

/-- After a chronological flush, the actual cached anchors, secants and
splits give precisely the original observable SS1-F map. -/
theorem ss1FPoint_chronological_records (f : E → ℝ) (G : E → E)
    (W : List (PairObservation E)) (x : ℕ → E) (k : ℕ) (z : E)
    (h : staticObservations W=List.ofFn (fun i : Fin W.length=>
      observePair f G (x (k+i.val)) (x (k+i.val+1)-x (k+i.val))))
    (hfaith : ∀ a∈W,PairFaithful f G z a)
    (hden : ∀ i,storedPairing W i i≠0) :
    ss1FPoint f G (storedAnchors W) (storedSteps W) (storedSplit W) z=
      ss1FPoint f G (windowAnchor (n:=W.length) x k) (windowStep x k)
        (fun i=>covectorSplit (innerSL ℝ (windowImage G x k i))
          (windowAnchor x k i) (windowStep x k i) z) z := by
  have ha : storedAnchors W=windowAnchor x k := by
    funext i
    exact congrArg PairObservation.anchor (staticObservations_get W _ h i)
  have hs : storedSteps W=windowStep x k := by
    funext i
    exact congrArg PairObservation.step (staticObservations_get W _ h i)
  have hy : storedImages W=windowImage G x k := by
    funext i
    have hh := congrArg PairObservation.image (staticObservations_get W _ h i)
    simpa only [staticObservation,observePair,storedImages,windowImage,add_sub_cancel] using hh
  have hl : storedSplit W=(fun i=>covectorSplit (innerSL ℝ (windowImage G x k i))
      (windowAnchor x k i) (windowStep x k i) z) := by
    funext i
    rw [storedSplit_eq_covectorSplit f G z W hfaith i (hden i),ha,hs,hy]
  rw [ha,hs,hl]

/-- The actual full XR-F candidate, on an actual chronological accepted
window, is literally the genuine SS1-F window rule with the observable
split policy. All gates refer to its real cached data. -/
theorem algorithm_full_chronological_ss1FWindowRule {n : ℕ} (P : Parameters)
    (hon : P.valuesEnabled=true)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (S : State (EuclideanSpace ℝ (Fin (n+1))))
    (x : ℕ → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ)
    (hx : S.point=x (k+n+1))
    (hfull : (algorithmModel P S).pairs.length=n+1)
    (hg : S.gradient=G S.point)
    (hfaith : ∀ a∈(algorithmModel P S).pairs,PairFaithful f G S.point a)
    (hden : ∀ i,storedPairing (algorithmModel P S).pairs i i≠0)
    (hgate : ∀ i,|12*storedSplit (algorithmModel P S).pairs i*
      ((algorithmModel P S).pairs.get i).valueDefect|≤storedPairing (algorithmModel P S).pairs i i/2)
    (hpass : correctedWindowPasses P.windowThreshold (algorithmModel P S).pairs)
    (hrecords : staticObservations (algorithmModel P S).pairs=List.ofFn
      (fun i : Fin (algorithmModel P S).pairs.length=>
        observePair f G (x (k+i.val)) (x (k+i.val+1)-x (k+i.val)))) :
    S.point+(algorithmModel P S).direction=
      ss1FWindowRule f G (ss1FObservedSplit G) (fun i : Fin (n+2)=>x (k+i.val)) := by
  let W := (algorithmModel P S).pairs
  have hp := algorithm_full_ss1FPoint P hon f G S (by omega) hfull hg hfaith hgate hpass
  rw [ss1FPoint_chronological_records f G W x k S.point hrecords hfaith hden,hx] at hp
  rw [ss1FPoint_fin_cast hfull] at hp
  change S.point+(algorithmModel P S).direction=
    ss1FPoint f G (fun i : Fin (n+1)=>x (k+i.val))
      (fun i=>x (k+i.val+1)-x (k+i.val))
      (fun i=>covectorSplit (innerSL ℝ (G (x (k+i.val+1))-G (x (k+i.val))))
        (x (k+i.val)) (x (k+i.val+1)-x (k+i.val)) (x (k+n+1))) (x (k+n+1))
  rw [hx]
  simpa only [windowAnchor,windowStep,windowImage,Fin.val_cast] using hp

end
end krylov.Convergence
