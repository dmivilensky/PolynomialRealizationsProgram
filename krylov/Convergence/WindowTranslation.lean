import krylov.Convergence.WindowMetricExecution

/-!
Article: main_krylov, thm:grow and cor:xrF, genuine centered executors.
Use: center the literal observed SS1 and SS1-F recursions at their actual
limit. Source: translation of differences and the proved affine invariance
of actual endpoint values and trapezoid defects.
-/
namespace krylov.Convergence
noncomputable section
open krylov.Methods krylov.Functions
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- Translation of the actual observed SS1 rule. -/
theorem ss1WindowRule_translate (G : E → E) (c : E) (q : Fin (n+2) → E) :
    ss1WindowRule G q-c=ss1WindowRule (fun z=>G (c+z)) (fun i=>q i-c) := by
  simp only [ss1WindowRule,ss1Point,show ∀ i j,(q i-c)-(q j-c)=q i-q j from fun _ _=>by abel_nf,
    show ∀ z : E,c+(z-c)=z from fun _=>by abel_nf]
  abel_nf

/-- Actual observed model-metric splits are translation invariant. -/
theorem ss1FObservedSplit_translate (G : E → E) (c : E) (q : Fin (n+2) → E) :
    ss1FObservedSplit (fun z=>G (c+z)) (fun i=>q i-c)=ss1FObservedSplit G q := by
  funext i
  simp only [ss1FObservedSplit,covectorSplit,show ∀ z : E,c+(z-c)=z from fun _=>by abel_nf,
    show (q i.succ-c)-(q i.castSucc-c)=q i.succ-q i.castSucc by abel_nf]
  congr 2
  abel_nf

/-- The complete actual value model is invariant under centering. -/
theorem valueCorrectedModel_translate {p : ℕ} (f : E → ℝ) (G : E → E)
    (c : E) (a s : Fin p → E) (l : Fin p → ℝ) :
    valueCorrectedModel (fun z=>f (c+z)) (fun z=>innerSL ℝ (G (c+z)))
      (fun i=>a i-c) s l=valueCorrectedModel f (fun z=>innerSL ℝ (G z)) a s l := by
  have hh := valueCorrectedModel_affine f (fun z=>innerSL ℝ (G z))
    (ContinuousLinearMap.id ℝ E) c (fun i=>a i-c) s l
  simpa only [ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_id,show ∀ z : E,c+(z-c)=z from fun _=>by abel_nf] using hh

/-- Translation of the genuine observable SS1-F rule. -/
theorem ss1FWindowRule_translate (f : E → ℝ) (G : E → E) (c : E) (q : Fin (n+2) → E) :
    ss1FWindowRule f G (ss1FObservedSplit G) q-c=
      ss1FWindowRule (fun z=>f (c+z)) (fun z=>G (c+z))
        (ss1FObservedSplit (fun z=>G (c+z))) (fun i=>q i-c) := by
  simp only [ss1FWindowRule,ss1FObservedSplit_translate,ss1FPoint,
    show ∀ i j,(q i-c)-(q j-c)=q i-q j from fun _ _=>by abel_nf,
    valueCorrectedModel_translate,show ∀ z : E,c+(z-c)=z from fun _=>by abel_nf]
  abel_nf

/-- The entire actual SS1 sequence may be centered without modifying any
observed physical step or gradient difference. -/
theorem ss1Sequence_translate (G : E → E) (c : E) (seed : Fin (n+2) → E) (j : ℕ) :
    ss1Sequence G seed j-c=ss1Sequence (fun z=>G (c+z)) (fun i=>seed i-c) j := by
  let x := fun k=>ss1Sequence G seed k-c
  have hstep (k : ℕ) : x (k+n+2)=ss1WindowRule (n:=n) (fun z=>G (c+z)) (fun i=>x (k+i.val)) := by
    change slidingSequence (ss1WindowRule G) seed (k+n+2)-c=_
    rw [slidingSequence_step]
    exact ss1WindowRule_translate G c _
  have hh := slidingSequence_shift_eq (ss1WindowRule (fun z=>G (c+z))) x 0 (fun k _=>hstep k) j
  have hseed : (fun i : Fin (n+2)=>x (0+i.val))=(fun i=>seed i-c) := by
    funext i
    dsimp only [x]
    rw [Nat.zero_add,ss1Sequence,slidingSequence_seed]
  rw [Nat.zero_add,hseed] at hh
  exact hh

/-- The genuine data-only SS1-F executor has the same exact centering
identity, including its real observable split policy. -/
theorem ss1FObservedSequence_translate (f : E → ℝ) (G : E → E) (c : E)
    (seed : Fin (n+2) → E) (j : ℕ) :
    ss1FSequence f G (ss1FObservedSplit G) seed j-c=
      ss1FSequence (fun z=>f (c+z)) (fun z=>G (c+z))
        (ss1FObservedSplit (fun z=>G (c+z))) (fun i=>seed i-c) j := by
  let x := fun k=>ss1FSequence f G (ss1FObservedSplit G) seed k-c
  have hstep (k : ℕ) : x (k+n+2)=
      ss1FWindowRule (n:=n) (fun z=>f (c+z)) (fun z=>G (c+z))
        (ss1FObservedSplit (fun z=>G (c+z))) (fun i=>x (k+i.val)) := by
    change slidingSequence (ss1FWindowRule f G (ss1FObservedSplit G)) seed (k+n+2)-c=_
    rw [slidingSequence_step]
    exact ss1FWindowRule_translate f G c _
  have hh := slidingSequence_shift_eq
    (ss1FWindowRule (fun z=>f (c+z)) (fun z=>G (c+z)) (ss1FObservedSplit (fun z=>G (c+z))))
    x 0 (fun k _=>hstep k) j
  have hseed : (fun i : Fin (n+2)=>x (0+i.val))=(fun i=>seed i-c) := by
    funext i
    dsimp only [x]
    rw [Nat.zero_add,ss1FSequence,slidingSequence_seed]
  rw [Nat.zero_add,hseed] at hh
  exact hh

end
end krylov.Convergence
