import krylov.Methods.FCObservedRule
import krylov.Methods.SmoothClasses

set_option autoImplicit false
/-!
Article: main_krylov, def:classes and cor:lm, actual fixed-shape policy charts.
Use: reconstruct arbitrary genuine observed histories, transfer actual
FC coefficient domains, and establish real local policy agreement directly
on primitive observed-data neighborhoods with true query boundaries.
Source: actual finite complete-history reconstruction and genuine local
observed-policy topology; no cycle regularity is assumed.
-/

namespace krylov.Methods
noncomputable section
open krylov.Stability Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

omit [InnerProductSpace ℝ E] in
/-- Reconstructing a genuine complete-history observation array with its true query shape recovers exactly the actual history.
Use: Reconstructing a genuine complete-history observation array with its true query shape recovers exactly the actual history.
Article: main_krylov, def:classes and cor:lm, actual fixed-shape policy charts.
Proof: Use the actual supplied observation list in the proved true reconstruction identity. -/
theorem historyFromObservations_of_array (H : History E) (data : Fin n → E)
    (hdata : H.observationList=List.ofFn data) :
    historyFromObservations H.queryShape (List.ofFn data)=H := by
  rw [← hdata,historyFromObservations_actual]

omit [InnerProductSpace ℝ E] in
/-- A true reconstructed observed-array retained window equals the actual history window.
Use: A true reconstructed observed-array retained window equals the actual history window.
Article: main_krylov, def:classes and cor:lm, actual fixed-shape policy charts.
Proof: Recover the genuine complete history before selecting its real retained pairs. -/
theorem chartWindow_of_array (memory : ℕ → ℕ) (H : History E) (data : Fin n → E)
    (hdata : H.observationList=List.ofFn data) :
    chartWindow memory H.queryShape data=selectedWindow memory H := by
  unfold chartWindow
  rw [historyFromObservations_of_array H data hdata]

/-- The primitive FC coefficient rule evaluates to the genuine implemented FC direction on every true fixed-shape observed history.
Use: The primitive FC coefficient rule evaluates to the genuine implemented FC direction on every true fixed-shape observed history.
Article: main_krylov, def:classes and cor:lm, actual fixed-shape policy charts.
Proof: Recover the real current gradient and retained window by true complete-history reconstruction. -/
theorem fcObservedRule_of_array (memory : ℕ → ℕ) (H : History E) (data : Fin n → E)
    (hdata : H.observationList=List.ofFn data) :
    (fcObservedRule memory H.queryShape n).evaluate data=(fcMethod memory).direction H := by
  rw [fcObservedRule_evaluate]
  change windowDirection (chartWindow memory H.queryShape data)
    (historyFromObservations H.queryShape (List.ofFn data)).gradient=_
  rw [chartWindow_of_array memory H data hdata,historyFromObservations_of_array H data hdata]
  rfl

/-- Primitive FC coefficients are C-r at any genuine observed presentation of an actual nonsingular retained model.
Use: Primitive FC coefficients are C-r at any genuine observed presentation of an actual nonsingular retained model.
Article: main_krylov, def:classes and cor:lm, actual fixed-shape policy charts.
Proof: Transfer the actual retained determinant through its true fixed getter-array coordinates and apply proved genuine primitive coefficient regularity. -/
theorem fcObservedRule_actual_regular (memory : ℕ → ℕ) (H : History E) (data : Fin n → E)
    (hdata : H.observationList=List.ofFn data) (r : WithTop ℕ∞)
    (hC : (crossGram (windowImages (selectedWindow memory H)) (windowSteps (selectedWindow memory H))).det≠0) :
    ContDiffAt ℝ r (fcObservedRule memory H.queryShape n : ObservedRule E n).coefficient data := by
  -- Transfer the actual inverse domain on the real retained window to the genuine fixed-dimensional primitive coefficient chart.
  apply fcObservedRule_coefficient_regular memory H.queryShape data _ r
  let W := selectedWindow memory H
  have hW := chartWindow_of_array memory H data hdata
  have hlen : W.length=min (memory H.queryShape.length) H.queryShape.length := by
    change (selectedWindow memory H).length=_
    rw [← hW,chartWindow_length]
  change (crossGram (fun i : Fin (min (memory H.queryShape.length) H.queryShape.length) => ((chartWindow memory H.queryShape data).getD i.val (0,0)).2)
    (fun i : Fin (min (memory H.queryShape.length) H.queryShape.length) => ((chartWindow memory H.queryShape data).getD i.val (0,0)).1)).det≠0
  rw [hW,← crossGram_getD_array_det W _ hlen]
  exact hC

omit [InnerProductSpace ℝ E] in
/-- A primitive observed-array neighborhood property yields the genuine local policy property on the actual structured complete histories.
Use: A primitive observed-array neighborhood property yields the genuine local policy property on the actual structured complete histories.
Article: main_krylov, def:classes and cor:lm, actual fixed-shape policy charts.
Proof: Reconstruct every actual history with the true fixed query boundaries and the given genuine observed list, then transfer the real neighborhood property. -/
theorem ObservedLocalAt.of_chart (H₀ : History E) (z₀ : E) (predicate : History E → E → Prop)
    (h : ∀ (n : ℕ) (data : Fin n → E), H₀.observationList=List.ofFn data →
      ∀ᶠ q : (Fin n → E) × E in 𝓝 (data,z₀),
        predicate (historyFromObservations H₀.queryShape (List.ofFn q.1)) q.2) :
    ObservedLocalAt H₀ z₀ predicate := by
  -- Every true history on the given observed-data neighborhood has the same genuine query boundaries and is reconstructed exactly.
  intro n data hdata
  refine ⟨{q | predicate (historyFromObservations H₀.queryShape (List.ofFn q.1)) q.2},h n data hdata,?_⟩
  intro q hq H hshape hobs
  have he : historyFromObservations H₀.queryShape (List.ofFn q.1)=H := by
    rw [← hshape,historyFromObservations_of_array H q.1 hobs]
  change predicate (historyFromObservations H₀.queryShape (List.ofFn q.1)) q.2 at hq
  rwa [he] at hq
/-- Primitive local agreement along the genuine raw reference run identifies the real complete histories of the raw and compiled executors.
Use: Primitive local agreement along the genuine raw reference run identifies the real complete histories of the raw and compiled executors.
Article: main_krylov, def:classes and cor:lm, actual fixed-shape policy charts.
Proof: Induct through actual reference decisions; true local equality identifies the real direction and entire correction tree before every genuine next record. -/
theorem localCompiled_reference_run_of_raw (m : ProbedMethod E) (P : CompiledProbedPolicy E)
    (A B : ℕ → E →L[ℝ] E) (g : E) (N : ℕ)
    (hlocal : ∀ k<N, LocalCompiledAt m P (methodRun m A B g k)
      (A k (P.method.direction (methodRun m A B g k)))) :
    methodRun m A B g N=methodRun P.method A B g N := by
  -- Compare actual raw reference decisions before constructing the genuine next compiled record.
  induction N with
  | zero => rfl
  | succ k ih =>
    have he := ih (fun j hj => hlocal j (hj.trans (Nat.lt_succ_self k)))
    have hp := (hlocal k (Nat.lt_succ_self k)).self
    rw [methodRun,methodRun,← he]
    dsimp only [methodAdvance]
    rw [hp.1,hp.2]

end
end krylov.Methods
