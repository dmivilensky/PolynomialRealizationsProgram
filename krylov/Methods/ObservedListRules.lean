import krylov.Stability.SmoothLists

/-!
Article: main_krylov, def:classes and lem:U(d), actual observed-history coefficient charts.
Use: read primitive coefficient rules on the genuine finite list of past
observations and prove their real decision regularity on locally fixed traces.
Source: actual finite-list coordinates, genuine observed coefficient
evaluation and the proved finite-vector smooth list charts.
-/

namespace krylov.Methods
noncomputable section
open Filter Topology krylov.Stability
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual finite observed vector coordinates, with zero outside the genuine available list.
Use: The actual finite observed vector coordinates, with zero outside the genuine available list.
Article: main_krylov, def:classes and lem:U(d), actual observed-history coefficient charts.
Proof: Each coordinate reads only the true supplied observed list. -/
def observedArray (m : ℕ) (v : List E) : Fin m → E := fun i => v.getD i.val 0

omit [InnerProductSpace ℝ E] in
/-- The genuine observation array reads every actual finite chart coordinate exactly.
Use: The genuine observation array reads every actual finite chart coordinate exactly.
Article: main_krylov, def:classes and lem:U(d), actual observed-history coefficient charts.
Proof: Evaluate the real finite list produced by the vector chart. -/
theorem observedArray_ofFn {m : ℕ} (data : Fin m → E) :
    observedArray m (List.ofFn data)=data := by
  funext i
  simp only [observedArray,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]

/-- A real data-only vector decision with primitive coefficients on the actual available observed list.
Use: A real data-only vector decision with primitive coefficients on the actual available observed list.
Article: main_krylov, def:classes and lem:U(d), actual observed-history coefficient charts.
Proof: Its dimension is the genuine observation count. -/
def listDecision (rules : ∀ m, ObservedRule E m) (v : List E) : E :=
  (rules v.length).evaluate (observedArray v.length v)

/-- The actual list decision agrees with its true finite-vector coefficient evaluation.
Use: The actual list decision agrees with its true finite-vector coefficient evaluation.
Article: main_krylov, def:classes and lem:U(d), actual observed-history coefficient charts.
Proof: The actual list length and all genuine observation coordinates equal their finite chart values. -/
theorem listDecision_ofFn (rules : ∀ m, ObservedRule E m) {m : ℕ} (data : Fin m → E) :
    listDecision rules (List.ofFn data)=(rules m).evaluate data := by
  unfold listDecision
  rw [List.length_ofFn,observedArray_ofFn]

/-- Primitive observed coefficient regularity implies actual decision regularity on the true smooth finite history chart.
Use: Primitive observed coefficient regularity implies actual decision regularity on the true smooth finite history chart.
Article: main_krylov, def:classes and lem:U(d), actual observed-history coefficient charts.
Proof: The real chart fixes the actual local data dimension. Compose the primitive coefficient function with those genuine observations and use their proved exact local execution equality. -/
theorem listDecision_contDiffAt (rules : ∀ m, ObservedRule E m) (v : X → List E) (x : X)
    {r : WithTop ℕ∞} (hv : SmoothListAt r v x)
    (hrule : ContDiffAt ℝ r (rules (v x).length).coefficient (observedArray (v x).length (v x))) :
    ContDiffAt ℝ r (fun p => listDecision rules (v p)) x := by
  -- The actual finite history chart fixes the real coefficient dimension on one neighborhood.
  obtain ⟨m,data,hd,he⟩ := hv
  have hdata : ContDiffAt ℝ r (rules m).coefficient (data x) := by
    rw [he.self_of_nhds] at hrule
    rw [List.length_ofFn,observedArray_ofFn] at hrule
    exact hrule
  apply ((rules m).evaluate_contDiffAt data x hdata hd).congr_of_eventuallyEq
  filter_upwards [he] with p hp
  rw [hp,listDecision_ofFn]

/-- The actual current gradient, initial observation and all true past query records as one finite available data list.
Use: The actual current gradient, initial observation and all true past query records as one finite available data list.
Article: main_krylov, def:classes and lem:U(d), actual observed-history coefficient charts.
Proof: Every direction, probe, recorded displacement, returned gradient and intermediate correction observation is retained. -/
def History.observationList (H : History E) : List E :=
  H.gradient::H.initial::H.records.flatMap (fun r =>
    [r.direction,r.probe,r.step,r.gradient]++r.corrections.flatMap (fun p => [p.1,p.2]))

omit [InnerProductSpace ℝ E] in
/-- The actual observation list begins with the true current gradient.
Use: The actual observation list begins with the true current gradient.
Article: main_krylov, def:classes and lem:U(d), actual observed-history coefficient charts.
Proof: Read its genuine first list coordinate. -/
theorem History.observationList_gradient (H : History E) : H.observationList.getD 0 0=H.gradient := rfl

omit [InnerProductSpace ℝ E] in
/-- The actual initial gradient remains the second true observation coordinate.
Use: The actual initial gradient remains the second true observation coordinate.
Article: main_krylov, def:classes and lem:U(d), actual observed-history coefficient charts.
Proof: Read its genuine retained initial list coordinate. -/
theorem History.observationList_initial (H : History E) : H.observationList.getD 1 0=H.initial := rfl
end
end krylov.Methods
