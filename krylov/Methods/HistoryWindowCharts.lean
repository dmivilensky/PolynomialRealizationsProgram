import krylov.Methods.ObservationSynthesis
import krylov.Methods.HistoryObservationRegularity
import krylov.Methods.DirectionReindex

set_option autoImplicit false
/-!
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Use: synthesize actual retained steps, observed secants and current
gradients from true fixed coefficient histories; derive their primitive
C-r data regularity and exact genuine finite coefficient-solve coordinates.
Source: actual structured-history reconstruction, true stored-pair map
identities and genuine finite-list coordinate reindexing.
-/

namespace krylov.Methods
noncomputable section
open Filter Topology krylov.Stability
variable {E F X : Type*} {n : ℕ}

/-- Genuine structured observed-history reconstruction has exactly its true supplied iteration count.
Use: Genuine structured observed-history reconstruction has exactly its true supplied iteration count.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Take actual lengths in the proved true query-shape identity. -/
theorem historyFromObservations_records_length [Zero E] (shape : List ℕ) (v : List E) :
    (historyFromObservations shape v).records.length=shape.length := by
  have h := congrArg List.length (historyFromObservations_shape shape v)
  simpa only [History.queryShape,List.length_map] using h

/-- Mapping real observed data preserves the genuine complete-history iteration count.
Use: Mapping real observed data preserves the genuine complete-history iteration count.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Actual record mapping preserves its true finite list length. -/
theorem History.map_records_length (f : E → F) (H : History E) : (H.map f).records.length=H.records.length :=
  List.length_map _

section Linear
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A genuine linear observation map preserves the true selected stored-pair window.
Use: A genuine linear observation map preserves the true selected stored-pair window.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Map the actual secant differences and use the genuine unchanged record count and real finite take identity. -/
theorem selectedWindow_map (memory : ℕ → ℕ) (f : E →ₗ[ℝ] F) (H : History E) :
    selectedWindow memory (H.map f)=(selectedWindow memory H).map (fun p => (f p.1,f p.2)) := by
  unfold selectedWindow
  rw [History.pairs_map,History.map_records_length,← List.map_take]
end Linear

section Charts
variable [NormedAddCommGroup E]

/-- The true retained stored-pair window reconstructed from genuine finite observed data with a fixed actual query shape.
Use: The true retained stored-pair window reconstructed from genuine finite observed data with a fixed actual query shape.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Apply the real retention implementation to the actual reconstructed history. -/
def chartWindow (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin n → E) : List (E × E) :=
  selectedWindow memory (historyFromObservations shape (List.ofFn data))

/-- True fixed-dimensional retained physical step coordinates read from the actual reconstructed window.
Use: True fixed-dimensional retained physical step coordinates read from the actual reconstructed window.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Read genuine pair coordinates at their actual retained finite indices. -/
def chartSteps (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin n → E)
    (i : Fin (min (memory shape.length) shape.length)) : E :=
  ((chartWindow memory shape data).getD i.val (0,0)).1

/-- True fixed-dimensional retained observed secant coordinates read from the actual reconstructed window.
Use: True fixed-dimensional retained observed secant coordinates read from the actual reconstructed window.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Read the actual gradient-difference component of each genuine retained pair. -/
def chartImages (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin n → E)
    (i : Fin (min (memory shape.length) shape.length)) : E :=
  ((chartWindow memory shape data).getD i.val (0,0)).2

/-- The actual current gradient of the genuinely reconstructed complete observed history.
Use: The actual current gradient of the genuinely reconstructed complete observed history.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Read the true current-gradient field from the real finite reconstruction. -/
def chartGradient (shape : List ℕ) (data : Fin n → E) : E :=
  (historyFromObservations shape (List.ofFn data)).gradient

/-- The actual fixed-shape reconstructed retained window has its true prescribed finite length for every genuine input array.
Use: The actual fixed-shape reconstructed retained window has its true prescribed finite length for every genuine input array.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Real pair extraction preserves the actual record count and true finite retention takes its genuine minimum. -/
theorem chartWindow_length (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin n → E) :
    (chartWindow memory shape data).length=min (memory shape.length) shape.length := by
  simp only [chartWindow,selectedWindow,List.length_take,History.pairs_length,historyFromObservations_records_length]
end Charts

section Regular
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- True smooth observation arrays give a genuine C-r retained-pair list chart and actual current-gradient regularity.
Use: True smooth observation arrays give a genuine C-r retained-pair list chart and actual current-gradient regularity.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Use genuine complete-history pair reconstruction regularity and restrict its true finite chart by the actual fixed retained count. -/
theorem chartWindow_regular (memory : ℕ → ℕ) (shape : List ℕ) (data : X → Fin n → E)
    (x : X) {r : WithTop ℕ∞} (hd : ContDiffAt ℝ r data x) :
    SmoothListAt r (fun p => chartWindow memory shape (data p)) x ∧
      ContDiffAt ℝ r (fun p => chartGradient shape (data p)) x := by
  -- The genuine input observations have a true finite chart before reconstructing or retaining any actual pair.
  have hv : SmoothListAt r (fun p => List.ofFn (data p)) x := ⟨n,data,hd,Eventually.of_forall fun _ => rfl⟩
  have hp := historyFromObservations_pairs_regular shape (fun p => List.ofFn (data p)) x hv
  refine ⟨?_,hp.2⟩
  convert! hp.1.take (memory shape.length) using 1
  funext p
  simp only [chartWindow,selectedWindow,historyFromObservations_records_length]

/-- Every actual retained reconstructed step and true observed secant coordinate is C-r in the genuine smooth input observations.
Use: Every actual retained reconstructed step and true observed secant coordinate is C-r in the genuine smooth input observations.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Read the real two coordinates through the actual finite retained-pair chart. -/
theorem chartSteps_regular (memory : ℕ → ℕ) (shape : List ℕ) (data : X → Fin n → E)
    (x : X) {r : WithTop ℕ∞} (hd : ContDiffAt ℝ r data x)
    (i : Fin (min (memory shape.length) shape.length)) :
    ContDiffAt ℝ r (fun p => chartSteps memory shape (data p) i) x ∧
      ContDiffAt ℝ r (fun p => chartImages memory shape (data p) i) x := by
  have hg := (chartWindow_regular memory shape data x hd).1.getD i.val
  exact ⟨hg.fst,hg.snd⟩

/-- The genuine actual reconstructed retained window is the true linear synthesis image of its fixed real coefficient-history window.
Use: The genuine actual reconstructed retained window is the true linear synthesis image of its fixed real coefficient-history window.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Use actual complete-history synthesis and genuine linear stored-window mapping. -/
theorem chartWindow_synthesis (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin n → E) :
    chartWindow memory shape data=(selectedWindow memory (coefficientHistory shape n)).map
      (fun p => (observationSynthesis data p.1,observationSynthesis data p.2)) := by
  unfold chartWindow
  rw [← coefficientHistory_synthesis shape data,selectedWindow_map]

/-- The genuine actual reconstructed current gradient is the true synthesis image of its fixed real coefficient-history gradient.
Use: The genuine actual reconstructed current gradient is the true synthesis image of its fixed real coefficient-history gradient.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Apply actual current-gradient map compatibility to the true complete-history synthesis identity. -/
theorem chartGradient_synthesis (shape : List ℕ) (data : Fin n → E) :
    chartGradient shape data=observationSynthesis data (coefficientHistory shape n).gradient := by
  unfold chartGradient
  rw [← coefficientHistory_synthesis shape data,History.gradient_map]

/-- Every actual reconstructed retained step and observed secant is the true synthesis image of its fixed genuine coefficient-history pair coordinates.
Use: Every actual reconstructed retained step and observed secant is the true synthesis image of its fixed genuine coefficient-history pair coordinates.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Map the actual finite window and use true zero-preserving coordinate mapping, including genuine absent defaults. -/
theorem chartSteps_synthesis (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin n → E)
    (i : Fin (min (memory shape.length) shape.length)) :
    chartSteps memory shape data i=observationSynthesis data
      (((selectedWindow memory (coefficientHistory shape n)).getD i.val (0,0)).1) ∧
    chartImages memory shape data i=observationSynthesis data
      (((selectedWindow memory (coefficientHistory shape n)).getD i.val (0,0)).2) := by
  -- Zero-preserving real synthesis also maps genuine absent pair defaults correctly.
  have hz : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (observationSynthesis data p.1,observationSynthesis data p.2)) 0=0 := by
    exact Prod.ext (map_zero _) (map_zero _)
  have he := getD_map_zero (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
    (observationSynthesis data p.1,observationSynthesis data p.2)) hz (selectedWindow memory (coefficientHistory shape n)) i.val
  simp only [chartSteps,chartImages,chartWindow_synthesis]
  exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
end Regular

section Direction
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- The actual physical list-window steps equal their genuine fixed getter-array coordinates under the true length index equivalence.
Use: The actual physical list-window steps equal their genuine fixed getter-array coordinates under the true length index equivalence.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Read the real valid list coordinate through its actual zero-default getter. -/
theorem windowSteps_getD_array (W : List (E × E)) (p : ℕ) (hp : W.length=p) :
    windowSteps W=(fun i : Fin p => (W.getD i.val (0,0)).1) ∘ finCongr hp := by
  funext i
  change (W.get i).1=(W.getD i.val (0,0)).1
  rw [List.getD_eq_get W (0,0) i]

omit [InnerProductSpace ℝ E] in
/-- The actual observed list-window images equal their genuine fixed getter-array coordinates under the true length index equivalence.
Use: The actual observed list-window images equal their genuine fixed getter-array coordinates under the true length index equivalence.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Read the real stored secant coordinate through its actual valid finite getter. -/
theorem windowImages_getD_array (W : List (E × E)) (p : ℕ) (hp : W.length=p) :
    windowImages W=(fun i : Fin p => (W.getD i.val (0,0)).2) ∘ finCongr hp := by
  funext i
  change (W.get i).2=(W.getD i.val (0,0)).2
  rw [List.getD_eq_get W (0,0) i]

/-- The genuine actual list-window direction solve equals its true fixed-dimensional getter-array conjugacy solve, including singular totalized cases.
Use: The genuine actual list-window direction solve equals its true fixed-dimensional getter-array conjugacy solve, including singular totalized cases.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Identify the real finite step/image coordinates by the true list-length index equivalence, then use the proved actual solve reindexing identity. -/
theorem windowDirection_getD_array (W : List (E × E)) (p : ℕ) (hp : W.length=p) (g : E) :
    windowDirection W g=conjugacyDirection
      (fun i : Fin p => (W.getD i.val (0,0)).1) (fun i : Fin p => (W.getD i.val (0,0)).2) g := by
  change conjugacyDirection (windowSteps W) (windowImages W) g=_
  rw [windowSteps_getD_array W p hp,windowImages_getD_array W p hp,conjugacyDirection_reindex]

/-- The genuine list-window conjugacy determinant equals its true fixed getter-array determinant.
Use: The genuine list-window conjugacy determinant equals its true fixed getter-array determinant.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: The actual step and image arrays reindex together, so their genuine cross-Gram matrix changes by a true simultaneous finite index equivalence preserving its real determinant. -/
theorem crossGram_getD_array_det (W : List (E × E)) (p : ℕ) (hp : W.length=p) :
    (crossGram (windowImages W) (windowSteps W)).det=
      (crossGram (fun i : Fin p => (W.getD i.val (0,0)).2) (fun i : Fin p => (W.getD i.val (0,0)).1)).det := by
  -- Both real cross-Gram axes use the same genuine list-length index equivalence, preserving the actual determinant.
  have he : crossGram (windowImages W) (windowSteps W)=
      (crossGram (fun i : Fin p => (W.getD i.val (0,0)).2)
        (fun i : Fin p => (W.getD i.val (0,0)).1)).submatrix (finCongr hp) (finCongr hp) := by
    rw [windowSteps_getD_array W p hp,windowImages_getD_array W p hp]
    rfl
  rw [he,Matrix.det_submatrix_equiv_self]

/-- The true reconstructed retained-window direction has exactly the genuine fixed finite step/image chart solve.
Use: The true reconstructed retained-window direction has exactly the genuine fixed finite step/image chart solve.
Article: main_krylov, def:classes and cor:lm, genuine fixed-shape observed window charts.
Proof: Use its proved actual window length in the true finite getter-array solve identity. -/
theorem chartWindow_direction (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin n → E) :
    windowDirection (chartWindow memory shape data) (chartGradient shape data)=
      conjugacyDirection (chartSteps memory shape data) (chartImages memory shape data) (chartGradient shape data) :=
  windowDirection_getD_array _ _ (chartWindow_length memory shape data) _
end Direction
end
end krylov.Methods
