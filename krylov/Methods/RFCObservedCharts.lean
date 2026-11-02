import krylov.Methods.FCObservedRule
import krylov.Methods.WindowCoordinates

set_option autoImplicit false
/-!
Article: main_krylov, def:classes and cor:lm, genuine RFC primitive model charts.
Use: synthesize the true current-plus-retained RFC basis from actual
observations, prove primitive model regularity, and identify every real
repeated-query tree with its genuine fixed-dimensional coefficient form.
Source: actual fixed-shape history reconstruction, true linear observation
synthesis and proved physical model-tree coordinate invariance.
-/

namespace krylov.Methods
noncomputable section
open krylov.Stability
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The genuine earlier complete-history observations inside the actual post-search correction input.
Use: The genuine earlier complete-history observations inside the actual post-search correction input.
Article: main_krylov, def:classes and cor:lm, genuine RFC primitive model charts.
Proof: Remove exactly the true post-search gradient, actual probe and real current direction. -/
def correctionHistoryData (data : Fin (n+3) → E) : Fin n → E := Fin.tail (Fin.tail (Fin.tail data))

/-- The true RFC augmented physical basis in fixed actual observed-data coordinates.
Use: The true RFC augmented physical basis in fixed actual observed-data coordinates.
Article: main_krylov, def:classes and cor:lm, genuine RFC primitive model charts.
Proof: Prepend the genuinely available current direction to the true reconstructed retained steps. -/
def augmentedChartSteps (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin (n+3) → E) :
    Fin (min (memory shape.length) shape.length+1) → E :=
  Fin.cons (data 2) (chartSteps memory shape (correctionHistoryData data))

/-- The true RFC augmented observed images in fixed actual data coordinates.
Use: The true RFC augmented observed images in fixed actual data coordinates.
Article: main_krylov, def:classes and cor:lm, genuine RFC primitive model charts.
Proof: Prepend the genuinely observed probe to the actual reconstructed retained secants. -/
def augmentedChartImages (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin (n+3) → E) :
    Fin (min (memory shape.length) shape.length+1) → E :=
  Fin.cons (data 1) (chartImages memory shape (correctionHistoryData data))

/-- The genuine fixed observation coefficients of the true current-plus-retained RFC basis.
Use: The genuine fixed observation coefficients of the true current-plus-retained RFC basis.
Article: main_krylov, def:classes and cor:lm, genuine RFC primitive model charts.
Proof: Use the actual current-direction coordinate and true retained coefficient-history steps with genuine zero prefix coefficients. -/
def augmentedCoefficientSteps (memory : ℕ → ℕ) (shape : List ℕ) (n : ℕ) :
    Fin (min (memory shape.length) shape.length+1) → Fin (n+3) → ℝ :=
  Fin.cons (Pi.single 2 1) (fun i => Fin.cons 0 (Fin.cons 0 (Fin.cons 0 (coefficientStep memory shape n i))))

/-- The genuine fixed augmented coefficient vectors synthesize exactly to the true physical RFC basis.
Use: The genuine fixed augmented coefficient vectors synthesize exactly to the true physical RFC basis.
Article: main_krylov, def:classes and cor:lm, genuine RFC primitive model charts.
Proof: The head is its real coordinate projection; the actual retained tail is the proved true coefficient-history synthesis. -/
theorem augmentedCoefficientSteps_synthesis (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin (n+3) → E)
    (i : Fin (min (memory shape.length) shape.length+1)) :
    observationSynthesis data (augmentedCoefficientSteps memory shape n i)=augmentedChartSteps memory shape data i := by
  -- Synthesize the genuine current direction first, then the actual retained steps from their true original history observations.
  refine Fin.cases ?_ (fun j => ?_) i
  · exact observationSynthesis_single data 2
  · change combine data (Fin.cons 0 (Fin.cons 0 (Fin.cons 0 (coefficientStep memory shape n j))))=_
    have he : data=Fin.cons (data 0) (Fin.cons (data 1) (Fin.cons (data 2) (correctionHistoryData data))) := by
      funext l
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) l
    rw [he]
    simp only [combine,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,zero_smul,zero_add]
    exact (chartSteps_synthesis memory shape (correctionHistoryData data) j).1.symm

/-- Every true augmented RFC step and actual observed image is C-r in the genuine primitive correction input.
Use: Every true augmented RFC step and actual observed image is C-r in the genuine primitive correction input.
Article: main_krylov, def:classes and cor:lm, genuine RFC primitive model charts.
Proof: Compose actual retained-coordinate regularity with true removal of the three new observations; actual head coordinates are linear projections. -/
theorem augmentedChart_regular (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin (n+3) → E)
    (r : WithTop ℕ∞) (i : Fin (min (memory shape.length) shape.length+1)) :
    ContDiffAt ℝ r (fun p : Fin (n+3) → E => augmentedChartSteps memory shape p i) data ∧
      ContDiffAt ℝ r (fun p : Fin (n+3) → E => augmentedChartImages memory shape p i) data := by
  have htail : ContDiffAt ℝ r (correctionHistoryData : (Fin (n+3) → E) → Fin n → E) data :=
    contDiffAt_pi.mpr fun l => contDiffAt_pi.mp contDiffAt_id l.succ.succ.succ
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨contDiffAt_pi.mp contDiffAt_id 2,contDiffAt_pi.mp contDiffAt_id 1⟩
  · exact chartSteps_regular memory shape correctionHistoryData data htail j

/-- Every entry of the genuine actual RFC augmented latest model is C-r in its true primitive observed input.
Use: Every entry of the genuine actual RFC augmented latest model is C-r in its true primitive observed input.
Article: main_krylov, def:classes and cor:lm, genuine RFC primitive model charts.
Proof: Apply standard real inner-product calculus to the actual newer image and true older step coordinates. -/
theorem augmentedChart_model_regular (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin (n+3) → E)
    (r : WithTop ℕ∞) (i j : Fin (min (memory shape.length) shape.length+1)) :
    ContDiffAt ℝ r (fun p : Fin (n+3) → E =>
      pairModel (augmentedChartSteps memory shape p) (augmentedChartImages memory shape p) i j) data :=
  ((augmentedChart_regular memory shape data r (max i j)).1).inner ℝ
    ((augmentedChart_regular memory shape data r (min i j)).2)

/-- Every real repeated RFC model tree equals the genuine fixed-coordinate augmented observed chart tree, including all possible actual future gradient answers.
Use: Every real repeated RFC model tree equals the genuine fixed-coordinate augmented observed chart tree, including all possible actual future gradient answers.
Article: main_krylov, def:classes and cor:lm, genuine RFC primitive model charts.
Proof: Use the true retained-window length and actual getter coordinates in the proved physical repeated-model tree reindexing identity. -/
theorem augmentedChart_repeatedTree (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin n → E)
    (d z gp : E) (count : ℕ) :
    repeatedModelTree (windowSteps ((d,z)::chartWindow memory shape data))
      (windowModel ((d,z)::chartWindow memory shape data)) count gp=
    repeatedModelTree (augmentedChartSteps memory shape (Fin.cons gp (Fin.cons z (Fin.cons d data))))
      (pairModel (augmentedChartSteps memory shape (Fin.cons gp (Fin.cons z (Fin.cons d data))))
        (augmentedChartImages memory shape (Fin.cons gp (Fin.cons z (Fin.cons d data))))) count gp := by
  -- The genuine augmented list and fixed observed chart differ only by their true finite length index equivalence.
  let W := (d,z)::chartWindow memory shape data
  have hlen : W.length=min (memory shape.length) shape.length+1 := by
    simp only [W,List.length_cons,chartWindow_length]
  apply repeatedModelTree_window_coordinates W hlen
  · rw [windowSteps_getD_array W _ hlen]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  · rw [windowImages_getD_array W _ hlen]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
/-- The actual augmented retained-model determinant equals its genuine fixed observed-chart determinant.
Use: The actual augmented retained-model determinant equals its genuine fixed observed-chart determinant.
Article: main_krylov, def:classes and cor:lm, genuine RFC primitive model charts.
Proof: Both true model axes undergo the same genuine finite length index equivalence, preserving the actual determinant. -/
theorem augmentedChart_model_det (memory : ℕ → ℕ) (shape : List ℕ) (data : Fin n → E)
    (d z gp : E) :
    (windowModel ((d,z)::chartWindow memory shape data)).det=
      (pairModel (augmentedChartSteps memory shape (Fin.cons gp (Fin.cons z (Fin.cons d data))))
        (augmentedChartImages memory shape (Fin.cons gp (Fin.cons z (Fin.cons d data))))).det := by
  let W := (d,z)::chartWindow memory shape data
  have hlen : W.length=min (memory shape.length) shape.length+1 := by
    simp only [W,List.length_cons,chartWindow_length]
  -- The true model matrix is changed only by the actual common finite length index equivalence.
  have hs : windowSteps W=augmentedChartSteps memory shape
      (Fin.cons gp (Fin.cons z (Fin.cons d data))) ∘ finCongr hlen := by
    rw [windowSteps_getD_array W _ hlen]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have hy : windowImages W=augmentedChartImages memory shape
      (Fin.cons gp (Fin.cons z (Fin.cons d data))) ∘ finCongr hlen := by
    rw [windowImages_getD_array W _ hlen]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [windowModel_of_coordinates W hlen _ _ hs hy,Matrix.det_submatrix_equiv_self]

end
end krylov.Methods
