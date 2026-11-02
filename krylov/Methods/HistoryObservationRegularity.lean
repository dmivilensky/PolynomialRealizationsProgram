import krylov.Methods.HistoryReconstruction
import krylov.Stability.SmoothLists

set_option autoImplicit false
/-!
Article: main_krylov, def:classes and cor:lm, actual primitive structured-history regularity.
Use: derive real C-r reconstructed gradient and stored-pair coordinates
from true finite observation data with their actual discrete query shape,
for genuine primitive coefficient charts of the named implementations.
Source: exact genuine observed-history reconstruction, actual finite-list
smooth charts and standard real product and subtraction calculus.
-/

namespace krylov.Stability
noncomputable section
open Filter Topology
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Taking a genuine fixed finite observed prefix preserves its actual C-r finite-coordinate chart.
Use: Taking a genuine fixed finite observed prefix preserves its actual C-r finite-coordinate chart.
Article: main_krylov, def:classes and cor:lm, actual primitive structured-history regularity.
Proof: Restrict the true finite chart to the genuine retained index interval and use exact actual list coordinates. -/
theorem SmoothListAt.take {r : WithTop ℕ∞} {v : X → List E} {x : X}
    (hv : SmoothListAt r v x) (k : ℕ) : SmoothListAt r (fun p => (v p).take k) x := by
  -- Restrict the true finite observation chart to exactly the actual retained prefix indices.
  obtain ⟨n,data,hd,he⟩ := hv
  let f := fun p (i : Fin (min k n)) => data p ⟨i.val,lt_of_lt_of_le i.isLt (min_le_right k n)⟩
  refine ⟨min k n,f,contDiffAt_pi.mpr (fun i => (contDiffAt_pi.mp hd) _),?_⟩
  filter_upwards [he] with p hp
  rw [hp]
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn]
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_ofFn,f]
end
end krylov.Stability

namespace krylov.Methods
noncomputable section
open krylov.Stability
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Genuine fixed-shape observed-record reconstruction has a true C-r current gradient and real finite C-r stored-pair chart.
Use: Genuine fixed-shape observed-record reconstruction has a true C-r current gradient and real finite C-r stored-pair chart.
Article: main_krylov, def:classes and cor:lm, actual primitive structured-history regularity.
Proof: Induct through the actual query shape. Read true step and gradient fields from the genuine input chart; each real secant is the actual current record gradient minus the genuine preceding reconstructed gradient. -/
theorem readHistoryPairs_regular (shape : List ℕ) (initial : X → E) (v : X → List E)
    (x : X) {r : WithTop ℕ∞} (hg : ContDiffAt ℝ r initial x) (hv : SmoothListAt r v x) :
    SmoothListAt r (fun p => (History.mk (initial p) (readHistoryRecords shape (v p))).pairs) x ∧
      ContDiffAt ℝ r (fun p => (History.mk (initial p) (readHistoryRecords shape (v p))).gradient) x := by
  -- Every genuine secant coordinate subtracts the true preceding reconstructed gradient, preserving the actual finite record boundaries.
  induction shape generalizing v with
  | nil => exact ⟨SmoothListAt.nil r x,hg⟩
  | cons q qs ih =>
    obtain ⟨hp,hgTail⟩ := ih (fun p => (v p).drop (4+2*q)) (hv.drop (4+2*q))
    have hgHead := hv.getD 3
    have hsHead := hv.getD 2
    refine ⟨?_,hgHead⟩
    convert! SmoothListAt.cons (hsHead.prodMk (hgHead.sub hgTail)) hp using 1

/-- The true reconstructed complete history has genuine C-r stored-pair observations and actual current gradient on every real finite observed-data chart.
Use: The true reconstructed complete history has genuine C-r stored-pair observations and actual current gradient on every real finite observed-data chart.
Article: main_krylov, def:classes and cor:lm, actual primitive structured-history regularity.
Proof: Read the actual initial-gradient coordinate and drop the true two-vector prefix before applying genuine fixed-shape record regularity. -/
theorem historyFromObservations_pairs_regular (shape : List ℕ) (v : X → List E)
    (x : X) {r : WithTop ℕ∞} (hv : SmoothListAt r v x) :
    SmoothListAt r (fun p => (historyFromObservations shape (v p)).pairs) x ∧
      ContDiffAt ℝ r (fun p => (historyFromObservations shape (v p)).gradient) x :=
  readHistoryPairs_regular shape (fun p => (v p).getD 1 0) (fun p => (v p).drop 2) x (hv.getD 1) (hv.drop 2)
end
end krylov.Methods
