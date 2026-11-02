import jacobi.Analysis.FullCells
import jacobi.Analysis.FloorMatrixIndex
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Article: jacobi, Theorem C.5.
Exact integration of the original full physical step cells and their
uniform compact-family quadrature. The genuine N=n+1 cell partition
and its Lebesgue widths are reused from the actual step isometry.
Source: Bochner integration of finite measurable step functions.
Use: compact_full_mesh_integral turns genuine spectral finite sums into exact physical integrals for both shifted energies in Theorem C.5.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual finite full-cell step function with arbitrary Banach values.
Use: compact_full_mesh_integral turns genuine spectral finite sums
into exact physical integrals for both shifted energies in Theorem C.5.
Article: jacobi, Theorem C.5.
-/
def fullCellStep (n:ℕ) (v:Fin (n+1)→E) (t:Interval) : E :=
  ∑i:Fin (n+1),(fullCell n i).indicator (fun _ => v i) t

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Every original finite full-cell step function is Bochner integrable.
Use: exact fullCellStep_integral and subtraction of the genuine
continuous compact profile have their actual integrability proved.
Article: jacobi, Theorem C.5.
Proof: each measurable physical cell has finite measure; its constant
indicator is integrable and their original sum is finite. -/
theorem fullCellStep_integrable (n:ℕ) (v:Fin (n+1)→E) : Integrable (fullCellStep n v) :=
  integrable_finsetSum _ (fun i _ => (integrable_const (v i)).indicator (fullCell_measurable n i))

/-- Integrating the original genuine full-cell step function gives
exactly its normalized finite sum in the actual physical measure.
Use: the uniform shifted energy convergence retains the exact source
N-cubed normalization rather than an approximate Riemann-sum identity.
Article: jacobi, Theorem C.5.
Proof: integrate the finite sum of original cell indicators. Every
actual cell has exactly its proved true Lebesgue width 1/N. -/
theorem fullCellStep_integral (n:ℕ) (v:Fin (n+1)→E) :
    (∫t:Interval,fullCellStep n v t)=(1/((n:ℝ)+1)) • ∑i:Fin (n+1),v i := by
  simp only [fullCellStep]
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_const (v i)).indicator (fullCell_measurable n i)),Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator_const _ (fullCell_measurable n i),fullCell_volume]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- On an actual original cell the full step function takes precisely
that cell's original value, also for general Banach-valued data.
Use: compact_full_mesh_integral compares actual cell values with the
same continuous physical profile at the genuine point of integration.
Article: jacobi, Theorem C.5.
Proof: all other original cell indicators vanish by proved disjointness. -/
theorem fullCellStep_cell (n:ℕ) (v:Fin (n+1)→E) (i:Fin (n+1)) {t:Interval}
    (ht:t∈fullCell n i) : fullCellStep n v t=v i := by
  classical
  rw [fullCellStep,Finset.sum_eq_single i]
  · exact indicator_of_mem ht _
  · intro j _ hji
    exact indicator_of_notMem (fun hj => Set.disjoint_left.mp (fullCell_disjoint n hji) hj ht) _
  · simp

end
end jacobi.Analysis
