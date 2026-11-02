import jacobi.Analysis.FullCells
import jacobi.Comparison.FloorEigenvectorLimit
import jacobi.GelfandLevitan.FullWaveMaps

/-!
Article: jacobi, Theorem 2.1.
The genuine finite eigenvectors are embedded by the original U_N into
the actual physical L2 space. Their representatives are their original
constant cell values, and every cell is within 1/N of its left endpoint.
Use: embeddedTargetEigenvector applies the genuine original step isometry.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- The actual original finite target eigenvector as a vector in its
finite Euclidean physical space, padded only in the spectral index.
Use: embeddedTargetEigenvector applies the genuine original step isometry.
Article: jacobi, Theorem 2.1.
-/
def finiteTargetEigenvector (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) : EuclideanSpace ℝ (Fin (n+1)) :=
  WithLp.toLp 2 (fun i => targetEigenvectorEntry a b ha hb n i k)

/-- The genuine original eigenvector embedded by the actual physical
step isometry, retaining its original signed orientation.
Use: embeddedTargetEigenvector_limit supplies the actual eigenprojector
trace-norm limit used in Theorem 2.1.
Article: jacobi, Theorem 2.1.
-/
def embeddedTargetEigenvector (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) : Space :=
  fullStepIsometry n (finiteTargetEigenvector a b ha hb n k)

/-- The genuine embedded vector has the original exact finite step
sum as its almost-everywhere representative in the actual L2 interval.
Use: its distance to the actual continuous full target wave is bounded
by the proved uniform row error plus the true cell oscillation.
Article: jacobi, Theorem 2.1.
Proof: the actual isometry is the earlier cell embedding, whose
finite indicator representative is already proved. -/
theorem embeddedTargetEigenvector_ae (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) :
    embeddedTargetEigenvector a b ha hb n k=ᵐ[volume]
      (fun t:Interval => ∑i:Fin (n+1),(fullCell n i).indicator
        (fun _ => sqrt ((n:ℝ)+1)*targetEigenvectorEntry a b ha hb n i k) t) := by
  change fullStepLinear n (finiteTargetEigenvector a b ha hb n k)=ᵐ[volume] _
  rw [fullStepLinear_eq]
  exact cellEmbedding_ae _ _ _ _

/-- At an actual point of a genuine cell, the original finite step
representative has exactly that cell's signed eigenvector value.
Use: embeddedTargetEigenvector_limit uses the original physical cells
without changing endpoints or taking representatives of arbitrary L2 vectors.
Article: jacobi, Theorem C.5.
Proof: the original cells are disjoint; all other finite indicators
vanish and the single actual cell contributes its full signed value. -/
theorem embeddedTargetEigenvector_cell (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ)
    (i:Fin (n+1)) {t:Interval} (ht:t∈fullCell n i) :
    (∑j:Fin (n+1),(fullCell n j).indicator
      (fun _ => sqrt ((n:ℝ)+1)*targetEigenvectorEntry a b ha hb n j k) t)=
      sqrt ((n:ℝ)+1)*targetEigenvectorEntry a b ha hb n i k := by
  classical
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem ht _
  · intro j _ hji
    exact indicator_of_notMem (fun hj => (Set.disjoint_left.mp (fullCell_disjoint n hji)) hj ht) _
  · simp

/-- Every interior physical point belongs to the original exact floor
cell, for every genuine positive matrix dimension.
Use: the embedded-vector limit covers almost every original physical
point by the same finite cells as the printed step isometry.
Article: jacobi, Theorem C.5.
Proof: the standard floor inequalities divide by the positive true N. -/
theorem floorMatrixIndex_mem_cell (n:ℕ) (t:ℝ) (ht:t∈Ioo (0:ℝ) 1) :
    (⟨t,⟨ht.1.le,ht.2.le⟩⟩:Interval)∈fullCell n (floorMatrixIndex n t ht) := by
  have hN : (0:ℝ)<(n:ℝ)+1 := by positivity
  change (Nat.floor (((n:ℝ)+1)*t):ℝ)/((n:ℝ)+1)≤t ∧
    t<((Nat.floor (((n:ℝ)+1)*t):ℝ)+1)/((n:ℝ)+1)
  constructor
  · exact (div_le_iff₀ hN).mpr (by
      simpa only [mul_comm t] using Nat.floor_le (mul_nonneg hN.le ht.1.le))
  · exact (lt_div_iff₀ hN).mpr (by
      simpa only [mul_comm t] using Nat.lt_floor_add_one (((n:ℝ)+1)*t))

/-- Every original point of a genuine physical cell is less than one
cell width from its actual left matrix coordinate.
Use: uniform continuity of the same full wave turns the original row
approximation into an actual L2 embedded-vector approximation.
Article: jacobi, Theorem 2.1.
Proof: the point is between its original left endpoint and its right
endpoint exactly one positive cell width later. -/
theorem fullCell_matrix_distance (n:ℕ) (i:Fin (n+1)) {t:Interval} (ht:t∈fullCell n i) :
    dist (matrixPoint n i) t<1/((n:ℝ)+1) := by
  change |(i.val:ℝ)/((n:ℝ)+1)-(t:ℝ)|<1/((n:ℝ)+1)
  rw [abs_of_nonpos (sub_nonpos.mpr ht.1)]
  have hdiff : ((i.val:ℝ)+1)/((n:ℝ)+1)=(i.val:ℝ)/((n:ℝ)+1)+1/((n:ℝ)+1) := by ring
  have hu := ht.2
  rw [hdiff] at hu
  linarith

end
end jacobi.Comparison
