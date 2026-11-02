import jacobi.Analysis.CellGeometry
import jacobi.GelfandLevitan.Profiles

/-!
Article: jacobi, Proposition C.3.
Physical reversal of a finite N-row matrix differs from reflection of
its left cell endpoints by exactly one cell. This elementary identity
keeps the original floor embedding and midpoint conventions unchanged.
Use: matrixPoint_reflection_distance controls the genuine one-cell shift when extending the signed eigenvector limit to the full chain.
-/
namespace jacobi.Analysis
noncomputable section
open Real jacobi.Reference jacobi.GelfandLevitan

/-- The original finite reversal sends i/N to 1-i/N-1/N.
Use: matrixPoint_reflection_distance controls the genuine one-cell
shift when extending the signed eigenvector limit to the full chain.
Article: jacobi, Proposition C.3.
Proof: expand the actual finite reversal and cancel the positive N. -/
theorem matrixMesh_rev (n:ℕ) (i:Fin (n+1)) :
    matrixMesh n i.rev=1-matrixMesh n i-1/((n:ℝ)+1) := by
  have hr : i.rev.val=n-i.val := by simp only [Fin.val_rev]; omega
  simp only [matrixMesh,hr,Nat.cast_sub (Nat.le_of_lt_succ i.isLt)]
  field_simp
  ring

/-- The actual reversed matrix point is one physical cell from the
reflection of its original left endpoint.
Use: target_eigenvector_uniform_limit uses continuity of the actual
full wave to eliminate this exact finite reversal discrepancy.
Article: jacobi, Proposition C.3.
Proof: the exact coordinate difference is -1/N and N is positive. -/
theorem matrixPoint_reflection_distance (n:ℕ) (i:Fin (n+1)) :
    dist (matrixPoint n i.rev) (physicalReflection (matrixPoint n i))=1/((n:ℝ)+1) := by
  change |matrixMesh n i.rev-(1-matrixMesh n i)|=1/((n:ℝ)+1)
  rw [matrixMesh_rev]
  have he : 1-matrixMesh n i-1/((n:ℝ)+1)-(1-matrixMesh n i)= -(1/((n:ℝ)+1)) := by ring
  rw [he,abs_neg,abs_of_nonneg (by positivity)]

end
end jacobi.Analysis
