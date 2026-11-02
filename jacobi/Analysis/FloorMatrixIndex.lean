import jacobi.Analysis.CellGeometry
import chebyshev1.Analysis.MeshApproximation

/-!
Article: jacobi, Theorem 2.1.
The original floor row is a genuine finite matrix index for every
interior physical point. Its actual matrix-size mesh tends to that point.
Source: the floor-mesh theorem already proved in chebyshev1.
Use: Theorem 2.1 and Theorem 2.1 use this original row, rather than an auxiliary clipped or asymptotically equivalent index.
-/
namespace jacobi.Analysis
noncomputable section
open Set Filter
open scoped Topology

/-- The actual physical floor row in the genuine N=n+1 matrix.
Use: Theorem 2.1 and Theorem 2.1 use this original row, rather
than an auxiliary clipped or asymptotically equivalent index.
Article: jacobi, Theorem 2.1.
-/
def floorMatrixIndex (n:ℕ) (t:ℝ) (ht:t∈Ioo (0:ℝ) 1) : Fin (n+1) :=
  ⟨Nat.floor (((n:ℝ)+1)*t),by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (chebyshev1.Analysis.floor_unit_bounds (n+1) (Nat.succ_pos n) ht).1⟩

/-- The original physical floor row tends to its actual interior
coordinate in the true matrix-size mesh.
Use: floor-row eigenvector and resolvent limits specialize the proved
moving-row theorems without changing the article's index convention.
Article: jacobi, Theorem 2.1.
Proof: reuse the first article's exact floor-mesh convergence along
the genuine cofinal dimensions N=n+1. -/
theorem floorMatrixMesh_tendsto (t:ℝ) (ht:t∈Ioo (0:ℝ) 1) :
    Tendsto (fun n:ℕ => matrixMesh n (floorMatrixIndex n t ht)) atTop (𝓝 t) := by
  have hh := chebyshev1.Analysis.floor_mesh_limit (tendsto_add_atTop_nat 1)
    (tendsto_const_nhds (x:=t)) (Eventually.of_forall (fun _ => ht.1.le))
  simpa only [floorMatrixIndex,matrixMesh,Nat.cast_add,Nat.cast_one] using hh

end
end jacobi.Analysis
