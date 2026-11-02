import jacobi.Analysis.HalfCells
import jacobi.Analysis.HalfMatrixCompactness

/-!
Article: jacobi, Theorem 2.1.
The actual paired cells use N+4, while the original matrix coordinates
use N. Every point of a physical cell remains uniformly O(1/N) from
either of its two matrix coordinates. This controls kernel sampling
without omitting the physical midpoint or the optional padded index.
Use: cell_matrix_distance compares actual cell points with the source GL kernel sampling points in a single compact metric domain.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set jacobi.Reference

/-- The true physical matrix coordinate as a point of the shared unit
interval, with its original matrix-size normalization.
Use: cell_matrix_distance compares actual cell points with the source
GL kernel sampling points in a single compact metric domain.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
-/
def matrixPoint (n : ℕ) (i : Fin (n+1)) : Interval :=
  ⟨matrixMesh n i,by
    constructor
    · unfold matrixMesh
      positivity
    · apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
      have hi : (i.val:ℝ)<(n:ℝ)+1 := by exact_mod_cast i.isLt
      linarith⟩

/-- Every point of the actual adjacent-pair cell is uniformly close to
the original physical coordinate of either matrix index in that pair.
Use: cell-kernel averages converge uniformly to the same original GL
kernel values used by gramPerturbation_uniform.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: division by two leaves an integer remainder at most one. The
cell width and its change of denominator each contribute O(1/N);
the original physical half-index bound controls the latter uniformly. -/
theorem cell_matrix_distance {n:ℕ} (i:Fin (n+1)) (hi:2*i.val≤n+1)
    {t:Interval} (ht:t∈halfCell ((n:ℝ)+5) (i.val/2)) :
    dist t (matrixPoint n i)≤6/((n:ℝ)+1) := by
  -- Retain both integer remainder bounds to control the change from N to N+4.
  have hN : (0:ℝ)<(n:ℝ)+1 := by positivity
  have hM : (0:ℝ)<(n:ℝ)+5 := by positivity
  have hrem : 2*(i.val/2) ≤ i.val ∧ i.val ≤ 2*(i.val/2)+1 := by omega
  have hl : 2*((i.val/2:ℕ):ℝ)≤(i.val:ℝ) := by exact_mod_cast hrem.1
  have hu : (i.val:ℝ)≤2*((i.val/2:ℕ):ℝ)+1 := by exact_mod_cast hrem.2
  have hh : 2*(i.val:ℝ)≤(n:ℝ)+1 := by exact_mod_cast hi
  have htlo : 2*((i.val/2:ℕ):ℝ)<(t:ℝ)*((n:ℝ)+5) := (div_lt_iff₀ hM).mp ht.1
  have hthi : (t:ℝ)*((n:ℝ)+5)≤2*((i.val/2:ℕ):ℝ)+2 := (le_div_iff₀ hM).mp ht.2
  have htHalf : (t:ℝ)≤1 := t.property.2
  change |(t:ℝ)-(i.val:ℝ)/((n:ℝ)+1)|≤6/((n:ℝ)+1)
  have he : (t:ℝ)-(i.val:ℝ)/((n:ℝ)+1)=
      ((t:ℝ)*((n:ℝ)+1)-(i.val:ℝ))/((n:ℝ)+1) := by field_simp
  rw [he]
  apply abs_le.mpr
  constructor
  · rw [← neg_div]
    apply (div_le_div_iff_of_pos_right hN).mpr
    nlinarith
  · apply (div_le_div_iff_of_pos_right hN).mpr
    nlinarith [t.property.1]

end
end jacobi.Analysis
