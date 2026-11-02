import jacobi.GelfandLevitan.CellQuadratic
import jacobi.Analysis.CellGeometry

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
The true Lebesgue cell averages of either actual continuum GL kernel
converge uniformly to its original matrix-coordinate samples. The cells
use N+4; all samples use the true matrix size N, including the midpoint.
Use: averagedKernel_uniform compares the genuine coercive cell forms with the same samples appearing in the proved uniform Gram limit.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace

/-- The actual average of a continuous kernel over the two paired
physical cells associated with the original row and column.
Use: averagedKernel_uniform compares the genuine coercive cell forms
with the same samples appearing in the proved uniform Gram limit.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
-/
def averagedKernel (G:C(Interval×Interval,ℝ)) (n:ℕ) (i j:Fin (n+1)) : ℝ :=
  cellKernelEntry G (halfCell ((n:ℝ)+5) (i.val/2))
    (halfCell ((n:ℝ)+5) (j.val/2)) / (2/((n:ℝ)+5))^2

/-- Every paired cell used by an actual matrix coordinate has exactly
the width in the denominator of averagedKernel.
Use: averagedKernel_uniform divides the original integral error by the
actual rectangle measure, with no unproved quadrature normalization.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the true finite index bounds put the cell below the unit endpoint;
the previously proved original Lebesgue cell-measure identity applies. -/
theorem matrixCell_volume {n:ℕ} (i:Fin (n+1)) :
    volume.real (halfCell ((n:ℝ)+5) (i.val/2))=2/((n:ℝ)+5) := by
  apply halfCell_volume (by positivity)
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+5)).mpr
  have hlo : 2*(i.val/2) ≤ i.val := by omega
  have hl : 2*((i.val/2:ℕ):ℝ)≤(i.val:ℝ) := by exact_mod_cast hlo
  have hi : (i.val:ℝ)<(n:ℝ)+1 := by exact_mod_cast i.isLt
  linarith

/-- The actual cell-averaged kernel converges uniformly to the original
kernel sampled at the true physical matrix coordinates.
Use: the source uniform finite Gram coercivity compares its two actual
continuum cell forms with the already proved two-edge Gram approximation.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: a continuous kernel is uniformly continuous on the original compact
unit square. Every point of the actual cell rectangle is within 6/N of
its actual matrix sample. Integrate the resulting uniform error and
divide by the proved true rectangle measure. -/
theorem averagedKernel_uniform (G:C(Interval×Interval,ℝ)) :
    ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, ∀ i j:Fin (n+1),
      2*i.val≤n+1 → 2*j.val≤n+1 →
      |averagedKernel G n i j-G (matrixPoint n i,matrixPoint n j)|≤ε := by
  -- The uniform modulus controls every point in each actual cell rectangle.
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous G.continuous) ε hε
  have hlim : Tendsto (fun n:ℕ => 6/((n:ℝ)+1)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hδ))
  refine ⟨N,fun n hn i j hi hj => ?_⟩
  let h : ℝ := 2/((n:ℝ)+5)
  have hh : 0<h := by dsimp [h]; positivity
  have hbound : ∀ p∈halfCell ((n:ℝ)+5) (i.val/2) ×ˢ
      halfCell ((n:ℝ)+5) (j.val/2),
      |G p-G (matrixPoint n i,matrixPoint n j)|≤ε := by
    intro p hp
    have hd : dist p (matrixPoint n i,matrixPoint n j)<δ := by
      rw [Prod.dist_eq]
      exact max_lt ((cell_matrix_distance i hi hp.1).trans_lt (hN n hn))
        ((cell_matrix_distance j hj hp.2).trans_lt (hN n hn))
    simpa only [Real.dist_eq] using (hclose hd).le
  have hb := cellKernelEntry_error G hbound
  rw [matrixCell_volume i,matrixCell_volume j] at hb
  change |averagedKernel G n i j-G (matrixPoint n i,matrixPoint n j)|≤ε
  unfold averagedKernel
  change |cellKernelEntry G _ _/h^2-G (matrixPoint n i,matrixPoint n j)|≤ε
  have he : cellKernelEntry G (halfCell ((n:ℝ)+5) (i.val/2))
      (halfCell ((n:ℝ)+5) (j.val/2))/h^2-G (matrixPoint n i,matrixPoint n j)=
      (cellKernelEntry G (halfCell ((n:ℝ)+5) (i.val/2))
      (halfCell ((n:ℝ)+5) (j.val/2))-h^2*G (matrixPoint n i,matrixPoint n j))/h^2 := by
    field_simp
  rw [he,abs_div,abs_of_pos (sq_pos_of_pos hh)]
  apply (div_le_iff₀ (sq_pos_of_pos hh)).mpr
  simpa only [pow_two,mul_comm ε] using hb

end
end jacobi.Comparison
