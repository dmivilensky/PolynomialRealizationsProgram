import jacobi.Analysis.FullCellQuadrature
import jacobi.Comparison.EmbeddedEigenvectors

/-!
Article: jacobi, Theorem C.5.
Actual finite physical arrays with a uniform compact-family continuous
profile limit have their uniform genuine integral limit. The exact
original full-cell step integral is reused for arbitrary Banach values.
Source: uniform continuity on compact sets and the Bochner integral norm bound.
Use: Theorem C.5 applies this to the actual complex squares and the actual squared norms of the original finite shifted diagonal.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace

/-- A genuine full physical finite array converging uniformly to a
compact continuous profile has its exact normalized sum converging
uniformly to the original physical integral over every parameter.
Use: Theorem C.5 applies this to the actual complex squares and the
actual squared norms of the original finite shifted diagonal.
Article: jacobi, Theorem C.5.
Proof: the original finite full-cell function integrates to exactly
its normalized finite sum. On almost every physical point its actual
cell value differs from the same continuous profile by the proved
uniform row error and a uniformly small original cell oscillation.
The genuine Bochner integral norm is bounded by this uniform error
times the fixed finite physical measure. -/
theorem compact_full_mesh_integral {P E:Type*} [MetricSpace P] [CompactSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (G:C(Interval×P,E)) (a:∀n:ℕ,Fin (n+1)→P→E)
    (ha:∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀i:Fin (n+1),∀p:P,
      ‖a n i p-G (matrixPoint n i,p)‖<ε) :
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀p:P,
      ‖(1/((n:ℝ)+1)) • (∑i:Fin (n+1),a n i p)-(∫t:Interval,G (t,p))‖<ε := by
  -- No continuity of the actual finite arrays is required inside their original cells.
  let M := (volume:Measure Interval).real univ
  have hM : 0≤M := measureReal_nonneg
  intro ε hε
  let η := ε/(4*(M+1))
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨NR,hNR⟩ := ha η hη
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous G.continuous) η hη
  have hone : Tendsto (fun n:ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_mono
      (fun n:ℕ => le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1)) tendsto_natCast_atTop_atTop)
  obtain ⟨NC,hNC⟩ := eventually_atTop.mp (hone.eventually (Iio_mem_nhds hδ))
  refine ⟨max NR NC,fun n hn p => ?_⟩
  have hG : Integrable (fun t:Interval => G (t,p)) :=
    (G.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hae : ∀ᵐt:Interval ∂volume,‖fullCellStep n (fun i => a n i p) t-G (t,p)‖≤2*η := by
    filter_upwards [interval_interior_ae] with t ht
    let i := floorMatrixIndex n t.val ht
    have hc : t∈fullCell n i := jacobi.Comparison.floorMatrixIndex_mem_cell n t.val ht
    rw [fullCellStep_cell n _ i hc]
    have hd : dist (matrixPoint n i,p) (t,p)<δ := by
      rw [Prod.dist_eq,dist_self,max_eq_left dist_nonneg]
      exact (jacobi.Comparison.fullCell_matrix_distance n i hc).trans (hNC n (by omega))
    have hosc := hclose hd
    rw [dist_eq_norm] at hosc
    exact (norm_sub_le_norm_sub_add_norm_sub _ (G (matrixPoint n i,p)) _).trans
      (by linarith [hNR n (by omega) i p])
  have hi := norm_integral_le_of_norm_le_const hae
  rw [integral_sub (fullCellStep_integrable n _) hG,fullCellStep_integral] at hi
  have hηeq : η*(4*(M+1))=ε := div_mul_cancel₀ _ (by positivity)
  exact hi.trans_lt (by nlinarith)

end
end jacobi.Analysis
