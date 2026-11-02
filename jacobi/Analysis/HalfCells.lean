import jacobi.Analysis.CellEmbedding
import jacobi.GelfandLevitan.Coercivity

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
The paired coordinates use actual disjoint physical cells of width 2/M.
Their Lebesgue measure, half-interval support and L2 norms are proved
with the existing reference-space measure, including null endpoints.
Use: halfCellVector constructs the true P and Q in the source positivity argument, using M=N+4 rather than changing the integration measure.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace

/-- The actual paired-coordinate cell in the original physical interval.
Use: halfCellVector constructs the true P and Q in the source positivity
argument, using M=N+4 rather than changing the integration measure.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
-/
def halfCell (M : ℝ) (l : ℕ) : Set Interval :=
  {t | 2*(l:ℝ)/M < (t:ℝ) ∧ (t:ℝ) ≤ (2*(l:ℝ)+2)/M}

/-- Physical paired-coordinate cells are measurable.
Use: the finite step embedding is a genuine original L2 vector.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: both coordinate inequalities are measurable. -/
theorem halfCell_measurable (M : ℝ) (l : ℕ) : MeasurableSet (halfCell M l) :=
  (measurableSet_lt measurable_const measurable_subtype_coe).inter
    (measurableSet_le measurable_subtype_coe measurable_const)

/-- Every cell has exactly its original Lebesgue width.
Use: halfCellVector_norm_sq fixes the normalization of the finite-to-L2
coercivity transfer, without an assumed quadrature factor.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Source: Lebesgue interval measure and mathlib's subtype measure.
Proof: the actual coordinate image is the real half-open interval;
the subtype pullback preserves its Lebesgue measure. -/
theorem halfCell_volume {M : ℝ} (hM : 0<M) (l : ℕ)
    (hu : (2*(l:ℝ)+2)/M ≤ 1) :
    (volume : Measure Interval).real (halfCell M l)=2/M := by
  -- Compute the real coordinate image before invoking the subtype measure formula.
  have hm : MeasurableEmbedding (Subtype.val : Interval → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have he : Subtype.val '' halfCell M l = Ioc (2*(l:ℝ)/M) ((2*(l:ℝ)+2)/M) := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ht
    · intro hx
      exact ⟨⟨x,⟨(by positivity : (0:ℝ)≤2*(l:ℝ)/M).trans hx.1.le,
        hx.2.trans hu⟩⟩,hx,rfl⟩
  unfold Measure.real
  rw [Measure.Subtype.volume_def,hm.comap_apply,he,Real.volume_Ioc]
  have hwidth : (2*(l:ℝ)+2)/M-2*(l:ℝ)/M=2/M := by ring
  rw [hwidth,ENNReal.toReal_ofReal (by positivity)]

/-- Distinct paired-coordinate cells are disjoint, including adjacent
cells sharing a null boundary coordinate.
Use: the exact L2 norm contains only the diagonal cell measures.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: ordering the cell indices separates the strict lower endpoint
of the later cell from the weak upper endpoint of the earlier cell. -/
theorem halfCell_disjoint {M : ℝ} (hM : 0<M) :
    Pairwise (fun i j : ℕ => Disjoint (halfCell M i) (halfCell M j)) := by
  -- The strict lower endpoint of the later cell excludes its earlier neighbor.
  intro i j hij
  apply Set.disjoint_left.mpr
  intro t hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hn : (i:ℝ)+1≤(j:ℝ) := by exact_mod_cast hlt
    have hd : (2*(i:ℝ)+2)/M≤2*(j:ℝ)/M :=
      (div_le_div_iff_of_pos_right hM).mpr (by linarith)
    exact (not_lt_of_ge (hi.2.trans hd)) hj.1
  · have hn : (j:ℝ)+1≤(i:ℝ) := by exact_mod_cast hgt
    have hd : (2*(j:ℝ)+2)/M≤2*(i:ℝ)/M :=
      (div_le_div_iff_of_pos_right hM).mpr (by linarith)
    exact (not_lt_of_ge (hj.2.trans hd)) hi.1

/-- The actual L2 embedding of one finite paired-coordinate family.
Use: halfCellVector_coercive applies the proved genuine GL coercivity
to the finite P and Q coefficient families in the source Gram proof.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
-/
def halfCellVector (M : ℝ) {L : ℕ} (v : Fin L → ℝ) : Space :=
  cellEmbedding (fun l => halfCell M l.val) (fun l => halfCell_measurable M l.val)
    (fun _ => measure_ne_top _ _) v

/-- Every cell in the chosen paired family lies inside the physical half.
Use: halfCellVector_supported discharges the actual support hypothesis
of the established continuum GL quadratic lower bound.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the last cell's upper endpoint is at most 2L/M<=1/2. -/
theorem halfCell_mem_half {M : ℝ} (hM : 0<M) {L : ℕ} (hL : 4*(L:ℝ)≤M)
    (l : Fin L) {t : Interval} (ht : t∈halfCell M l.val) : (t:ℝ)≤1/2 := by
  have hl : (l.val:ℝ)+1≤(L:ℝ) := by exact_mod_cast l.isLt
  have hu : (2*(l.val:ℝ)+2)/M≤1/2 := (div_le_iff₀ hM).mpr (by linarith)
  exact ht.2.trans hu

/-- The actual paired step embedding has the precise source norm.
Use: the two continuum coercivity inequalities become lower bounds
for the original finite Euclidean squared norm after pairing.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the genuine cells are disjoint and all have the proved common
Lebesgue width 2/M, so the general exact L2 cell identity applies. -/
theorem halfCellVector_norm_sq {M : ℝ} (hM : 0<M) {L : ℕ}
    (hL : 4*(L:ℝ)≤M) (v : Fin L → ℝ) :
    ‖halfCellVector M v‖^2=(2/M)*∑ l, (v l)^2 := by
  apply cellEmbedding_norm_sq
  · intro i j hij
    exact halfCell_disjoint hM (fun he => hij (Fin.ext he))
  · intro l
    apply halfCell_volume hM
    have hl : (l.val:ℝ)+1≤(L:ℝ) := by exact_mod_cast l.isLt
    apply (div_le_iff₀ hM).mpr
    linarith

/-- The genuine finite paired step function is half-supported.
Use: the source continuum coercivity constant is applied without an
additional support premise or a replacement Hilbert space.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: every actual cell lies in the half interval, and the finite
indicator embedding vanishes outside their union. -/
theorem halfCellVector_supported {M : ℝ} (hM : 0<M) {L : ℕ}
    (hL : 4*(L:ℝ)≤M) (v : Fin L → ℝ) :
    HalfSupported (halfCellVector M v) := by
  have hh := cellEmbedding_supported (fun l : Fin L => halfCell M l.val)
    (fun l => halfCell_measurable M l.val)
    (fun l => measure_ne_top (volume : Measure Interval) (halfCell M l.val))
    {t : Interval | (t:ℝ)≤1/2} (fun l _ ht => halfCell_mem_half hM hL l ht) v
  filter_upwards [hh] with t ht
  intro hhalf
  exact ht (not_le.mpr hhalf)

/-- One true continuum GL coercivity constant controls every actual
paired cell family, simultaneously over all mesh sizes and vectors.
Use: the finite Gram lower bound compares its sampled kernel with
these genuinely coercive cell forms for the two source orders.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: half support and the exact L2 norm have been proved for the
actual cells. Substitute both into the established source GL coercivity. -/
theorem halfCellVector_coercive (a : ℝ) (ha : -1<a) :
    ∃ κ:ℝ, 0<κ ∧ ∀ (M:ℝ), 0<M → ∀ (L:ℕ), 4*(L:ℝ)≤M →
      ∀ v:Fin L→ℝ, κ*((2/M)*∑ l, (v l)^2) ≤
        jacobi.GelfandLevitan.quadratic a ha (halfCellVector M v) := by
  obtain ⟨κ,hκ,hbound⟩ := jacobi.GelfandLevitan.quadratic_coercive a ha
  refine ⟨κ,hκ,fun M hM L hL v => ?_⟩
  simpa only [halfCellVector_norm_sq hM hL] using
    hbound (halfCellVector M v) (halfCellVector_supported hM hL v)

end
end jacobi.Analysis
