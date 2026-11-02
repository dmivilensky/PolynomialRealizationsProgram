import jacobi.GelfandLevitan.CellQuadratic
import jacobi.Analysis.PairedQuadratic

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
The two actual GL cell-compressed forms, separated by adjacent-coordinate
pairing, have a uniform strictly positive lower bound. This is the
coercive comparison form for the original uniformly sampled Gram matrix.
Both edge constants are obtained from the previously proved genuine
continuum operators, rather than supplied as certificate assumptions.
Use: pairedCellForm_coercive gives a common positive comparison bound before the source's uniformly vanishing kernel-sampling error is added.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set MeasureTheory jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan
attribute [local instance] Measure.Subtype.measureSpace

/-- The actual paired cell-integrated two-edge quadratic form.
Use: pairedCellForm_coercive gives a common positive comparison bound
before the source's uniformly vanishing kernel-sampling error is added.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
-/
def pairedCellForm (a b:ℝ) (ha:-1<a) (hb:-1<b) (M:ℝ)
    {L:ℕ} (v:Fin L × Fin 2 → ℝ) : ℝ :=
  (M/4)*(quadratic a ha (halfCellVector M (pairPlus v))+
    quadratic b hb (halfCellVector M (pairMinus v)))

/-- The true two-edge cell comparison form has one positive lower
bound for every admissible physical mesh and every paired finite vector.
Use: the original finite Gram coercivity absorbs its uniform kernel
approximation error into this actual fixed positive lower bound.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: obtain both genuine original continuum gaps. Apply them to the
actual half-supported P and Q cell embeddings, reduce to their exact
cell norms and use the proved finite paired-norm identity. -/
theorem pairedCellForm_coercive (a b:ℝ) (ha:-1<a) (hb:-1<b) :
    ∃ κ:ℝ, 0<κ ∧ ∀ M:ℝ, 0<M → ∀ L:ℕ, 4*(L:ℝ)≤M →
      ∀ v:Fin L × Fin 2 → ℝ, κ*(∑ p, (v p)^2)≤pairedCellForm a b ha hb M v := by
  -- Take the smaller of the two genuine continuum gaps before scaling either cell form.
  obtain ⟨ka,hka,hA⟩ := halfCellVector_coercive a ha
  obtain ⟨kb,hkb,hB⟩ := halfCellVector_coercive b hb
  refine ⟨min ka kb,lt_min hka hkb,fun M hM L hL v => ?_⟩
  have hP := (mul_le_mul_of_nonneg_right (min_le_left ka kb)
    (by positivity : 0≤(2/M)*∑ l, (pairPlus v l)^2)).trans (hA M hM L hL (pairPlus v))
  have hQ := (mul_le_mul_of_nonneg_right (min_le_right ka kb)
    (by positivity : 0≤(2/M)*∑ l, (pairMinus v l)^2)).trans (hB M hM L hL (pairMinus v))
  have hh := mul_le_mul_of_nonneg_left (add_le_add hP hQ)
    (show 0≤M/4 by positivity)
  have he : (M/4)*(min ka kb*((2/M)*∑ l, (pairPlus v l)^2)+
      min ka kb*((2/M)*∑ l, (pairMinus v l)^2)) = min ka kb*(∑ p, (v p)^2) := by
    calc
      _ = (min ka kb/2)*((∑ l, (pairPlus v l)^2)+(∑ l, (pairMinus v l)^2)) := by
        field_simp
        ring
      _ = _ := by rw [paired_norm]; ring
  rw [he] at hh
  exact hh

end
end jacobi.Comparison
