import polyak.ModeLocking.Continuation.ShiftDerivative

/-! The left kernel is the literal sum of the positive weights in each
nonzero tight residue class. Lags in the zero class remain separate. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

def classWeight (r : Fin D.d) : ℝ :=
  ∑ n ∈ D.lags, if n % (L : ℤ) = D.reps r then D.dual n else 0

theorem classWeight_pos (r : Fin D.d) : 0 < D.classWeight r := by
  classical
  obtain ⟨n, hn, _, _, _, hr, _⟩ := D.class_pair r
  unfold classWeight
  refine Finset.sum_pos' ?_ ⟨n, hn, ?_⟩
  · intro m hm
    split_ifs
    · exact (D.dual_pos m hm).le
    · exact le_rfl
  · rw [ite_eq_left hr]
    exact D.dual_pos n hn

theorem class_sum_symbol_at (t : ℝ) (ω : Frequency) (hω : ω ∈ periodicGrid L) :
    (∑ r, D.classWeight r * (Geometry.shiftedCurve q t).lag (D.reps r) ω) =
      finiteSymbol q t D.lags D.dual ω := by
  classical
  unfold classWeight
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm, finiteSymbol_actual]
  apply Finset.sum_congr rfl
  intro n hn
  rcases D.classes n hn with hz | ⟨r₀, hr⟩
  · have hh (r : Fin D.d) : n % (L : ℤ) ≠ D.reps r := by
      rw [hz]
      exact (D.reps_pos r).ne
    simp only [ite_eq_right (hh _), Finset.sum_const_zero]
    rw [lag_mod_grid (Geometry.shiftedCurve q t) hω n, hz, Curve.lag_zero, mul_zero]
  · have hh (r : Fin D.d) : n % (L : ℤ) = D.reps r ↔ r = r₀ := by
      rw [hr]
      exact ⟨fun h => (D.reps_injective h).symm, fun h => by rw [h]⟩
    simp_rw [hh]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ r₀),
      lag_mod_grid (Geometry.shiftedCurve q t) hω n, hr]

theorem class_sum_symbol (ω : Frequency) (hω : ω ∈ periodicGrid L) :
    (∑ r, D.classWeight r * (Geometry.shiftedCurve q s).lag (D.reps r) ω) =
      finiteSymbol q s D.lags D.dual ω := D.class_sum_symbol_at s ω hω

theorem matrix_transpose_mul_classWeight : D.matrix.transpose.mulVec D.classWeight = 0 := by
  funext i
  change (∑ r, (Geometry.shiftedCurve q s).lag (D.reps r) (D.atoms i) * D.classWeight r) = 0
  simpa only [mul_comm] using (D.class_sum_symbol (D.atoms i) (D.atoms_grid i)).trans
    (D.symbol_zero_support i)

end polyak.ModeLocking.RegularData
