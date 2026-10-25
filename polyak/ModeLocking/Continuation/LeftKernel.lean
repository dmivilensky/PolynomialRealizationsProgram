import polyak.ModeLocking.Continuation.Transversality

/-! The left kernel has precisely the positive class-weight direction. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem classWeight_ne_zero : D.classWeight ≠ 0 := by
  intro he
  have i : Fin D.d := ⟨0, D.d_pos⟩
  have hz := congrFun he i
  change D.classWeight i = 0 at hz
  exact (D.classWeight_pos i).ne' hz

theorem classWeight_sum_pos : 0 < ∑ i, D.classWeight i :=
  Finset.sum_pos' (fun i _ => (D.classWeight_pos i).le)
    ⟨⟨0, D.d_pos⟩, Finset.mem_univ _, D.classWeight_pos _⟩

theorem left_kernel_finrank : Module.finrank ℝ D.matrix.transpose.mulVecLin.ker = 1 := by
  have hn := D.matrix.transpose.mulVecLin.finrank_range_add_finrank_ker
  have hr : Module.finrank ℝ D.matrix.transpose.mulVecLin.range = D.d - 1 := by
    change D.matrix.transpose.rank = D.d - 1
    rw [Matrix.rank_transpose]
    exact D.rank
  rw [Module.finrank_pi, Fintype.card_fin] at hn
  have hp := D.d_pos
  omega

theorem left_kernel_eq_span : D.matrix.transpose.mulVecLin.ker =
    Submodule.span ℝ {D.classWeight} :=
  eq_span_singleton_of_mem_of_finrank_eq_one D.left_kernel_finrank
    D.matrix_transpose_mul_classWeight D.classWeight_ne_zero

theorem left_kernel_unique {v : Fin D.d → ℝ} (hv : D.matrix.transpose.mulVec v = 0) :
    ∃ c : ℝ, ∀ i, v i = c * D.classWeight i := by
  have hmem : v ∈ D.matrix.transpose.mulVecLin.ker := hv
  rw [D.left_kernel_eq_span] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨c, fun i => by simpa using (congrFun hc i).symm⟩

end polyak.ModeLocking.RegularData
