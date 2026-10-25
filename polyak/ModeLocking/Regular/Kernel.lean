import polyak.ModeLocking.Regular.Extremals
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Rank in (R1) identifies the complete kernel, not just a candidate vector. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem primal_ne_zero : (fun i => (D.primal i : ℝ)) ≠ 0 := by
  intro he
  have i : Fin D.d := ⟨0, D.d_pos⟩
  have hzero := congrFun he i
  change (D.primal i : ℝ) = 0 at hzero
  exact (D.primal_pos i).ne' (by exact_mod_cast hzero)

theorem kernel_finrank : Module.finrank ℝ D.matrix.mulVecLin.ker = 1 := by
  have hn := D.matrix.mulVecLin.finrank_range_add_finrank_ker
  have hr : Module.finrank ℝ D.matrix.mulVecLin.range = D.d - 1 := D.rank
  rw [Module.finrank_pi, Fintype.card_fin] at hn
  have hp := D.d_pos
  omega

theorem kernel_eq_span : D.matrix.mulVecLin.ker =
    Submodule.span ℝ {(fun i => (D.primal i : ℝ))} :=
  eq_span_singleton_of_mem_of_finrank_eq_one D.kernel_finrank
    D.matrix_mul_primal D.primal_ne_zero

theorem kernel_unique {v : Fin D.d → ℝ} (hv : D.matrix.mulVec v = 0) :
    ∃ c : ℝ, ∀ i, v i = c * (D.primal i : ℝ) := by
  have hmem : v ∈ D.matrix.mulVecLin.ker := hv
  rw [D.kernel_eq_span] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨c, fun i => by simpa using (congrFun hc i).symm⟩

theorem positive_kernel_unique {v : Fin D.d → ℝ} (hv : D.matrix.mulVec v = 0)
    (hpos : ∀ i, 0 ≤ v i) (hne : v ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, v i = c * (D.primal i : ℝ) := by
  obtain ⟨c, hc⟩ := D.kernel_unique hv
  refine ⟨c, ?_, hc⟩
  have i : Fin D.d := ⟨0, D.d_pos⟩
  have hp : 0 < (D.primal i : ℝ) := by exact_mod_cast D.primal_pos i
  have hcne : c ≠ 0 := by
    intro hz
    apply hne
    funext j
    change v j = 0
    simpa only [hz, zero_mul] using hc j
  have hnn := hpos i
  rw [hc i] at hnn
  exact lt_of_le_of_ne ((mul_nonneg_iff_of_pos_right hp).mp hnn) hcne.symm

end polyak.ModeLocking.RegularData
