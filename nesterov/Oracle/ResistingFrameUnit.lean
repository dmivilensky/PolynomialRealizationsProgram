import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! A genuine unit vector orthogonal to any sufficiently small finite family. -/
namespace nesterov.Oracle
noncomputable section
open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_unit_orthogonal_finite {I : Type*} [Fintype I] (u : I→E)
    (hcard : Fintype.card I<Module.finrank ℝ E) :
    ∃ w : E,‖w‖=1 ∧ ∀ i : I,inner ℝ w (u i)=0 := by
  let U := Submodule.span ℝ (Set.range u)
  have hU : Module.finrank ℝ U≤Fintype.card I := finrank_range_le_card u
  have hdim := U.finrank_add_finrank_orthogonal
  have horth : 0<Module.finrank ℝ Uᗮ := by omega
  obtain ⟨v,hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp horth
  have hve : (v:E)≠0 := by
    intro hh
    apply hv
    exact Subtype.ext hh
  have hn : ‖(v:E)‖≠0 := norm_ne_zero_iff.mpr hve
  refine ⟨‖(v:E)‖⁻¹ • (v:E),?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ hn]
  · intro i
    have hi := (U.mem_orthogonal' (v:E)).mp v.property (u i)
      (Submodule.subset_span ⟨i,rfl⟩)
    simp only [inner_smul_left,hi,mul_zero,starRingEnd_apply,star_trivial]

end
end nesterov.Oracle
