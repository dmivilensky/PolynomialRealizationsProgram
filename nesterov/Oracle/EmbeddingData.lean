import nesterov.Oracle.EmbeddingFrame
import nesterov.Oracle.ExtensionSmooth

/-! The finite-simplex extension commutes with an orthonormal embedding,
including its actual optimizer moment, potential and gradient. -/
namespace nesterov.Oracle
noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace
variable {I J E : Type*} [Fintype I]
    [Fintype J] [DecidableEq J] [Nonempty J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace ExtensionData

def embed (D : ExtensionData J (EuclideanSpace ℝ I)) (v : I→E) : ExtensionData J E where
  q := D.q
  q_pos := D.q_pos
  q_lt_one := D.q_lt_one
  slopes := fun j=>frameLift v (D.slopes j)
  offsets := D.offsets

omit [DecidableEq J] [Nonempty J] in
theorem embed_moment (D : ExtensionData J (EuclideanSpace ℝ I)) (v : I→E) (α : J→ℝ) :
    moment (D.embed v).slopes α=frameLift v (moment D.slopes α) := by
  simp only [moment,embed,map_sum,map_smul]

omit [DecidableEq J] [Nonempty J] in
theorem embed_raw (D : ExtensionData J (EuclideanSpace ℝ I)) {v : I→E}
    (hv : Orthonormal ℝ v) (y : E) (α : J→ℝ) :
    (D.embed v).raw y α=D.raw (frameCoordinates v y) α := by
  unfold raw
  rw [D.embed_moment,inner_frameLift,norm_frameLift hv]
  rfl

omit [Fintype I] in
theorem moment_eq_support_of_max {K F : Type*} [Fintype K] [DecidableEq K] [Nonempty K]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (D : ExtensionData K F) (y : F) {α : K→ℝ} (hα : α∈Weights K)
    (hmax : ∀ β∈Weights K,D.raw y β≤D.raw y α) : moment D.slopes α=D.support y := by
  have hs := D.optimizer_strong y hα
  have hm := hmax (D.optimizer y) (D.optimizer_weights y)
  have hfrac : ‖moment D.slopes α-D.support y‖^2/(2*(1-D.q))≤0 := by linarith
  have hsq : ‖moment D.slopes α-D.support y‖^2≤0 := by
    simpa only [zero_mul] using
      (div_le_iff₀ (by linarith [D.q_lt_one] : 0<2*(1-D.q))).mp hfrac
  have hn : ‖moment D.slopes α-D.support y‖=0 := by nlinarith [norm_nonneg (moment D.slopes α-D.support y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem embed_support (D : ExtensionData J (EuclideanSpace ℝ I)) {v : I→E}
    (hv : Orthonormal ℝ v) (y : E) :
    (D.embed v).support y=frameLift v (D.support (frameCoordinates v y)) := by
  have hα := (D.embed v).optimizer_weights y
  have hmax : ∀ β∈Weights J,D.raw (frameCoordinates v y) β≤
      D.raw (frameCoordinates v y) ((D.embed v).optimizer y) := by
    intro β hβ
    simpa only [D.embed_raw hv] using (D.embed v).optimizer_max y β hβ
  have hm := moment_eq_support_of_max D (frameCoordinates v y) hα hmax
  change moment (D.embed v).slopes ((D.embed v).optimizer y)=_
  rw [D.embed_moment,hm]

theorem embed_maximum_value (D : ExtensionData J (EuclideanSpace ℝ I)) {v : I→E}
    (hv : Orthonormal ℝ v) (y : E) :
    (D.embed v).raw y ((D.embed v).optimizer y)=
      D.raw (frameCoordinates v y) (D.optimizer (frameCoordinates v y)) := by
  apply le_antisymm
  · rw [D.embed_raw hv]
    exact D.optimizer_max _ _ ((D.embed v).optimizer_weights y)
  · have hh := (D.embed v).optimizer_max y (D.optimizer (frameCoordinates v y))
      (D.optimizer_weights _)
    simpa only [D.embed_raw hv] using hh

theorem embed_potential (D : ExtensionData J (EuclideanSpace ℝ I)) {v : I→E}
    (hv : Orthonormal ℝ v) (y : E) :
    (D.embed v).potential y=D.q/2*‖y‖^2+
      D.raw (frameCoordinates v y) (D.optimizer (frameCoordinates v y)) := by
  unfold potential
  rw [D.embed_maximum_value hv]
  rfl

theorem embed_field (D : ExtensionData J (EuclideanSpace ℝ I)) {v : I→E}
    (hv : Orthonormal ℝ v) (y : E) :
    (D.embed v).field y=D.q • y+frameLift v (D.support (frameCoordinates v y)) := by
  unfold field
  rw [D.embed_support hv]
  rfl

end ExtensionData
end
end nesterov.Oracle
