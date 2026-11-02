import krylov.Stability.CompactCoefficients
import Mathlib.Analysis.Normed.Group.Bounded
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(b), common C-one field bounds.
Use: derive actual compact mean-value constants and combine finitely many
true remainder bounds without assuming a uniform trajectory estimate.
Source: the reused compact C-one mean-value theorem and the standard compact
image bound; finite induction supplies common radii and constants.
-/

namespace krylov.Stability
noncomputable section
open Set Metric Filter Topology
variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Genuine C-one fields have common bounded reference values, first-order
increments and bounded nearby values on every compact reference family.
Use: compact quadratic product estimates need only actual primitive C-one data.
Article: main_krylov, apH:dcs2(b), true compact field bounds.
Proof: apply the existing mean-value theorem on the open C-one locus and
the actual compact-image norm bound, then restrict the common radius to one. -/
theorem compact_c1_field_bounds (f : X → F) (K : Set X) (hK : IsCompact K)
    (hf : ∀ x∈K,ContDiffAt ℝ 1 f x) :
    ∃ delta L M : ℝ,0<delta ∧ 0≤L ∧ 0≤M ∧
      (∀ x∈K,‖f x‖≤M) ∧ ∀ x∈K,∀ y : X,‖y-x‖≤delta →
        ‖f y-f x‖≤L*‖y-x‖ ∧ ‖f y‖≤M+L := by
  let U := interior {x | ContDiffAt ℝ 1 f x}
  have hKU : K⊆U := fun x hx => mem_interior_iff_mem_nhds.mpr ((hf x hx).eventually (by simp))
  obtain ⟨delta,L,hd,hL,hbound⟩ := compact_local_lipschitz f U K isOpen_interior hK hKU
    (fun x hx => (show ContDiffAt ℝ 1 f x from interior_subset hx).contDiffWithinAt)
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
  refine ⟨min delta 1,L,max M 0,lt_min hd zero_lt_one,hL,le_max_right _ _,
    fun x hx => (hM x hx).trans (le_max_left _ _),?_⟩
  intro x hx y hy
  have he := hbound x hx y (hy.trans (min_le_left _ _))
  refine ⟨he,?_⟩
  have ht : ‖f y‖≤‖f y-f x‖+‖f x‖ := norm_le_norm_sub_add _ _
  exact ht.trans ((add_le_add he ((hM x hx).trans (le_max_left _ _))).trans (by
    have hs := mul_le_mul_of_nonneg_left (hy.trans (min_le_right _ _)) hL
    linarith))

variable {ι : Type*} [Fintype ι]

omit [NormedSpace ℝ X] [ProperSpace X] [NormedSpace ℝ F] in
/-- Finitely many proved genuine compact quadratic remainders share one
positive radius and one nonnegative constant, including an empty family.
Use: assemble all actual scalar window coordinates into a vector estimate.
Article: main_krylov, apH:dcs2(b), finite common remainder constants.
Proof: finite induction intersects two true tubes and adds their nonnegative
constants; no coordinate maximum or nonempty-index hypothesis is supplied. -/
theorem finite_compact_quadratic_bounds (f : ι → X × X → F) (K : Set X)
    (hf : ∀ i,∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ y : X,‖y-x‖≤delta →
      ‖f i (x,y)‖≤C*‖y-x‖^2) :
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ y : X,‖y-x‖≤delta →
      ∀ i,‖f i (x,y)‖≤C*‖y-x‖^2 := by
  have hfinite (I : Finset ι) : ∃ delta C : ℝ,0<delta ∧ 0≤C ∧
      ∀ x∈K,∀ y : X,‖y-x‖≤delta → ∀ i∈I,‖f i (x,y)‖≤C*‖y-x‖^2 := by
    classical
    induction I using Finset.induction_on with
    | empty => exact ⟨1,0,zero_lt_one,le_refl 0,by simp⟩
    | @insert i I _ ih =>
      obtain ⟨di,Ci,hdi,hCi,hi⟩ := hf i
      obtain ⟨dI,CI,hdI,hCI,hI⟩ := ih
      refine ⟨min di dI,Ci+CI,lt_min hdi hdI,add_nonneg hCi hCI,?_⟩
      intro x hx y hy j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact (hi x hx y (hy.trans (min_le_left _ _))).trans
          (mul_le_mul_of_nonneg_right (by linarith : Ci≤Ci+CI) (sq_nonneg _))
      · exact (hI x hx y (hy.trans (min_le_right _ _)) j hj).trans
          (mul_le_mul_of_nonneg_right (by linarith : CI≤Ci+CI) (sq_nonneg _))
  obtain ⟨delta,C,hd,hC,hbound⟩ := hfinite Finset.univ
  exact ⟨delta,C,hd,hC,fun x hx y hy i => hbound x hx y hy i (Finset.mem_univ i)⟩

end
end krylov.Stability
