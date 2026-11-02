import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
A finite reflection orbit is a spin partition function with nonnegative
interaction coefficients. Expanding its factors reduces comparison to the
cardinality of affine fibers of additive maps. Translating by one solution
embeds each affine fiber into its homogeneous fiber. This proves the finite
comparison without assuming the analytic rearrangement theorem.
Source: the polarization proof of Brascamp–Lieb–Luttinger via reflection orbits.
Use: each term in the expansion of the cyclic reflection partition function.
-/
namespace jacobi.Rearrangement
open scoped BigOperators Classical

/-- A simultaneous affine fiber has at most as many points as its homogeneous fiber.
Use: each term in the expansion of the cyclic reflection partition function.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: if the affine fiber is nonempty, subtraction of a chosen solution injects
it into the homogeneous fiber. If it is empty, its cardinality is zero. -/
theorem affine_fiber_card_le {G H I : Type*} [AddGroup G] [AddGroup H] [Fintype G] [Fintype I]
    (f : I → G →+ H) (h : I → H) (s : Finset I) :
    (Finset.univ.filter (fun x => ∀ i ∈ s, f i x=h i)).card ≤
      (Finset.univ.filter (fun x => ∀ i ∈ s, f i x=0)).card := by
  classical
  -- A translation is injective even before restricting it to the simultaneous affine fiber.
  let A := Finset.univ.filter (fun x => ∀ i ∈ s, f i x=h i)
  let B := Finset.univ.filter (fun x => ∀ i ∈ s, f i x=0)
  by_cases hA : A.Nonempty
  · obtain ⟨x₀,hx₀⟩ := hA
    have h₀ : ∀ i ∈ s, f i x₀=h i := (Finset.mem_filter.mp hx₀).2
    apply Finset.card_le_card_of_injOn (s := A) (t := B) (fun x => x-x₀)
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,fun i hi => ?_⟩
      rw [map_sub,hx' i hi,h₀ i hi,sub_self]
    · intro x _ y _ he
      exact sub_left_injective he
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change A.card ≤ B.card
    rw [he,Finset.card_empty]
    exact Nat.zero_le _

/-- Expanding a nonnegative interaction partition function produces affine-fiber counts.
Use: replaces the full spin sum by coefficientwise comparisons of simultaneous equations.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: distribute the finite product, interchange the two finite sums, and
identify a product of zero-one indicators with the simultaneous fiber indicator. -/
theorem affine_partition_expansion {G H I : Type*} [Fintype G] [Fintype I]
    (f : I → G → H) (h : I → H) (b c : I → ℝ) :
    (∑ x : G, ∏ i : I, (b i+c i*(if f i x=h i then 1 else 0))) =
      ∑ s : Finset I, ((∏ i ∈ s, c i)*(∏ i ∈ sᶜ, b i))*
        ((Finset.univ.filter (fun x => ∀ i ∈ s, f i x=h i)).card : ℝ) := by
  classical
  -- Nonnegativity is unnecessary for this exact finite polynomial identity.
  have hp (x : G) : (∏ i : I, (b i+c i*(if f i x=h i then 1 else 0))) =
      ∑ s : Finset I, ((∏ i ∈ s, c i)*(∏ i ∈ sᶜ, b i))*
        (if ∀ i ∈ s, f i x=h i then 1 else 0) := by
    simp_rw [add_comm (b _)]
    rw [Fintype.prod_add]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.prod_mul_distrib,Finset.prod_boole]
    split_ifs <;> ring
  simp_rw [hp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.mul_sum,Finset.sum_boole]

/-- Homogenizing all affine spin constraints increases a nonnegative partition function.
Use: all cyclic moment polarization inequalities share this one finite comparison.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: expand into nonnegative coefficients times affine-fiber counts, then
inject every affine fiber into the corresponding homogeneous fiber. -/
theorem affine_partition_le_homogeneous {G H I : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype I] (f : I → G →+ H) (h : I → H) (b c : I → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    (∑ x : G, ∏ i : I, (b i+c i*(if f i x=h i then 1 else 0))) ≤
      ∑ x : G, ∏ i : I, (b i+c i*(if f i x=0 then 1 else 0)) := by
  classical
  -- The only inequality in the argument is the already proved affine-fiber cardinality bound.
  rw [affine_partition_expansion,affine_partition_expansion]
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left
  · norm_cast
    simpa only [Pi.zero_apply] using affine_fiber_card_le f h s
  ·
    exact mul_nonneg (Finset.prod_nonneg (fun i _ => hc i)) (Finset.prod_nonneg (fun i _ => hb i))

end jacobi.Rearrangement
