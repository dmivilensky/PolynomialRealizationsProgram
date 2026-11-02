import jacobi.Rearrangement.AffinePartition
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
An arbitrary finite graph with nonnegative same-side-favoring interactions
has larger reflection partition sum when every vertex pair is sorted in the
same direction. Cycles, including their repeated edges at order two, are
instances of this theorem. No simplicity or connectivity is required.
Source: polarization proof of the Brascamp–Lieb–Luttinger inequality.
Use: encodes density values on a reflection pair as one affine spin constraint.
-/
namespace jacobi.Rearrangement
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

/-- A two-valued vertex potential is a nonnegative baseline plus a preferred-spin bonus.
Use: encodes density values on a reflection pair as one affine spin constraint.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: check both spins and both possible orders of the two real values. -/
theorem spin_potential_expansion (a b : ℝ) (σ : ZMod 2) :
    (if σ=0 then a else b)=min a b+(max a b-min a b)*
      (if σ=(if b ≤ a then (0 : ZMod 2) else 1) then 1 else 0) := by
  by_cases hab : b ≤ a
  · fin_cases σ <;> split_ifs <;> simp_all
  · have hab' : a ≤ b := (not_le.mp hab).le
    fin_cases σ <;> split_ifs <;> simp_all

/-- The homogeneous vertex constraint places the larger value at spin zero.
Use: identifies the homogeneous affine partition with simultaneous polarization.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: split whether the spin is zero and simplify the baseline and bonus. -/
theorem spin_sorted_expansion (a b : ℝ) (σ : ZMod 2) :
    min a b+(max a b-min a b)*(if σ=0 then 1 else 0)=
      if σ=0 then max a b else min a b := by
  by_cases hσ : σ=0 <;> simp [hσ]

/-- A same-side interaction is a baseline plus the bonus for a homogeneous spin equation.
Use: the exponential kernel factors in the finite reflection partition.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: equality of spins is equivalent to their difference being zero. -/
theorem spin_interaction_expansion (A B : ℝ) (σ τ : ZMod 2) :
    (if σ=τ then A else B)=B+(A-B)*(if σ-τ=0 then 1 else 0) := by
  by_cases h : σ=τ <;> simp [sub_eq_zero,h]

/-- Evaluation of one spin coordinate as an actual additive homomorphism.
Use: places vertex and edge factors in the proved affine-fiber comparison theorem.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def spinEvaluation {V : Type*} (v : V) : (V → ZMod 2) →+ ZMod 2 where
  toFun σ := σ v
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Sorting all vertex pairs increases the full finite graph reflection partition.
Use: a cycle graph gives the finite orbit inequality for every spectral moment G_p.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: express vertex bonuses and edge bonuses as affine additive equations.
The proved nonnegative affine partition comparison homogenizes all vertex
preferences simultaneously and leaves the already homogeneous edges unchanged. -/
theorem graph_partition_sorted {V E : Type*} [Fintype V] [Fintype E]
    (left right : E → V) (a b : V → ℝ) (A B : E → ℝ)
    (ha : ∀ v, 0 ≤ a v) (hb : ∀ v, 0 ≤ b v) (hB : ∀ e, 0 ≤ B e) (hAB : ∀ e, B e ≤ A e) :
    (∑ σ : V → ZMod 2, (∏ v, if σ v=0 then a v else b v)*
      ∏ e, if σ (left e)=σ (right e) then A e else B e) ≤
    ∑ σ : V → ZMod 2, (∏ v, if σ v=0 then max (a v) (b v) else min (a v) (b v))*
      ∏ e, if σ (left e)=σ (right e) then A e else B e := by
  classical
  -- Vertex equations may be affine; every edge equation is already homogeneous.
  let f : V ⊕ E → (V → ZMod 2) →+ ZMod 2 := Sum.elim spinEvaluation
    (fun e => spinEvaluation (left e)-spinEvaluation (right e))
  let h : V ⊕ E → ZMod 2 := Sum.elim (fun v => if b v ≤ a v then 0 else 1) (fun _ => 0)
  let β : V ⊕ E → ℝ := Sum.elim (fun v => min (a v) (b v)) B
  let γ : V ⊕ E → ℝ := Sum.elim (fun v => max (a v) (b v)-min (a v) (b v))
    (fun e => A e-B e)
  have hβ (i : V ⊕ E) : 0 ≤ β i := by
    cases i with
    | inl v => exact le_min (ha v) (hb v)
    | inr e => exact hB e
  have hγ (i : V ⊕ E) : 0 ≤ γ i := by
    cases i with
    | inl v => exact sub_nonneg.mpr ((min_le_left _ _).trans (le_max_left _ _))
    | inr e => exact sub_nonneg.mpr (hAB e)
  have H := affine_partition_le_homogeneous f h β γ hβ hγ
  -- Identify both expanded graph products; parallel edges and self-edges require no special cases.
  have hl (σ : V → ZMod 2) : (∏ i : V ⊕ E, (β i+γ i*(if f i σ=h i then 1 else 0))) =
      (∏ v, if σ v=0 then a v else b v)*
        ∏ e, if σ (left e)=σ (right e) then A e else B e := by
    rw [Fintype.prod_sum_type]
    congr 1
    · apply Finset.prod_congr rfl
      intro v _
      exact (spin_potential_expansion (a v) (b v) (σ v)).symm
    · apply Finset.prod_congr rfl
      intro e _
      exact (spin_interaction_expansion (A e) (B e) (σ (left e)) (σ (right e))).symm
  have hr (σ : V → ZMod 2) : (∏ i : V ⊕ E, (β i+γ i*(if f i σ=0 then 1 else 0))) =
      (∏ v, if σ v=0 then max (a v) (b v) else min (a v) (b v))*
        ∏ e, if σ (left e)=σ (right e) then A e else B e := by
    rw [Fintype.prod_sum_type]
    congr 1
    · apply Finset.prod_congr rfl
      intro v _
      exact spin_sorted_expansion (a v) (b v) (σ v)
    · apply Finset.prod_congr rfl
      intro e _
      exact (spin_interaction_expansion (A e) (B e) (σ (left e)) (σ (right e))).symm
  calc
    _ = ∑ σ : V → ZMod 2, ∏ i : V ⊕ E, (β i+γ i*(if f i σ=h i then 1 else 0)) :=
      Finset.sum_congr rfl (fun σ _ => (hl σ).symm)
    _ ≤ ∑ σ : V → ZMod 2, ∏ i : V ⊕ E, (β i+γ i*(if f i σ=0 then 1 else 0)) := by
      convert H using 1 <;> congr 1 <;> funext σ <;>
        apply Finset.prod_congr rfl <;> intro i _ <;> split_ifs <;> rfl
    _ = _ := Finset.sum_congr rfl (fun σ _ => hr σ)

end jacobi.Rearrangement
