import krylov.Stability.CompactProductZero
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(c), genuine C-one compact frozen-estimate products.
Use: freeze only the original reference estimate in actual finite residual
weights while retaining the actual varying searched line lengths and defects.
Source: the proved compact diagonal-zero product estimate and finite smooth
scalar inversion/products; every zero factor follows from true reference data.
-/

namespace krylov.Cancellation
noncomputable section
open Set Filter Topology
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- Replacing the actual observed estimates in finite chronological residual
products by their genuine reference values changes the result by a common
compact-uniform quadratic remainder under C-one data alone.
Use: apply to actual native DC searches, original data-only estimates and real
physical fresh defects; no smoothness of a desired remainder is assumed.
Article: main_krylov, thm:dcs(c).
With freezeSearch=true the actual searched lengths are frozen as well.
Proof: true smooth finite inversion/products make each difference of actual
and frozen weights C-one on the diagonal compact set and exactly zero there.
The real fresh defects vanish on quadratic references. The proved compact
product estimate bounds their actual finite sum by one squared perturbation norm. -/
theorem compact_frozen_residual_products (alpha a : X → ℕ → ℝ) (d : X → ℕ → ℝ)
    (N : ℕ) (K : Set X) (hK : IsCompact K)
    (halpha : ∀ x∈K,∀ l<N,ContDiffAt ℝ 1 (fun y => alpha y l) x)
    (ha : ∀ x∈K,∀ l<N,ContDiffAt ℝ 1 (fun y => a y l) x)
    (ha0 : ∀ x∈K,∀ l<N,a x l≠0)
    (hd : ∀ x∈K,∀ j<N,ContDiffAt ℝ 1 (fun y => d y j) x)
    (hd0 : ∀ x∈K,∀ j<N,d x j=0) (freezeSearch : Bool := false) :
    ∃ δ C : ℝ,0<δ ∧ 0≤C ∧ ∀ x∈K,∀ y : X,‖y-x‖≤δ →
      ‖(∑ j∈Finset.range N,(∏ l∈Finset.Ico (j+1) N,(1-alpha y l/a y l))*d y j)-
        (∑ j∈Finset.range N,(∏ l∈Finset.Ico (j+1) N,(1-(if freezeSearch then alpha x l else alpha y l)/a x l))*d y j)‖≤C*‖y-x‖^2 := by
  let u := fun p : X × X => fun j : Fin N =>
    (∏ l∈Finset.Ico (j.val+1) N,(1-alpha p.2 l/a p.2 l))-
      (∏ l∈Finset.Ico (j.val+1) N,(1-(if freezeSearch then alpha p.1 l else alpha p.2 l)/a p.1 l))
  have hu : ∀ x∈K,ContDiffAt ℝ 1 u (x,x) := by
    intro x hx
    apply contDiffAt_pi.mpr
    intro j
    have hactual : ContDiffAt ℝ 1 (fun p : X × X =>
        ∏ l∈Finset.Ico (j.val+1) N,(1-alpha p.2 l/a p.2 l)) (x,x) := by
      apply contDiffAt_prod
      intro l hl
      have hlN := (Finset.mem_Ico.mp hl).2
      have hα : ContDiffAt ℝ 1 (fun p : X × X => alpha p.2 l) (x,x) := (halpha x hx l hlN).comp (x,x) contDiffAt_snd
      have hβ : ContDiffAt ℝ 1 (fun p : X × X => a p.2 l) (x,x) := (ha x hx l hlN).comp (x,x) contDiffAt_snd
      exact contDiffAt_const.sub (hα.div hβ (ha0 x hx l hlN))
    have hfrozen : ContDiffAt ℝ 1 (fun p : X × X =>
        ∏ l∈Finset.Ico (j.val+1) N,(1-(if freezeSearch then alpha p.1 l else alpha p.2 l)/a p.1 l)) (x,x) := by
      apply contDiffAt_prod
      intro l hl
      have hlN := (Finset.mem_Ico.mp hl).2
      have hα : ContDiffAt ℝ 1 (fun p : X × X => if freezeSearch then alpha p.1 l else alpha p.2 l) (x,x) := by
        cases freezeSearch with
        | false => exact (halpha x hx l hlN).comp (x,x) contDiffAt_snd
        | true => exact (halpha x hx l hlN).comp (x,x) contDiffAt_fst
      have hβ : ContDiffAt ℝ 1 (fun p : X × X => a p.1 l) (x,x) := (ha x hx l hlN).comp (x,x) contDiffAt_fst
      exact contDiffAt_const.sub (hα.div hβ (ha0 x hx l hlN))
    exact hactual.sub hfrozen
  obtain ⟨δ,C,hδ,hC,hbound⟩ := krylov.Stability.compact_zero_product_sum u
    (fun y (j : Fin N) => d y j.val) K hK hu
    (fun x hx => contDiffAt_pi.mpr (fun j => hd x hx j j.isLt))
    (fun x _ => by funext j;simp only [u,ite_self,sub_self,Pi.zero_apply])
    (fun x hx => by funext j;exact hd0 x hx j j.isLt)
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx y hy
  have h := hbound x hx y hy
  simp only [u,sub_mul,Finset.sum_sub_distrib] at h
  rw [Fin.sum_univ_eq_sum_range (fun j => (∏ l∈Finset.Ico (j+1) N,(1-alpha y l/a y l))*d y j),
    Fin.sum_univ_eq_sum_range (fun j => (∏ l∈Finset.Ico (j+1) N,(1-(if freezeSearch then alpha x l else alpha y l)/a x l))*d y j)] at h
  exact h

end
end krylov.Cancellation
