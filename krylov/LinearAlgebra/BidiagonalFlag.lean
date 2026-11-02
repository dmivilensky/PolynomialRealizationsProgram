import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Span.Basic
set_option autoImplicit false
/-!
Article: main_krylov, apE:Pi, exact bidiagonal flag back substitution.
Use: derive every old-flag column from the original bidiagonal evaluated
steps, with division only by their nonzero diagonal coefficients.
Source: finite triangular back substitution and chronological interval products.
-/

namespace krylov.LinearAlgebra
noncomputable section
open scoped BigOperators
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A selected bidiagonal basis preserves the whole corresponding unit prefix.
Use: separate old CG directions from the genuine oblique tail.
Article: main_krylov, apE:Pi, Pi_l u_k=u_k for k<=l.
Proof: cancel each true nonzero diagonal after the preceding selected column. -/
theorem bidiagonal_flag_prefix (P : V →L[ℝ] V) (u s : ℕ → V)
    (a b : ℕ → ℝ) (N l : ℕ)
    (hb : ∀ k<N,b k≠0) (hs0 : s 0=b 0 • u 0)
    (hs : ∀ k,k+1<N → s (k+1)=a k • u k+b (k+1) • u (k+1))
    (hP : ∀ k<N,P (s k)=if k≤l then s k else 0)
    (k : ℕ) (hk : k<N) (hl : k≤l) : P (u k)=u k := by
  induction k with
  | zero =>
    have h := hP 0 hk
    rw [ite_eq_left (Nat.zero_le l),hs0,map_smul] at h
    have hh := congrArg (fun v => (b 0)⁻¹ • v) h
    simpa only [smul_smul,inv_mul_cancel₀ (hb 0 hk),one_smul] using hh
  | succ k ih =>
    have hi := ih (by omega) (by omega)
    have h := hP (k+1) hk
    rw [ite_eq_left hl,hs k hk,map_add,map_smul,map_smul,hi] at h
    have he := add_left_cancel h
    have hh := congrArg (fun v => (b (k+1))⁻¹ • v) he
    simpa only [smul_smul,inv_mul_cancel₀ (hb (k+1) hk),one_smul] using hh

/-- The actual zero selected bidiagonal column gives its exact tail recurrence.
Use: invert the real trial diagonal rather than an amplitude or trial error.
Article: main_krylov, apE:Pi, oblique back substitution.
Proof: apply the true flag and multiply by the nonzero diagonal inverse. -/
theorem bidiagonal_flag_recurrence (P : V →L[ℝ] V) (u s : ℕ → V)
    (a b : ℕ → ℝ) (l k : ℕ)
    (hb : b (k+1)≠0) (hl : l<k+1)
    (hs : s (k+1)=a k • u k+b (k+1) • u (k+1))
    (hP : P (s (k+1))=if k+1≤l then s (k+1) else 0) :
    P (u (k+1))=(-a k/b (k+1)) • P (u k) := by
  have h := hP
  rw [ite_eq_right (by omega),hs,map_add,map_smul,map_smul] at h
  have hh := congrArg (fun v => (b (k+1))⁻¹ • v) h
  simp only [smul_add,smul_smul,inv_mul_cancel₀ hb,one_smul,smul_zero] at hh
  have he : P (u (k+1))= -((b (k+1))⁻¹*a k) • P (u k) := by
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hh)
  rw [he]
  congr 1
  ring

/-- Every real oblique tail column is the printed chronological product times
its single boundary direction, including zero off-diagonal factors.
Use: obtain the full original r_lk formula without excluding exact trials.
Article: main_krylov, apE:Pi.
Proof: start at the preserved boundary and iterate the actual nonzero-diagonal
recurrence, appending one factor to its genuine finite interval product. -/
theorem bidiagonal_flag_tail (P : V →L[ℝ] V) (u s : ℕ → V)
    (a b : ℕ → ℝ) (N l : ℕ)
    (hb : ∀ k<N,b k≠0) (hs0 : s 0=b 0 • u 0)
    (hs : ∀ k,k+1<N → s (k+1)=a k • u k+b (k+1) • u (k+1))
    (hP : ∀ k<N,P (s k)=if k≤l then s k else 0)
    (k : ℕ) (hk : k<N) (hl : l≤k) :
    P (u k)=(∏ j∈Finset.Ico (l+1) (k+1),-a (j-1)/b j) • u l := by
  induction k,hl using Nat.le_induction with
  | base =>
    rw [Finset.Ico_self,Finset.prod_empty,one_smul]
    exact bidiagonal_flag_prefix P u s a b N l hb hs0 hs hP l hk le_rfl
  | succ k hl ih =>
    rw [bidiagonal_flag_recurrence P u s a b l k (hb (k+1) hk) (by omega)
      (hs k hk) (hP (k+1) hk),ih (by omega),smul_smul,
      Finset.prod_Ico_succ_top (a := l+1) (b := k+1) (by omega)]
    simp only [Nat.add_sub_cancel]
    congr 1
    exact mul_comm _ _

/-- Every genuine bidiagonal evaluated-step prefix spans exactly its original
unit-vector prefix, with no nonzero off-diagonal requirement.
Use: derive equality of the actual evaluated and CG old flags.
Article: main_krylov, apE:Pi.
Proof: every evaluated column belongs to the unit prefix by its two-term
formula. Conversely, successive nonzero diagonal cancellation expresses each
unit vector in the actual evaluated-step prefix. -/
theorem bidiagonal_prefix_span (u s : ℕ → V) (a b : ℕ → ℝ) (N k : ℕ)
    (hk : k≤N) (hb : ∀ j<N,b j≠0) (hs0 : s 0=b 0 • u 0)
    (hs : ∀ j,j+1<N → s (j+1)=a j • u j+b (j+1) • u (j+1)) :
    Submodule.span ℝ (s '' Set.Iio k)=Submodule.span ℝ (u '' Set.Iio k) := by
  let S := Submodule.span ℝ (s '' Set.Iio k)
  let U := Submodule.span ℝ (u '' Set.Iio k)
  have hU : ∀ j<k,u j∈S := by
    intro j
    induction j with
    | zero =>
      intro hj
      have he : u 0=(b 0)⁻¹ • s 0 := by
        rw [hs0,smul_smul,inv_mul_cancel₀ (hb 0 (hj.trans_le hk)),one_smul]
      rw [he]
      exact S.smul_mem _ (Submodule.subset_span ⟨0,hj,rfl⟩)
    | succ j ih =>
      intro hj
      have he : u (j+1)=(b (j+1))⁻¹ • (s (j+1)-a j • u j) := by
        rw [hs j (hj.trans_le hk),add_sub_cancel_left,smul_smul,
          inv_mul_cancel₀ (hb (j+1) (hj.trans_le hk)),one_smul]
      rw [he]
      exact S.smul_mem _ (S.sub_mem (Submodule.subset_span ⟨j+1,hj,rfl⟩)
        (S.smul_mem _ (ih (by omega))))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    cases j with
    | zero => rw [hs0];exact U.smul_mem _ (Submodule.subset_span ⟨0,hj,rfl⟩)
    | succ j =>
      change j+1<k at hj
      rw [hs j (hj.trans_le hk)]
      exact U.add_mem (U.smul_mem _ (Submodule.subset_span ⟨j,by change j<k;omega,rfl⟩))
        (U.smul_mem _ (Submodule.subset_span ⟨j+1,hj,rfl⟩))
  · exact Submodule.span_le.mpr (by rintro _ ⟨j,hj,rfl⟩;exact hU j hj)

end
end krylov.LinearAlgebra
