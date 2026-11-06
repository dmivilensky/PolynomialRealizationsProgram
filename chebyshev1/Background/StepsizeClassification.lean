import chebyshev1.Stepsize.Basic
import chebyshev1.Jacobi.TerminalClassification
import Mathlib.LinearAlgebra.Lagrange

/-! Exact gradient schedules are precisely permutations of the reciprocal Chebyshev roots. -/
namespace chebyshev1.Stepsize
noncomputable section
open Polynomial Set
open scoped BigOperators

def chebyshevRoot (I : SpectralInterval) (N : ℕ) (j : Fin N) : ℝ :=
  I.lambda (JacobiData.chebyshevNode N j)

theorem chebyshevRoot_mem (I : SpectralInterval) (N : ℕ) (j : Fin N) :
    chebyshevRoot I N j ∈ Icc I.mu I.L :=
  I.lambda_mem ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem chebyshevRoot_ne_zero (I : SpectralInterval) (N : ℕ) (j : Fin N) :
    chebyshevRoot I N j ≠ 0 :=
  (I.mu_pos.trans_le (chebyshevRoot_mem I N j).1).ne'

theorem chebyshevRoot_injective (I : SpectralInterval) (N : ℕ) :
    Function.Injective (chebyshevRoot I N) := by
  intro i j hij
  apply JacobiData.chebyshevNode_injective N
  simpa only [chebyshevRoot, I.z_lambda] using congrArg I.z hij

theorem residual_chebyshevRoot (I : SpectralInterval) (N : ℕ) (j : Fin N) :
    (I.residual N).eval (chebyshevRoot I N j) = 0 := by
  have ht := JacobiData.monicChebyshev_node N j
  have hc : ((2 : ℝ)^(N-1))⁻¹ ≠ 0 := by positivity
  have hz : (Polynomial.Chebyshev.T ℝ N).eval (JacobiData.chebyshevNode N j) = 0 := by
    exact (mul_eq_zero.mp (by simpa only [JacobiData.monicChebyshev, eval_mul, eval_C] using ht)).resolve_left hc
  rw [I.residual_eval, chebyshevRoot, I.z_lambda, hz, zero_div]

theorem polynomial_eval_prod (gamma : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    (polynomial gamma N).eval x = ∏ s ∈ Finset.range N, (1-gamma s*x) := by
  induction N with
  | zero => simp [polynomial]
  | succ N ih =>
    rw [polynomial, eval_mul, eval_sub, eval_one, eval_mul, eval_C, eval_X,
      Finset.prod_range_succ, ih]
    ring

theorem polynomial_natDegree_le (gamma : ℕ → ℝ) (N : ℕ) :
    (polynomial gamma N).natDegree ≤ N := by
  induction N with
  | zero => simp [polynomial]
  | succ N ih =>
    have hl : (1-C (gamma N)*X : ℝ[X]).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (max_le (by simp)
        ((natDegree_C_mul_le _ _).trans (by simp)))
    exact (natDegree_mul_le).trans (by omega)

private theorem normalized_roots_unique {N : ℕ} (r : Fin N → ℝ)
    (hi : Function.Injective r) (hne : ∀ i, r i ≠ 0)
    (p q : ℝ[X]) (hp : p.natDegree ≤ N) (hq : q.natDegree ≤ N)
    (hzero : p.eval 0 = q.eval 0) (hr : ∀ i, p.eval (r i) = q.eval (r i)) : p = q := by
  let S := insert 0 (Finset.univ.image r)
  have hn : (0 : ℝ) ∉ Finset.univ.image r := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i
    exact hne i
  have hcard : S.card = N+1 := by
    simp only [S, Finset.card_insert_of_notMem hn,
      Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]
  apply eq_of_degrees_lt_of_eval_finset_eq S
  · rw [hcard]
    have hd : p.degree ≤ (N : WithBot ℕ) := degree_le_natDegree.trans (by exact_mod_cast hp)
    exact hd.trans_lt (by exact_mod_cast Nat.lt_succ_self N)
  · rw [hcard]
    have hd : q.degree ≤ (N : WithBot ℕ) := degree_le_natDegree.trans (by exact_mod_cast hq)
    exact hd.trans_lt (by exact_mod_cast Nat.lt_succ_self N)
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hzero
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hr i

/-- The complete iff, including arbitrary ordering and the vacuous zero horizon. -/
theorem finalExact_iff_permutation (gamma : ℕ → ℝ) (I : SpectralInterval) (N : ℕ) :
    FinalExact gamma I N ↔ ∃ σ : Equiv.Perm (Fin N),
      ∀ s : Fin N, gamma s.val = 1/chebyshevRoot I N (σ s) := by
  constructor
  · intro hexact
    have hroots (j : Fin N) : ∃ s : Fin N, gamma s.val*chebyshevRoot I N j = 1 := by
      have hz : (polynomial gamma N).eval (chebyshevRoot I N j) = 0 := by
        rw [final_polynomial_eq gamma I N hexact, residual_chebyshevRoot]
      rw [polynomial_eval_prod, Finset.prod_eq_zero_iff] at hz
      obtain ⟨s, hs, he⟩ := hz
      exact ⟨⟨s, Finset.mem_range.mp hs⟩, by linarith⟩
    let f : Fin N → Fin N := fun j => (hroots j).choose
    have hf (j : Fin N) : gamma (f j).val*chebyshevRoot I N j = 1 := (hroots j).choose_spec
    have hinj : Function.Injective f := by
      intro j k hjk
      apply chebyshevRoot_injective I N
      have hg : gamma (f j).val ≠ 0 := by
        intro hz
        have hh := hf j
        rw [hz, zero_mul] at hh
        norm_num at hh
      apply mul_left_cancel₀ hg
      exact (hf j).trans (by simpa only [hjk] using (hf k).symm)
    let σ := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
    refine ⟨σ.symm, ?_⟩
    intro s
    have hh := hf (σ.symm s)
    change gamma (σ (σ.symm s)).val*chebyshevRoot I N (σ.symm s) = 1 at hh
    rw [σ.apply_symm_apply] at hh
    exact (eq_div_iff (chebyshevRoot_ne_zero I N _)).mpr hh
  · rintro ⟨σ, hgamma⟩
    have he : polynomial gamma N = I.residual N := by
      apply normalized_roots_unique (chebyshevRoot I N)
        (chebyshevRoot_injective I N) (chebyshevRoot_ne_zero I N)
        _ _ (polynomial_natDegree_le gamma N) (by rw [I.residual_natDegree])
      · rw [polynomial_eval_prod, I.residual_eval]
        simp only [mul_zero, sub_zero, Finset.prod_const_one]
        have hz : I.z 0 = I.eta := by simp [SpectralInterval.z, SpectralInterval.eta]
        rw [hz]
        exact (div_self (I.den_ne N)).symm
      · intro j
        rw [residual_chebyshevRoot, polynomial_eval_prod]
        apply Finset.prod_eq_zero (Finset.mem_range.mpr (σ.symm j).isLt)
        have hh := hgamma (σ.symm j)
        simp only [σ.apply_symm_apply] at hh
        rw [hh]
        field_simp [chebyshevRoot_ne_zero I N j]
        ring
    intro x hx
    rw [← polynomial_eval, he]

end
end chebyshev1.Stepsize
