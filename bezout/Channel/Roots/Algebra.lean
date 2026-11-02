import bezout.Channel.Roots.Factors
import bezout.Channel.Roots.Energy

/-!
Article: bezout, Proposition D.1, root-order independence and continuous extension.
Use: the actual diagonal insertion profile is a polynomial with one affine
factor omitted. Reordering steps therefore only reindexes physical columns.
Proof: replace one factor by one in the ordered causal product, then use
commutative finite-product reindexing. No division by a root is used.
-/

namespace bezout.Channel.Roots
noncomputable section
open Polynomial
open scoped BigOperators

/-- Natural-index extension of an arbitrary finite root-step schedule. -/
def extend {N : ℕ} (α : Fin N → ℝ) (j : ℕ) : ℝ := if hj : j<N then α ⟨j,hj⟩ else 0

/-- Extension preserves every actual finite call coefficient. -/
@[simp] theorem extend_fin {N : ℕ} (α : Fin N → ℝ) (j : Fin N) : extend α j.val=α j := by
  simp [extend,j.isLt]

/-- A commutative causal product is its finite product, independently of order. -/
theorem orderedProduct_eq_prod {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    chebyshev1.orderedProduct f n=∏ j ∈ Finset.range n, f j := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chebyshev1.orderedProduct,Finset.prod_range_succ,ih,mul_comm]

/-- The ordinary root-step polynomial is its literal finite affine product. -/
theorem polynomial_eq_prod (γ : ℕ → ℝ) (N : ℕ) :
    chebyshev1.Stepsize.polynomial γ N=∏ j ∈ Finset.range N, (1-C (γ j)*X) := by
  induction N with
  | zero => simp [chebyshev1.Stepsize.polynomial]
  | succ N ih => rw [chebyshev1.Stepsize.polynomial,Finset.prod_range_succ,ih]; ring

/-- Finite natural extension gives precisely the terminal product of the actual steps. -/
theorem polynomial_extend {N : ℕ} (α : Fin N → ℝ) :
    chebyshev1.Stepsize.polynomial (extend α) N=terminal α := by
  rw [polynomial_eq_prod,Finset.prod_range]
  simp only [extend_fin,terminal]

/-- The concrete root schedule is the natural extension of its actual finite steps. -/
theorem schedule_eq_extend (I : chebyshev1.SpectralInterval) (N : ℕ)
    (e : Equiv.Perm (Fin N)) : schedule I N e=extend (steps I N e) := rfl

/-- Every ordering of the concrete Chebyshev roots has the exact normalized terminal. -/
theorem schedule_polynomial (I : chebyshev1.SpectralInterval) (N : ℕ)
    (e : Equiv.Perm (Fin N)) : chebyshev1.Stepsize.polynomial (schedule I N e) N=I.residual N := by
  rw [schedule_eq_extend,polynomial_extend,terminal_steps_eq]

/-- The concrete scheduled realization belongs to the exact-terminal comparison class. -/
theorem schedule_finalExact (I : chebyshev1.SpectralInterval) (N : ℕ)
    (e : Equiv.Perm (Fin N)) : chebyshev1.Stepsize.FinalExact (schedule I N e) I N := by
  intro x _
  rw [← chebyshev1.Stepsize.polynomial_eval,schedule_polynomial]

/-- A finite product with one omitted factor is unchanged by finite/Nat indexing. -/
theorem prod_fin_erase {M : Type*} [CommMonoid M] {N : ℕ} (f : ℕ → M) (s : Fin N) :
    (∏ j ∈ (Finset.univ : Finset (Fin N)).erase s, f j.val) =
      ∏ j ∈ (Finset.range N).erase s.val, f j := by
  apply Finset.prod_bij (fun j _ => j.val)
  · intro j hj
    simp only [Finset.mem_erase,Finset.mem_univ,and_true] at hj
    simp only [Finset.mem_erase,Finset.mem_range]
    exact ⟨fun he => hj (Fin.ext he),j.isLt⟩
  · intro i _ j _ he
    exact Fin.ext he
  · intro j hj
    have hlt := (Finset.mem_erase.mp hj).2
    have hN : j<N := Finset.mem_range.mp hlt
    refine ⟨⟨j,hN⟩,?_,rfl⟩
    simp only [Finset.mem_erase,Finset.mem_univ,and_true]
    intro he
    exact (Finset.mem_erase.mp hj).1 (congrArg Fin.val he)
  · intro _ _
    rfl

/-- The diagonal profile as a globally defined continuous polynomial expression. -/
def diagonalProfile {N : ℕ} (α : Fin N → ℝ) (s : Fin N) (x : ℝ) : ℝ :=
  -α s * ∏ j ∈ (Finset.univ : Finset (Fin N)).erase s, (1-α j*x)

/-- Every actual causal diagonal kernel is the product with its own factor omitted. -/
theorem diagonalKernel_erase (γ : ℕ → ℝ) {N s : ℕ} (hs : s<N) (x : ℝ) :
    diagonalKernel γ N s x = -γ s * ∏ j ∈ (Finset.range N).erase s, (1-γ j*x) := by
  have hp := chebyshev1.orderedProduct_update (fun j => 1-γ j*x) 1 hs
  rw [orderedProduct_eq_prod,Finset.prod_update_of_mem (Finset.mem_range.mpr hs),one_mul] at hp
  have he : (Finset.range N) \ {s}=(Finset.range N).erase s := by ext j; simp [and_comm]
  rw [he] at hp
  rw [diagonalKernel,chebyshev1.Stepsize.kernel_formula]
  rw [hp]
  ring

/-- The finite profile is exactly the old physical insertion kernel, including at roots. -/
theorem diagonalKernel_extend {N : ℕ} (α : Fin N → ℝ) (s : Fin N) (x : ℝ) :
    diagonalKernel (extend α) N s.val x=diagonalProfile α s x := by
  rw [diagonalKernel_erase (extend α) s.isLt,extend_fin,← prod_fin_erase]
  simp only [extend_fin,diagonalProfile]

/-- Omitting a factor commutes with every permutation of all finite steps. -/
theorem prod_erase_permute {M : Type*} [CommMonoid M] {N : ℕ}
    (f : Fin N → M) (e : Equiv.Perm (Fin N)) (s : Fin N) :
    (∏ j ∈ (Finset.univ : Finset (Fin N)).erase s, f (e j)) =
      ∏ j ∈ (Finset.univ : Finset (Fin N)).erase (e s), f j := by
  apply Finset.prod_bij (fun j _ => e j)
  · intro j hj
    simp only [Finset.mem_erase,Finset.mem_univ,and_true] at hj ⊢
    exact fun he => hj (e.injective he)
  · intro i _ j _ he
    exact e.injective he
  · intro j hj
    refine ⟨e.symm j,?_,e.apply_symm_apply j⟩
    simp only [Finset.mem_erase,Finset.mem_univ,and_true] at hj ⊢
    intro he
    exact hj (by simpa using congrArg e he)
  · intro _ _
    rfl

/-- Reordering root steps only reindexes the actual physical diagonal profiles. -/
theorem diagonalProfile_permute {N : ℕ} (α : Fin N → ℝ) (e : Equiv.Perm (Fin N))
    (s : Fin N) (x : ℝ) : diagonalProfile (α ∘ e) s x=diagonalProfile α (e s) x := by
  unfold diagonalProfile
  simp only [Function.comp_apply]
  rw [prod_erase_permute (fun j => 1-α j*x) e s]

/-- Multiplication by the omitted factor recovers the full actual terminal polynomial. -/
theorem diagonalProfile_mul_factor {N : ℕ} (α : Fin N → ℝ) (s : Fin N) (x : ℝ) :
    diagonalProfile α s x * (1-α s*x) = -α s * (terminal α).eval x := by
  unfold diagonalProfile terminal
  rw [eval_prod,mul_assoc,Finset.prod_erase_mul _ _ (Finset.mem_univ s)]
  simp only [eval_sub,eval_one,eval_mul,eval_C,eval_X]

/-- Away from its own root, the exact quotient formula equals the physical polynomial. -/
theorem diagonalProfile_quotient {N : ℕ} (α : Fin N → ℝ) (s : Fin N) (x : ℝ)
    (hα : α s≠0) (hx : (α s)⁻¹≠x) :
    diagonalProfile α s x=-(terminal α).eval x/((α s)⁻¹-x) := by
  have hp := diagonalProfile_mul_factor α s x
  have hd : (α s)⁻¹-x≠0 := sub_ne_zero.mpr hx
  apply (eq_div_iff hd).mpr
  have he : 1-α s*x=α s*((α s)⁻¹-x) := by field_simp
  rw [he] at hp
  exact (mul_left_cancel₀ hα (by nlinarith [hp]))

/-- The root quotient has the everywhere continuous physical polynomial as extension. -/
theorem continuous_diagonalProfile {N : ℕ} (α : Fin N → ℝ) (s : Fin N) :
    Continuous (diagonalProfile α s) := by
  unfold diagonalProfile
  fun_prop

end
end bezout.Channel.Roots
