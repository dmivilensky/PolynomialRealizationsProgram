import chebyshev1.Jacobi.TerminalSpectrum
import chebyshev1.Jacobi.InverseUniqueness
import chebyshev1.Chebyshev.Polynomial
import chebyshev1.Chebyshev.Coordinates
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-! Both directions of terminal Chebyshev exactness, with monic normalization. -/
namespace chebyshev1.JacobiData
noncomputable section
open Polynomial Polynomial.Chebyshev
variable (J : JacobiData) (I : SpectralInterval)

/-- The Chebyshev polynomial normalized to be monic, including degree zero. -/
def monicChebyshev (N : ℕ) : ℝ[X] := C ((2:ℝ)^(N-1))⁻¹ * T ℝ N

theorem monicChebyshev_monic (N : ℕ) : (monicChebyshev N).Monic := by
  rw [Monic, monicChebyshev, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_T]
  simp

theorem terminal_residual_iff_monic {N : ℕ} (hsq : ∀ t, 0 ≤ J.aSq t)
    (h : J.Admissible I N) :
    J.residual I N = I.residual N ↔ J.leading N = monicChebyshev N := by
  constructor
  · intro he
    have ht : J.leading N = C (J.den I N / I.den N) * T ℝ N := by
      apply Polynomial.funext
      intro x
      have hx := congrArg (fun p : ℝ[X] => p.eval (I.lambda x)) he
      rw [J.residual_eval, I.residual_eval, I.z_lambda] at hx
      simp only [eval_mul, eval_C]
      field_simp [J.den_ne I h le_rfl, I.den_ne N] at hx ⊢
      nlinarith
    have hc := congrArg (fun p : ℝ[X] => p.coeff N) ht
    have htop : (T ℝ N).coeff N = (2:ℝ)^(N-1) := by
      simpa only [Polynomial.leadingCoeff, natDegree_T, Int.natAbs_natCast]
        using (leadingCoeff_T ℝ (N:ℤ))
    rw [show (J.leading N).coeff N = 1 from J.block_coeff_top hsq 0 N,
      coeff_C_mul, htop] at hc
    have hscale : J.den I N / I.den N = ((2:ℝ)^(N-1))⁻¹ := by
      rw [← one_div]
      apply (eq_div_iff (pow_ne_zero (N-1) (by norm_num : (2:ℝ)≠0))).mpr
      exact hc.symm
    simpa only [hscale, monicChebyshev] using ht
  · intro ht
    exact J.terminal_residual I (inv_ne_zero (pow_ne_zero _ (by norm_num))) ht

/-- Exact scalar execution on the physical interval is equivalent to the terminal monic polynomial. -/
theorem terminal_scalar_iff_monic {N : ℕ} (hsq : ∀ t, 0 ≤ J.aSq t)
    (h : J.Admissible I N) :
    (∀ lam ∈ Set.Icc I.mu I.L,
      (J.realization I).scalarTransfer N lam = (I.residual N).eval lam) ↔
        J.leading N = monicChebyshev N := by
  rw [← J.terminal_residual_iff_monic I hsq h]
  constructor
  · intro he
    apply I.polynomial_eq
    intro lam hlam
    rw [← J.scalar_exact I h N le_rfl lam]
    exact he lam hlam
  · intro he lam _
    rw [J.scalar_exact I h N le_rfl, he]

def chebyshevNode (N : ℕ) (k : Fin N) : ℝ :=
  Real.cos ((2*(k:ℝ)+1)*Real.pi/(2*(N:ℝ)))

theorem chebyshevNode_injective (N : ℕ) : Function.Injective (chebyshevNode N) := by
  have hi := (Finset.range N).nodup_map_iff_injOn.mp (roots_T_real_nodup N)
  intro i j hij
  apply Fin.ext
  exact hi (Finset.mem_range.mpr i.isLt) (Finset.mem_range.mpr j.isLt) hij

theorem monicChebyshev_node (N : ℕ) (k : Fin N) :
    (monicChebyshev N).eval (chebyshevNode N k) = 0 := by
  have ht : IsRoot (T ℝ N) (chebyshevNode N k) := by
    rw [← mem_roots (T_ne_zero ℝ N), roots_T_real]
    simp only [Finset.mem_val, Finset.mem_image, Finset.mem_range]
    exact ⟨k.val,k.isLt,rfl⟩
  change (T ℝ N).eval (chebyshevNode N k)=0 at ht
  simp only [monicChebyshev, eval_mul, eval_C, ht, mul_zero]

/-- Prescribing the Chebyshev node set is equivalent to prescribing the monic terminal polynomial. -/
theorem terminal_monic_iff_spectrum {N : ℕ} (hsq : ∀ t, 0 ≤ J.aSq t) :
    J.leading N = monicChebyshev N ↔
      spectrum ℝ (J.matrix 0 N) = Set.range (chebyshevNode N) := by
  constructor
  · intro ht
    ext x
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, ← J.block_eq_charpoly hsq,
      ← leading, ht]
    simp only [monicChebyshev, IsRoot, eval_mul, eval_C, mul_eq_zero,
      inv_ne_zero (pow_ne_zero (N-1) (by norm_num : (2:ℝ)≠0)), false_or]
    rw [← IsRoot, ← mem_roots (T_ne_zero ℝ N), roots_T_real]
    simp only [Finset.mem_val, Finset.mem_image, Finset.mem_range, Set.mem_range]
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨⟨k,hk⟩,rfl⟩
    · rintro ⟨k,rfl⟩
      exact ⟨k.val,k.isLt,rfl⟩
  · intro hs
    by_cases hn : N=0
    · subst N
      simp [monicChebyshev]
    apply sub_eq_zero.mp
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (chebyshevNode_injective N)
    · intro k
      have hk : chebyshevNode N k ∈ spectrum ℝ (J.matrix 0 N) := hs ▸ ⟨k,rfl⟩
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly, ← J.block_eq_charpoly hsq,
        ← leading] at hk
      change (J.leading N).eval (chebyshevNode N k)=0 at hk
      simp only [eval_sub, hk, monicChebyshev_node, sub_self]
    · have hd : (monicChebyshev N).natDegree = N := by
        rw [monicChebyshev, natDegree_C_mul
          (inv_ne_zero (pow_ne_zero _ (by norm_num : (2:ℝ)≠0))), natDegree_T]
        exact Int.natAbs_natCast N
      simpa only [Fintype.card_fin, leading] using
        (IsMonicOfDegree.natDegree_sub_lt hn
          ⟨J.block_natDegree hsq 0 N,J.block_monic hsq 0 N⟩
          ⟨hd,monicChebyshev_monic N⟩)

theorem terminal_scalar_iff_spectrum {N : ℕ} (hsq : ∀ t, 0 ≤ J.aSq t)
    (h : J.Admissible I N) :
    (∀ lam ∈ Set.Icc I.mu I.L,
      (J.realization I).scalarTransfer N lam = (I.residual N).eval lam) ↔
        spectrum ℝ (J.matrix 0 N) = Set.range (chebyshevNode N) :=
  (J.terminal_scalar_iff_monic I hsq h).trans (J.terminal_monic_iff_spectrum hsq)

end
end chebyshev1.JacobiData
