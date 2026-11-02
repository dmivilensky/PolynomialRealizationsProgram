import krylov.Strings.DiscreteIdentification
import krylov.LinearAlgebra.JacobiStrictPrefix
import jacobi.Finite.PolynomialRecurrence
import Mathlib.Analysis.RCLike.Lemmas

/-!
Article: `main_krylov`, `apC:lem:stieltjes(b)`.
The existing canonical reconstruction supplies the genuine Jacobi matrix
of arbitrary positive finite probability data. Nonnegative nodes make
this same matrix positive semidefinite; irreducibility makes each proper
prefix strictly positive. Hence the canonical zero-energy polynomial
values have the strict alternating signs needed for positive string data.
-/

namespace krylov.Strings
noncomputable section
open Matrix Polynomial chebyshev1 chebyshev2 jacobi.Finite
open scoped BigOperators Matrix.Norms.L2Operator

namespace DiscreteInverse
variable {N : ℕ} (M : DiscreteMeasure (N+1))

/-- The true canonical Jacobi reconstruction is positive semidefinite when
all prescribed physical spectral nodes are nonnegative. -/
theorem reconstructed_posSemidef (hnode : ∀ i, 0≤M.node i) : M.reconstructed.matrix.PosSemidef := by
  rw [← krylov.LinearAlgebra.coordinates_posSemidef_iff M.reconstructedBasis]
  change (M.reconstructedBasis.Qᵀ*M.reconstructed.matrix*M.reconstructedBasis.Q).PosSemidef
  rw [M.reconstructedBasis.diagonalize]
  exact Matrix.posSemidef_diagonal_iff.mpr hnode

/-- Every actual proper leading prefix of the reconstructed Jacobi matrix
is positive definite, including prefixes ending before a zero support node. -/
theorem reconstructed_prefix_posDef (hnode : ∀ i, 0≤M.node i) (k : ℕ) (hk : k≤N) :
    (M.reconstructed.data.matrix 0 k).PosDef := by
  have hfull := krylov.LinearAlgebra.jacobi_strict_prefix M.reconstructed.matrix
    (reconstructed_posSemidef M hnode)
    (fun i j h ↦ by
      rw [M.reconstructed_matrix]
      exact M.multiplication_tridiagonal i j h)
    (fun i j h ↦ by
      rw [M.reconstructed_matrix, M.multiplication_adjacent i j h]
      exact (div_pos (M.orthogonalPolynomial_degree i).2
        (M.orthogonalPolynomial_degree j).2).ne')
  let e : Fin k → Fin N := fun i ↦ ⟨i.val, by omega⟩
  have he : Function.Injective e := by
    intro i j h
    apply Fin.ext
    simpa only [e] using congrArg Fin.val h
  have hsub := hfull.submatrix he
  convert hsub using 1
  ext i j
  simp only [Jacobi.matrix, JacobiData.matrix_apply, Matrix.submatrix_apply]
  simp only [Fin.ext_iff, e, Fin.val_castSucc]

/-- Genuine canonical polynomial values at zero, with their physical sign. -/
def zeroValue (k : ℕ) : ℝ :=
  if hk : k<N+1 then (-1 : ℝ)^k*(M.orthogonalPolynomial ⟨k,hk⟩).eval 0 else 1

/-- Every physical canonical zero-energy value is strictly positive after
the genuine alternating sign; this discharges all inverse-string denominators. -/
theorem zeroValue_pos (hnode : ∀ i, 0≤M.node i) (k : ℕ) : 0<zeroValue M k := by
  by_cases hk : k<N+1
  · rw [zeroValue, dite_eq_left hk, ← normalizedLeading_eq_orthogonalPolynomial]
    have hd := (reconstructed_prefix_posDef M hnode k (by omega)).det_pos
    have hchar : (M.reconstructed.data.leading k).eval 0 =
        (-1 : ℝ)^k*(M.reconstructed.data.matrix 0 k).det := by
      rw [JacobiData.leading,
        M.reconstructed.data.block_eq_charpoly M.reconstructed.coupling_nonneg, Matrix.eval_charpoly]
      simp only [map_zero, zero_sub, Matrix.det_neg, Fintype.card_fin]
    rw [normalizedLeading, eval_mul, eval_C, hchar]
    have hs := alternating_sq k
    have hp := linkProduct_pos M.reconstructed_irreducible hk
    calc
      _ = ((-1 : ℝ)^k)^2 * (M.reconstructed.data.linkProduct k)⁻¹ *
          (M.reconstructed.data.matrix 0 k).det := by ring
      _ > 0 := by rw [hs, one_mul]; exact mul_pos (inv_pos.mpr hp) hd
  · simp only [zeroValue, dite_eq_right hk, zero_lt_one]

/-- The actual first canonical polynomial gives the normalized unit origin. -/
theorem zeroValue_zero : zeroValue M 0=1 := by
  simp only [zeroValue, Nat.succ_pos, dite_eq_left, pow_zero, one_mul]
  rw [krylov.Reference.orthogonalPolynomial_first, eval_one]

/-- Real specialization of the already proved actual normalized Jacobi
three-term recurrence, retaining its degree-zero boundary convention. -/
theorem normalizedLeading_recurrence_real {n : ℕ} (J : Jacobi n) (hJ : J.Irreducible)
    (z : ℝ) (k : ℕ) (hk : k+1<n) :
    Real.sqrt (J.data.aSq (k+1))*(normalizedLeading J (k+1)).eval z+
      (if k=0 then 0 else Real.sqrt (J.data.aSq k)*(normalizedLeading J (k-1)).eval z)+
      J.data.b k*(normalizedLeading J k).eval z=z*(normalizedLeading J k).eval z := by
  have h := normalizedLeading_recurrence J hJ (z : ℂ) k hk
  have hc (P : ℝ[X]) : Polynomial.aeval (z : ℂ) P=((P.eval z : ℝ) : ℂ) :=
    (Polynomial.ofReal_eval (K := ℂ) P z).symm
  simp_rw [hc] at h
  by_cases hk0 : k=0
  · simp only [ite_eq_left hk0] at h ⊢
    exact_mod_cast h
  · simp only [ite_eq_right hk0] at h ⊢
    exact_mod_cast h

/-- The actual first off-diagonal Jacobi coupling in natural-number coordinates. -/
def coupling (k : ℕ) : ℝ := Real.sqrt (M.reconstructed.data.aSq (k+1))

/-- Every used canonical Jacobi coupling is strictly positive. -/
theorem coupling_pos (k : ℕ) (hk : k<N) : 0<coupling M k :=
  Real.sqrt_pos.mpr (M.reconstructed_irreducible (k+1) (by omega) (by omega))

/-- The actual zero-energy positive values satisfy the physical harmonic
balance at every nonterminal site. -/
theorem zeroValue_balance (k : ℕ) (hk : k<N) :
    M.reconstructed.data.b k*zeroValue M k=
      coupling M k*zeroValue M (k+1)+
        (if k=0 then 0 else coupling M (k-1)*zeroValue M (k-1)) := by
  have hr := normalizedLeading_recurrence_real M.reconstructed M.reconstructed_irreducible 0 k (by omega)
  have hnorm (j : ℕ) (hj : j<N+1) :
      (normalizedLeading M.reconstructed j).eval 0=
        (-1 : ℝ)^j*zeroValue M j := by
    rw [normalizedLeading_eq_orthogonalPolynomial M ⟨j,hj⟩, zeroValue, dite_eq_left hj]
    have hs := alternating_sq j
    calc
      _ = ((-1 : ℝ)^j)^2*(M.orthogonalPolynomial ⟨j,hj⟩).eval 0 := by rw [hs, one_mul]
      _ = _ := by ring
  rw [hnorm k (by omega), hnorm (k+1) (by omega), zero_mul] at hr
  by_cases hk0 : k=0
  · subst k
    simp only [Nat.zero_add, pow_zero, pow_one, one_mul, ite_true, add_zero, coupling] at hr ⊢
    linarith
  · rw [ite_eq_right hk0, hnorm (k-1) (by omega)] at hr
    have he : k-1+1=k := by omega
    have hs' : (-1 : ℝ)^(k-1)=-(-1 : ℝ)^k := by
      have ht : (-1 : ℝ)^k=(-1 : ℝ)^(k-1)*(-1) := by
        conv_lhs => rw [← he]
        exact pow_succ _ _
      linear_combination ht
    rw [pow_succ, hs'] at hr
    simp only [coupling, he, ite_eq_right hk0]
    apply mul_left_cancel₀ (pow_ne_zero k (by norm_num : (-1 : ℝ)≠0))
    linear_combination hr

end DiscreteInverse
end
end krylov.Strings
