import jacobi.Laguerre.Matrix
import jacobi.Finite.OrderedSpectrum
import Mathlib.Analysis.Matrix.PosDef

/-!
Article: jacobi, Proposition 6.1.
The exact Laguerre recurrence is encoded in the existing Jacobi type.
Its actual Cholesky factor gives positivity, and the general endpoint
cofactor theorem gives simplicity and a complete increasing enumeration.
No finite Laguerre zero geometry is assumed.
Use: roots uses the general irreducible finite spectral ordering, avoiding a separate orthogonal-polynomial zero theory for Laguerre.
-/
namespace jacobi.Laguerre
noncomputable section
open Polynomial Matrix Set jacobi.Counterexample jacobi.Finite
set_option backward.isDefEq.respectTransparency false

/-- The original finite Laguerre recurrence matrix encoded in the existing Jacobi type.
Use: roots uses the general irreducible finite spectral ordering, avoiding a separate orthogonal-polynomial zero theory for Laguerre.
Article: jacobi, Proposition 6.1.
-/
def chain (a:ℝ) (N:ℕ) : chebyshev2.Jacobi N :=
  fromMatrix ((data a).matrix 0 N)

/-- The finite Laguerre Jacobi encoding is exactly the original recurrence matrix.
Use: every actual spectral and characteristic statement in roots_zero_iff concerns the source matrix itself.
Article: jacobi, Proposition 6.1.
Proof: the original recurrence matrix is real symmetric and tridiagonal, and all actual adjacent entries are nonnegative square roots. -/
theorem chain_matrix (a:ℝ) (N:ℕ) : (chain a N).matrix=(data a).matrix 0 N := by
  -- The common encoding needs only symmetry, nonnegative adjacent entries and the original zero band.
  apply fromMatrix_eq _ ((data a).matrix_isHermitian 0 N)
  · intro i j hij
    rw [chebyshev1.JacobiData.matrix_apply,ite_eq_right (by
      intro he
      have hh:=congrArg Fin.val he
      omega),ite_eq_left hij]
    exact Real.sqrt_nonneg _
  · intro i j hij
    have hne:i≠j:=by intro he; subst j; omega
    have hu:¬i.val+1=j.val:=by omega
    have hl:¬j.val+1=i.val:=by omega
    simp only [chebyshev1.JacobiData.matrix_apply,hne,hu,hl,ite_false]

/-- The actual Laguerre matrix has strictly positive internal couplings throughout a>-1.
Use: roots is the complete simple ordered spectrum, with no extra irreducibility or distinctness premise.
Article: jacobi, Proposition 6.1.
Proof: its encoded coupling is the square of sqrt(i*(i+a)), which
is strictly positive at every actual positive interior index. -/
theorem chain_irreducible {a:ℝ} (ha:-1 < a) (N:ℕ) : (chain a N).Irreducible := by
  -- The finite coefficient encoding retains exactly the original positive interior entries.
  intro i hi hiN
  change 0 < (if h : 0 < i ∧ i < N then
    ((data a).matrix 0 N ⟨i-1,by omega⟩ ⟨i,h.2⟩)^2 else 0)
  rw [dite_eq_left ⟨hi,hiN⟩]
  have hne:(⟨i-1,by omega⟩:Fin N)≠⟨i,hiN⟩ := by
    intro he
    have hh:=congrArg Fin.val he
    dsimp only at hh
    omega
  have hu:i-1+1=i:=by omega
  rw [chebyshev1.JacobiData.matrix_apply,ite_eq_right hne,ite_eq_left hu]
  apply sq_pos_of_pos
  apply Real.sqrt_pos.mpr
  simp only [data,Nat.zero_add]
  have hiR : (1:ℝ) ≤ i := by exact_mod_cast hi
  apply mul_pos <;> linarith

/-- The actual positive Laguerre zeros in their original increasing order.
Use: the Laguerre Mehler--Heine and full l1 edge limits refer to this complete original zero list.
Article: jacobi, Proposition 6.1.
-/
def roots (a:ℝ) (ha:-1 < a) (N:ℕ) : Fin N ↪o ℝ :=
  increasingSpectrum (chain a N) (chain_irreducible ha N)

/-- A real number is an actual classical Laguerre zero exactly when it occurs in the original complete ordered finite list.
Use: the real zero supplied by Mehler--Heine is identified with a canonical finite source index.
Article: jacobi, Proposition 6.1.
Proof: the genuine signed rising-factorial normalization is nonzero.
The complete actual characteristic polynomial identity and finite
spectral theorem convert the original polynomial zero to its sorted index. -/
theorem roots_zero_iff {a:ℝ} (ha:-1 < a) (N:ℕ) (x:ℝ) :
    (polynomial a N).eval x=0 ↔ ∃i:Fin N,roots a ha N i=x := by
  -- Every root belongs to the original classical polynomial, not a newly defined characteristic surrogate.
  have hnorm:signedNormalization a N≠0 :=
    mul_ne_zero (pow_ne_zero N (by norm_num)) (denominator_pos ha N).ne'
  change (polynomial a N).eval x=0 ↔
    ∃i:Fin N,increasingSpectrum (chain a N) (chain_irreducible ha N) i=x
  rw [← increasingSpectrum_exhaustive,Matrix.mem_spectrum_iff_isRoot_charpoly,chain_matrix,
    matrix_eq_factor ha,characteristic_polynomial ha]
  simp only [Polynomial.IsRoot,eval_mul,eval_C,mul_eq_zero,hnorm,false_or]

/-- Every canonical Laguerre zero is a true zero of the original classical normalized polynomial.
Use: the ordered edge limit applies the compact zero-exclusion theorem to actual finite polynomial roots.
Article: jacobi, Proposition 6.1.
Proof: specialize the proved exhaustive original zero equivalence to the canonical index itself. -/
theorem roots_is_zero {a:ℝ} (ha:-1 < a) {N:ℕ} (i:Fin N) :
    (polynomial a N).eval (roots a ha N i)=0 :=
  (roots_zero_iff ha N _).mpr ⟨i,rfl⟩

/-- Every original Laguerre zero is strictly positive for every a>-1 and every finite dimension.
Use: reciprocal edge spectra and their exact total trace use genuine positive denominators, not totalized reciprocals.
Article: jacobi, Proposition 6.1.
Proof: the exact Cholesky swap preserves the complete original
spectrum. Its independently proved positive definiteness forces
every actual eigenvalue, hence every original ordered root, to be positive. -/
theorem roots_pos {a:ℝ} (ha:-1 < a) {N:ℕ} (i:Fin N) : 0 < roots a ha N i := by
  -- The positivity theorem is applied to the unchanged finite spectral value.
  have hm:=increasingSpectrum_mem (chain a N) (chain_irreducible ha N) i
  rw [chain_matrix,matrix_eq_factor ha] at hm
  have hs:roots a ha N i∈spectrum ℝ (swappedGram (laguerreDiagonal a) laguerreLower N) := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly,swapped_charpoly]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hm
  have hp:=swapped_posDef (N:=N) (laguerreDiagonal a) laguerreLower (by linarith : 0 < a+1)
    (fun j _=>laguerre_factor_drift ha j)
  rw [hp.isHermitian.spectrum_real_eq_range_eigenvalues] at hs
  obtain ⟨j,hj⟩:=hs
  exact hj ▸ hp.eigenvalues_pos j

end
end jacobi.Laguerre
