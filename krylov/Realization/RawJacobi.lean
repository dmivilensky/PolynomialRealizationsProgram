import chebyshev1.Jacobi.Determinant
import chebyshev1.Jacobi.Exactness
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
Article: main_krylov, prop:dict(i), raw positive tridiagonal determinant coordinates.
Use: construct the existing normalized Jacobi realization from an arbitrary
actual positive tridiagonal matrix with negative adjacent entries, without
assuming a measured reference matrix or leading/tail determinant formula.
Source: the proved Jacobi characteristic-polynomial recurrence of PasechnyukTakac26;
positive principal submatrices reuse mathlib Matrix.PosDef.submatrix.
-/

namespace krylov.Realization
noncomputable section
open Matrix Polynomial chebyshev1
variable {N : ℕ}
/-- The actual normalized Jacobi coefficients constructed from a real raw negative-offdiagonal tridiagonal matrix.
Use: The sign/affine coordinate change is J=2I−T, so existing Jacobi machinery applies to the actual source matrix.
Article: main_krylov, prop:dict(i). -/
def rawJacobi (T : Matrix (Fin N) (Fin N) ℝ) : JacobiData where
  b s := if hs : s < N then 2-T ⟨s,hs⟩ ⟨s,hs⟩ else 0
  aSq s := if hs : 0 < s ∧ s < N then
    (T ⟨s-1,by omega⟩ ⟨s,hs.2⟩)^2 else 0
/-- The actual contiguous principal block of the supplied raw physical matrix, including empty blocks.
Use: Leading and tail determinants refer to the genuine source matrix entries.
Article: main_krylov, prop:dict(i). -/
def rawBlock (T : Matrix (Fin N) (Fin N) ℝ) (a m : ℕ) (h : a+m ≤ N) : Matrix (Fin m) (Fin m) ℝ :=
  T.submatrix (fun i=>⟨a+i.val,by omega⟩) (fun i=>⟨a+i.val,by omega⟩)
/-- The genuinely constructed squared Jacobi couplings are nonnegative at every index.
Use: Discharge the real Jacobi characteristic-polynomial recurrence premise.
Article: main_krylov, prop:dict(i).
Proof: Every actual nonzero branch is a real square; the extension branch is zero. -/
theorem rawJacobi_aSq_nonneg (T : Matrix (Fin N) (Fin N) ℝ) : ∀ s, 0 ≤ (rawJacobi T).aSq s := by
  intro s
  dsimp only [rawJacobi]
  split  <;> positivity
/-- Every actual contiguous principal block of the supplied positive matrix is positive definite.
Use: All leading determinant denominators are genuinely positive, including the empty block.
Article: main_krylov, prop:dict(i).
Proof: The actual contiguous index map is injective; apply the standard positive principal-submatrix theorem. -/
theorem rawBlock_posDef (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef) (a m : ℕ) (h : a+m ≤ N) :
    (rawBlock T a m h).PosDef := by
  apply hT.submatrix
  intro i j hij
  apply Fin.ext
  have he := congrArg Fin.val hij
  dsimp only at he
  omega
/-- Every true normalized Jacobi block equals 2I minus the actual corresponding raw physical principal block.
Use: All determinant and tail formulas are tied to the original supplied matrix.
Article: main_krylov, prop:dict(i).
Proof: Compare actual entries: diagonal affine shifts agree; negative true adjacent entries determine the positive square-root coupling signs, real symmetry handles the lower neighbor, and both far entries vanish. -/
theorem rawJacobi_matrix (T : Matrix (Fin N) (Fin N) ℝ) (hsym : T.IsSymm)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0)
    (a m : ℕ) (h : a+m ≤ N) :
    (rawJacobi T).matrix a m=(2 : ℝ) • 1-rawBlock T a m h := by
  -- The actual diagonal, two neighboring entries and vanishing far band are checked in the source matrix coordinates.
  let e : Fin m → Fin N := fun i=>⟨a+i.val,by omega⟩
  ext i j
  rw [JacobiData.matrix_apply]
  change (if i=j then (rawJacobi T).b (a+i.val)
    else if i.val+1=j.val then Real.sqrt ((rawJacobi T).aSq (a+j.val))
    else if j.val+1=i.val then Real.sqrt ((rawJacobi T).aSq (a+i.val)) else 0)=
      2*(if i=j then 1 else 0)-T (e i) (e j)
  by_cases hij : i=j
  · subst j
    simp only [ite_true,rawJacobi,dite_eq_left (show a+i.val < N by omega),mul_one]
    rfl
  simp only [hij,ite_false,mul_zero,zero_sub]
  by_cases hu : i.val+1=j.val
  · rw [ite_eq_left hu]
    have hp : 0 < a+j.val ∧ a+j.val < N := by omega
    simp only [rawJacobi,dite_eq_left hp]
    have he : (⟨a+j.val-1,by omega⟩ : Fin N)=e i := Fin.ext (by dsimp only [e]; omega)
    rw [he,Real.sqrt_sq_eq_abs,abs_of_neg (hneg (e i) (e j) (by dsimp only [e]; omega))]
  · rw [ite_eq_right hu]
    by_cases hl : j.val+1=i.val
    · rw [ite_eq_left hl]
      have hp : 0 < a+i.val ∧ a+i.val < N := by omega
      simp only [rawJacobi,dite_eq_left hp]
      have he : (⟨a+i.val-1,by omega⟩ : Fin N)=e j := Fin.ext (by dsimp only [e]; omega)
      rw [he,Real.sqrt_sq_eq_abs,abs_of_neg (hneg (e j) (e i) (by dsimp only [e]; omega))]
      exact congrArg Neg.neg (congrFun (congrFun hsym.eq (e i)) (e j))
    · rw [ite_eq_right hl,htri (e i) (e j) (by dsimp only [e]; have hi := i.isLt; have hj := j.isLt; omega),neg_zero]
/-- An auxiliary affine coordinate normalization with z(λ)=2−λ.
Use: This only fixes coordinates for reusing the older Jacobi construction; it imposes no spectral bounds [1,3] on the supplied physical matrix.
Article: main_krylov, prop:dict(i). -/
def dictionaryInterval : SpectralInterval := ⟨1,3,by norm_num,by norm_num⟩
/-- Every constructed Jacobi continuant evaluates to the genuine shifted determinant of the corresponding raw physical block.
Use: The leading/tail determinant dictionary holds for the actual supplied matrix and every real spectral argument.
Article: main_krylov, prop:dict(i).
Proof: Reuse the existing exact Jacobi characteristic-polynomial identity and evaluate it at 2−λ; the actual block bridge cancels the affine shift. -/
theorem raw_block_eval (T : Matrix (Fin N) (Fin N) ℝ) (hsym : T.IsSymm)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0)
    (a m : ℕ) (h : a+m ≤ N) (lam : ℝ) :
    ((rawJacobi T).block a m).eval (2-lam)=(rawBlock T a m h-lam • 1).det := by
  rw [JacobiData.block_eq_charpoly _ (rawJacobi_aSq_nonneg T),Matrix.eval_charpoly,
    rawJacobi_matrix T hsym htri hneg a m h]
  congr 1
  have hs : Matrix.scalar (Fin m) (2-lam)=((2-lam) : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ) :=
    (Matrix.smul_one_eq_diagonal (2-lam)).symm
  rw [hs]
  module
/-- The auxiliary Jacobi coordinate of zero is exactly two.
Use: The genuine physical leading determinants normalize the reused Jacobi residuals.
Article: main_krylov, prop:dict(i).
Proof: Evaluate the fixed affine normalization. -/
theorem dictionaryInterval_eta : dictionaryInterval.eta=2 := by
  norm_num [dictionaryInterval,SpectralInterval.eta,SpectralInterval.delta]
/-- The auxiliary spectral coordinate is exactly 2−λ.
Use: No spectral scale factors remain in the raw physical determinant formulas.
Article: main_krylov, prop:dict(i).
Proof: Evaluate and simplify the actual auxiliary affine coordinate. -/
theorem dictionaryInterval_z (lam : ℝ) : dictionaryInterval.z lam=2-lam := by
  dsimp [dictionaryInterval,SpectralInterval.z,SpectralInterval.delta]
  ring

/-- The actual Jacobi normalization denominator equals the genuine unshifted raw leading-block determinant.
Use: Every reused normalized coefficient has precisely its printed physical determinant denominator.
Article: main_krylov, prop:dict(i).
Proof: Evaluate the proved real shifted block determinant at zero. -/
theorem raw_den_det (T : Matrix (Fin N) (Fin N) ℝ) (hsym : T.IsSymm)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (m : ℕ) (hm : m ≤ N) :
    (rawJacobi T).den dictionaryInterval m=(rawBlock T 0 m (by omega)).det := by
  rw [JacobiData.den,JacobiData.leading,dictionaryInterval_eta]
  simpa only [sub_zero,zero_smul] using raw_block_eval T hsym htri hneg 0 m (by omega) 0

/-- Every supplied positive negative-offdiagonal tridiagonal matrix constructs a genuinely admissible Jacobi realization through its full dimension.
Use: All actual finite recurrence coefficients and injection tails have positive real denominators.
Article: main_krylov, prop:dict(i).
Proof: True principal-block positivity makes every actual leading determinant positive; substitute the proved physical normalization identity. -/
theorem rawJacobi_admissible (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) :
    (rawJacobi T).Admissible dictionaryInterval N := by
  intro m hm
  rw [raw_den_det T hT.1.isSymm htri hneg m hm]
  exact (rawBlock_posDef T hT 0 m (by omega)).det_pos

/-- The true constructed fixed-realization residual is the printed ratio of actual shifted and unshifted raw leading determinants.
Use: The source determinant dictionary is proved for a genuine supplied positive tridiagonal matrix rather than assumed from CG data.
Article: main_krylov, prop:dict(i).
Proof: Reuse the existing actual Jacobi realization exactness and substitute both proved raw physical determinant bridges. -/
theorem raw_residual_eval (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (m : ℕ) (hm : m ≤ N) (lam : ℝ) :
    (((rawJacobi T).realization dictionaryInterval).residualPolynomial m).eval lam=
      (rawBlock T 0 m (by omega)-lam • 1).det/(rawBlock T 0 m (by omega)).det := by
  rw [(rawJacobi T).residualPolynomial_eq dictionaryInterval (rawJacobi_admissible T hT htri hneg) m hm,
    (rawJacobi T).residual_eval dictionaryInterval m lam,dictionaryInterval_z,JacobiData.leading,
    raw_block_eval T hT.1.isSymm htri hneg 0 m (by omega) lam,
    raw_den_det T hT.1.isSymm htri hneg m hm]

end
end krylov.Realization
