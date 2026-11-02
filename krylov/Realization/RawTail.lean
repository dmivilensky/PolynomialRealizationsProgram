import krylov.Realization.InsertionPolynomials
import krylov.Realization.RawJacobi
import chebyshev1.Jacobi.Kernel

/-!
Article: main_krylov, prop:dict(i), actual leading/tail independent-injection polynomials.
Use: prove the printed raw physical determinant formula for the actual
independent-injection polynomial of the constructed Jacobi realization.
Source: the existing genuine Jacobi tail transfer of PasechnyukTakac26 and
the proved raw positive tridiagonal sign/affine coordinate bridge.
-/

namespace krylov.Realization
noncomputable section
open Matrix Polynomial chebyshev1
open scoped BigOperators
/-- The actual scalar query polynomial of a true two-term realization is its genuine prefix residual polynomial.
Use: identifies the source r_s with the actual polynomial queried by the fixed recurrence.
Article: main_krylov, prop:dict(i).
Proof: the actual two-term initial, query and output vectors select the same first memory coordinate. -/
theorem twoTerm_query_eval (S : TwoTerm) (s : ℕ) (lam : ℝ) :
    (queryPolynomial S.realization s).eval lam=(S.realization.residualPolynomial s).eval lam := by
  rw [queryPolynomial_eval,chebyshev1.Realization.residualPolynomial_eval]
  simp only [chebyshev1.Realization.scalarTransfer,chebyshev1.Realization.scalarContract,
    Matrix.mulVec,dotProduct,TwoTerm.realization,Fin.sum_univ_two]
  simp
/-- The actual independent-injection polynomial of a genuine admissible Jacobi realization is its true normalized trailing continuant.
Use: the source tail response follows from the real realization rather than an assumed injection formula.
Article: main_krylov, prop:dict(i).
Proof: the actual injection vector selects the genuine first tail column;
the existing real Jacobi tail transfer and actual gradient coefficient cancel
the intermediate positive leading normalization. -/
theorem jacobiInjection_eval (J : JacobiData) (I : SpectralInterval) (N s : ℕ) (hJ : J.Admissible I N)
    (hs : s<N) (lam : ℝ) :
    (injectionPolynomial (J.realization I) N s).eval lam=
      -(2/I.delta)*(J.den I s/J.den I N)*(J.block (s+1) (N-(s+1))).eval (I.z lam) := by
  -- Evaluate the actual injection readout before applying any normalized continuant identity.
  rw [injectionPolynomial_eval]
  have he : (J.realization I).readout ⬝ᵥ
      (orderedProduct (fun i=>(J.realization I).scalarStep (s+1+i) lam) (N-(s+1)) *ᵥ (J.realization I).g s)=
      orderedProduct (fun i=>(J.realization I).scalarStep (s+1+i) lam) (N-(s+1)) 0 0*(J.method I).gamma s := by
    simp [JacobiData.realization,TwoTerm.realization,dotProduct,Matrix.mulVec,Fin.sum_univ_two]
  rw [he,J.tail_fundamental I hJ (s+1) (by omega) (by omega) lam]
  dsimp only [JacobiData.method]
  field_simp [J.den_ne I hJ (show s+1≤N by omega),J.den_ne I hJ le_rfl]
/-- The genuine full contiguous raw principal block is the supplied physical matrix itself.
Use: the terminal injection denominator is precisely det T.
Article: main_krylov, prop:dict(i).
Proof: the true contiguous index embedding at offset zero is the identity. -/
theorem rawBlock_full {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) :
    rawBlock T 0 N (by omega)=T := by
  ext i j
  simp only [rawBlock,Matrix.submatrix_apply,Nat.zero_add,Fin.eta]

/-- The true fixed-memory query polynomial of the supplied positive negative-offdiagonal tridiagonal matrix is the printed genuine leading determinant ratio.
Use: the source r_s is tied both to the actual scalar query and to the original physical matrix.
Article: main_krylov, prop:dict(i), r_s(λ).
Proof: the true two-term query selects its actual prefix residual; the proved raw physical residual determinant identity applies. -/
theorem raw_query_eval {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s≤N) (lam : ℝ) :
    (queryPolynomial ((rawJacobi T).realization dictionaryInterval) s).eval lam=
      (rawBlock T 0 s (by omega)-lam • 1).det/(rawBlock T 0 s (by omega)).det := by
  rw [show (rawJacobi T).realization dictionaryInterval=((rawJacobi T).method dictionaryInterval).realization from rfl,
    twoTerm_query_eval]
  exact raw_residual_eval T hT htri hneg s hs lam

/-- The actual independent-injection response of the constructed raw physical Jacobi realization is the printed true leading-times-tail determinant ratio.
Use: the source R_s formula is proved for the actual supplied positive tridiagonal matrix, including empty leading and tail blocks.
Article: main_krylov, prop:dict(i), R_s(λ).
Proof: the real normalized Jacobi tail formula evaluates the actual injection
polynomial; the proved raw physical leading/tail determinant identities cancel
the auxiliary affine normalization and give the true terminal denominator det T. -/
theorem raw_injection_eval {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s<N) (lam : ℝ) :
    (injectionPolynomial ((rawJacobi T).realization dictionaryInterval) N s).eval lam=
      -(rawBlock T 0 s (by omega)).det*
        (rawBlock T (s+1) (N-(s+1)) (by omega)-lam • 1).det/T.det := by
  -- All determinant factors belong to the original physical T, with actual empty blocks allowed.
  rw [jacobiInjection_eval _ dictionaryInterval N s (rawJacobi_admissible T hT htri hneg) hs lam,
    show dictionaryInterval.delta=2 from by norm_num [dictionaryInterval,SpectralInterval.delta],
    div_self (by norm_num : (2 : ℝ)≠0),dictionaryInterval_z,
    raw_den_det T hT.1.isSymm htri hneg s hs.le,
    raw_den_det T hT.1.isSymm htri hneg N le_rfl,
    raw_block_eval T hT.1.isSymm htri hneg (s+1) (N-(s+1)) (by omega) lam,rawBlock_full]
  ring

/-- The genuine two-variable insertion kernel of the supplied positive
tridiagonal matrix is its printed leading-times-tail determinant ratio.
Use: both factors come from the actual fixed-memory query and injection,
with no independently assumed response polynomial.
Article: main_krylov, prop:dict(i) and s6:kernel.
Proof: multiply the proved actual query and injection formulas and cancel
the strictly positive genuine leading principal determinant. -/
theorem raw_kernel_eval {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s<N) (lam nu : ℝ) :
    ((rawJacobi T).realization dictionaryInterval).kernel N s lam nu=
      -(rawBlock T 0 s (by omega)-nu • 1).det*
        (rawBlock T (s+1) (N-(s+1)) (by omega)-lam • 1).det/T.det := by
  rw [fixed_kernel_polynomial_factorization,raw_query_eval T hT htri hneg s hs.le nu,
    raw_injection_eval T hT htri hneg s hs lam]
  have hd := (rawBlock_posDef T hT 0 s (by omega)).det_pos.ne'
  field_simp [hd,hT.det_pos.ne']

end
end krylov.Realization
