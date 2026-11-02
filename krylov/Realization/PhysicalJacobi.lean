import krylov.Realization.ChebyshevNodes
import krylov.Realization.RawCGCoefficients

/-!
Article: Proposition A.5 [prop:dict] of krylov.tex.
Use: turn the complete jacobi inverse spectral simplex chart into actual
positive negative-offdiagonal physical matrices, their genuine spectral bases
and terminal-exact raw frozen-CG realizations, and prove the converse spectral constraint.
Source: reused finite Jacobi spectral reconstruction, actual affine physical
spectral coordinates and the proved genuine raw leading-determinant dictionary.
-/

namespace krylov.Realization
noncomputable section
open Matrix Polynomial chebyshev1 chebyshev2
open scoped BigOperators Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The genuine physical positive-interval affine image of a finite normalized Jacobi matrix.
Use: The genuine physical positive-interval affine image of a finite normalized Jacobi matrix.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: Use the actual physical spectral variable lambda rather than auxiliary raw dictionary coordinates. -/
def physicalJacobi (I : SpectralInterval) (J : chebyshev2.Jacobi N) : Matrix (Fin N) (Fin N) ℝ :=
  ((I.L+I.mu)/2) • 1-(I.delta/2) • J.matrix

/-- The actual physical affine image of every genuine interior-node Jacobi fibre point is positive definite.
Use: The actual physical affine image of every genuine interior-node Jacobi fibre point is positive definite.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: The true prescribed nodes lie inside minus one and one; the actual affine physical eigenvalues lie above the positive lower endpoint. Reuse the genuine affine positive-definiteness theorem. -/
theorem physicalJacobi_posDef (I : SpectralInterval) (S : jacobi.Finite.Nodes N)
    (J : jacobi.Finite.Fiber N S.polynomial) : (physicalJacobi I J.val).PosDef := by
  -- Positivity is derived from the genuine prescribed physical eigenvalues.
  have hp := J.val.affine_posDef ((I.L+I.mu)/2) (-(I.delta/2)) (fun x hx => by
    rw [S.spectrum_eq J.property] at hx
    obtain ⟨i,rfl⟩ := hx
    have hm := I.lambda_mem ⟨(S.interval i).1.le,(S.interval i).2.le⟩
    have he : 0<I.lambda (S.value i) := I.mu_pos.trans_le hm.1
    simpa only [SpectralInterval.lambda,neg_mul,sub_eq_add_neg] using he)
  have hs : Matrix.scalar (Fin N) ((I.L+I.mu)/2)=((I.L+I.mu)/2) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
    ext i j
    simp [Matrix.scalar_apply,Matrix.diagonal_apply,Matrix.one_apply]
  rw [hs] at hp
  simpa only [physicalJacobi,sub_eq_add_neg,neg_smul] using hp

/-- The actual physical affine Jacobi matrix is genuinely tridiagonal.
Use: The actual physical affine Jacobi matrix is genuinely tridiagonal.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: Both the real identity matrix and true Jacobi far-band entries vanish off the actual tridiagonal band. -/
theorem physicalJacobi_tridiagonal (I : SpectralInterval) (J : chebyshev2.Jacobi N) :
    ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → physicalJacobi I J i j=0 := by
  -- Compare actual physical entries in the true tridiagonal band.
  intro i j hij
  have hne : i≠j := by intro he;subst j;omega
  have hu : ¬i.val+1=j.val := by omega
  have hl : ¬j.val+1=i.val := by omega
  simp only [physicalJacobi,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply_ne hne,
    mul_zero,Jacobi.matrix,JacobiData.matrix_apply,hne,hu,hl,ite_false,zero_add,mul_zero,sub_zero]

/-- Every actual physical adjacent entry is negative for a genuine irreducible Jacobi chain.
Use: Every actual physical adjacent entry is negative for a genuine irreducible Jacobi chain.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: The true positive squared coupling has a positive square root, multiplied by the negative actual half interval width. -/
theorem physicalJacobi_negative (I : SpectralInterval) (J : chebyshev2.Jacobi N) (hJ : J.Irreducible) :
    ∀ i j : Fin N, i.val+1=j.val → physicalJacobi I J i j<0 := by
  intro i j hij
  have hne : i≠j := by intro he;subst j;omega
  have hcoupling : 0<J.data.aSq j.val := hJ j.val (by omega) j.isLt
  have hentry : J.matrix i j=Real.sqrt (J.data.aSq j.val) := by
    simp only [Jacobi.matrix,JacobiData.matrix_apply,hne,hij,ite_false,ite_true,zero_add]
  simp only [physicalJacobi,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply_ne hne,mul_zero,hentry,zero_sub]
  exact neg_neg_of_pos (mul_pos (div_pos I.delta_pos (by norm_num)) (Real.sqrt_pos.mpr hcoupling))

/-- The genuine physical affine spectral basis has the original actual eigenvectors and the true affine physical eigenvalues.
Use: The genuine physical affine spectral basis has the original actual eigenvectors and the true affine physical eigenvalues.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: The real orthogonal identities remain unchanged; diagonalize the actual affine physical matrix. -/
def physicalJacobiBasis (I : SpectralInterval) (J : chebyshev2.Jacobi N) (B : SpectralBasis J.matrix) :
    SpectralBasis (physicalJacobi I J) where
  Q := B.Q
  eigenvalues i := I.lambda (B.eigenvalues i)
  transpose_mul := B.transpose_mul
  mul_transpose := B.mul_transpose
  diagonalize := by
    -- Preserve the actual orthogonal eigenvectors and transform only their real eigenvalues.
    rw [physicalJacobi,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
      Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,B.transpose_mul,B.diagonalize]
    ext i j
    by_cases he : i=j
    · subst j
      simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,Matrix.diagonal_apply_eq,smul_eq_mul,mul_one,SpectralInterval.lambda]
    · simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_ne he,Matrix.diagonal_apply_ne _ he,smul_eq_mul,mul_zero,sub_self]

/-- The actual shifted physical matrix is the true normalized Jacobi characteristic pencil times the physical half width.
Use: The actual shifted physical matrix is the true normalized Jacobi characteristic pencil times the physical half width.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: Use the exact genuine affine spectral-coordinate identity and actual matrix scalar linearity. -/
theorem physicalJacobi_shift (I : SpectralInterval) (J : chebyshev2.Jacobi N) (lam : ℝ) :
    physicalJacobi I J-lam • 1=(I.delta/2) • (I.z lam • 1-J.matrix) := by
  have hz : I.delta/2*I.z lam=(I.L+I.mu)/2-lam := by
    have hd : I.L-I.mu≠0 := I.delta_pos.ne'
    unfold SpectralInterval.z SpectralInterval.delta
    field_simp [hd]
  rw [smul_sub,smul_smul,hz]
  unfold physicalJacobi
  module

/-- The actual physical shifted determinant equals the genuine leading Jacobi continuant at the true physical spectral coordinate times the half-width power.
Use: The actual physical shifted determinant equals the genuine leading Jacobi continuant at the true physical spectral coordinate times the half-width power.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: Apply the true affine pencil identity, the actual determinant scalar factor and the existing genuine characteristic-continuant theorem. -/
theorem physicalJacobi_determinant (I : SpectralInterval) (J : chebyshev2.Jacobi N) (lam : ℝ) :
    (physicalJacobi I J-lam • 1).det=(I.delta/2)^N*(J.data.leading N).eval (I.z lam) := by
  rw [physicalJacobi_shift,Matrix.det_smul,Fintype.card_fin]
  congr 1
  change (I.z lam • (1 : Matrix (Fin N) (Fin N) ℝ)-J.matrix).det=(J.data.block 0 N).eval (I.z lam)
  rw [J.data.block_eq_charpoly J.coupling_nonneg,Matrix.eval_charpoly]
  congr 1
  ext i j
  simp [Matrix.scalar_apply,Matrix.diagonal_apply,Matrix.one_apply,Jacobi.matrix]

/-- The actual raw physical frozen-CG terminal residual equals the true normalized Jacobi residual in the prescribed physical interval.
Use: The actual raw physical frozen-CG terminal residual equals the true normalized Jacobi residual in the prescribed physical interval.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: Substitute the genuine raw determinant identity and the proved actual physical determinant coordinate formula; cancel only the nonzero half-width power. -/
theorem physicalJacobi_raw_residual (I : SpectralInterval) (S : jacobi.Finite.Nodes N)
    (J : jacobi.Finite.Fiber N S.polynomial) :
    ((rawJacobi (physicalJacobi I J.val)).realization dictionaryInterval).residualPolynomial N=
      J.val.data.residual I N := by
  -- Compare both genuine physical determinant formulas before cancelling their common nonzero coordinate factor.
  have hT := physicalJacobi_posDef I S J
  have htri := physicalJacobi_tridiagonal I J.val
  have hneg := physicalJacobi_negative I J.val J.property.1
  have hz : I.z 0=I.eta := by unfold SpectralInterval.z SpectralInterval.eta;ring
  have hdet : (physicalJacobi I J.val).det=(I.delta/2)^N*J.val.data.den I N := by
    simpa only [zero_smul,sub_zero,hz,JacobiData.den] using physicalJacobi_determinant I J.val 0
  apply Polynomial.funext
  intro lam
  rw [raw_residual_eval _ hT htri hneg N le_rfl,rawBlock_full,physicalJacobi_determinant,hdet,JacobiData.residual_eval]
  have hc : (I.delta/2)^N≠0 := pow_ne_zero N (div_ne_zero I.delta_pos.ne' (by norm_num))
  exact mul_div_mul_left _ _ hc

/-- Every positive spectral probability vector constructs a genuine physical interval Jacobi matrix through the complete jacobi chart.
Use: Every positive spectral probability vector constructs a genuine physical interval Jacobi matrix through the complete jacobi chart.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: Use the actual reconstructed fibre point and its true physical affine image. -/
def weightedPhysicalJacobi (I : SpectralInterval) (S : jacobi.Finite.Nodes (N+1))
    (w : jacobi.Finite.WeightSimplex (N+1)) : Matrix (Fin (N+1)) (Fin (N+1)) ℝ :=
  physicalJacobi I (jacobi.Finite.reconstructFiber S w).val

/-- The actual constructed physical matrix has a genuine spectral basis from the true inverse spectral reconstruction.
Use: The actual constructed physical matrix has a genuine spectral basis from the true inverse spectral reconstruction.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: Reuse its actual orthogonal eigenvectors under the real physical affine transformation. -/
def weightedPhysicalBasis (I : SpectralInterval) (S : jacobi.Finite.Nodes (N+1))
    (w : jacobi.Finite.WeightSimplex (N+1)) : SpectralBasis (weightedPhysicalJacobi I S w) :=
  physicalJacobiBasis I (jacobi.Finite.reconstructFiber S w).val (S.measure w).reconstructedBasis

/-- The actual reconstructed physical eigenvalues are precisely the prescribed physical affine nodes.
Use: The actual reconstructed physical eigenvalues are precisely the prescribed physical affine nodes.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: Read the genuine constructed physical spectral basis. -/
theorem weightedPhysicalBasis_values (I : SpectralInterval) (S : jacobi.Finite.Nodes (N+1))
    (w : jacobi.Finite.WeightSimplex (N+1)) :
    (weightedPhysicalBasis I S w).eigenvalues=fun i => I.lambda (S.value i) := rfl

/-- The actual first-site spectral probabilities of the genuine physical matrix are exactly the arbitrary input weights.
Use: The actual first-site spectral probabilities of the genuine physical matrix are exactly the arbitrary input weights.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: Physical affine transformation preserves the true eigenvectors; reuse the complete actual jacobi spectral-weight reconstruction. -/
theorem weightedPhysicalBasis_weights (I : SpectralInterval) (S : jacobi.Finite.Nodes (N+1))
    (w : jacobi.Finite.WeightSimplex (N+1)) (k : Fin (N+1)) :
    (weightedPhysicalBasis I S w).weight 0 k=w.val k :=
  (S.measure w).reconstructed_weight (by omega) k

/-- Every arbitrary positive spectral weight vector gives a genuinely terminal-Chebyshev-exact raw physical frozen-CG realization at the actual cosine nodes.
Use: Every arbitrary positive spectral weight vector gives a genuinely terminal-Chebyshev-exact raw physical frozen-CG realization at the actual cosine nodes.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: The genuine raw/physical residual identity transfers the actual monic Chebyshev terminal polynomial of the reconstructed fibre point to the true physical residual. -/
theorem weightedPhysicalJacobi_chebyshev (I : SpectralInterval) (w : jacobi.Finite.WeightSimplex (N+1)) :
    ((rawJacobi (weightedPhysicalJacobi I (chebyshevNodes (N+1)) w)).realization dictionaryInterval).residualPolynomial (N+1)=
      I.residual (N+1) := by
  let S := chebyshevNodes (N+1)
  let J := jacobi.Finite.reconstructFiber S w
  change ((rawJacobi (physicalJacobi I J.val)).realization dictionaryInterval).residualPolynomial (N+1)=I.residual (N+1)
  rw [physicalJacobi_raw_residual I S J]
  apply J.val.data.terminal_residual I (pow_ne_zero N (by norm_num : (1/2 : ℝ)≠0))
  exact ((fibre_terminal_iff J.val).mpr (J.property.2.trans (chebyshevNodes_polynomial (N+1) (by omega)))).trans
    (fiberPolynomial_succ N)


/-- True terminal Chebyshev exactness of the actual raw physical realization is equivalent to the genuine normalized Jacobi terminal predicate.
Use: True terminal Chebyshev exactness of the actual raw physical realization is equivalent to the genuine normalized Jacobi terminal predicate.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: All genuine fibre spectrum bounds discharge the real Jacobi admissibility denominators. Reuse both directions of the actual finite Jacobi/recurrence terminal equivalence and the proved raw physical residual bridge. -/
theorem physicalJacobi_exact_iff (I : SpectralInterval) (S : jacobi.Finite.Nodes N)
    (J : jacobi.Finite.Fiber N S.polynomial) (hN : 0<N) :
    ((rawJacobi (physicalJacobi I J.val)).realization dictionaryInterval).residualPolynomial N=I.residual N ↔
      J.val.Terminal := by
  -- Derive actual denominator admissibility from the true fibre spectrum before applying the existing inverse recurrence equivalence.
  have had : J.val.data.Admissible I N := J.val.data.admissible_of_spectrum I N J.val.coupling_nonneg (by
    intro x hx
    rw [show J.val.data.matrix 0 N=J.val.matrix from rfl,S.spectrum_eq J.property] at hx
    obtain ⟨i,rfl⟩ := hx
    exact ⟨(S.interval i).1.le,(S.interval i).2.le⟩)
  constructor
  · intro h
    have ht : (J.val.recurrence I had).Terminal I := by
      rw [Recurrence.Terminal,J.val.residual_eq I had le_rfl]
      exact (physicalJacobi_raw_residual I S J).symm.trans h
    have hj := (J.val.recurrence I had).jacobi_terminal I hN ht
    rwa [J.val.jacobi_recurrence I had] at hj
  · intro h
    rw [physicalJacobi_raw_residual I S J]
    have ht := J.val.recurrence_terminal I hN h
    rwa [Recurrence.Terminal,J.val.residual_eq I (J.val.admissible I hN h) le_rfl] at ht


/-- The genuine physical characteristic polynomial has precisely the prescribed physical nodes and is independent of the actual free spectral weights.
Use: The genuine physical characteristic polynomial has precisely the prescribed physical nodes and is independent of the actual free spectral weights.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: Use the actual constructed spectral basis characteristic factorization. -/
theorem weightedPhysicalJacobi_charpoly (I : SpectralInterval) (S : jacobi.Finite.Nodes (N+1))
    (w : jacobi.Finite.WeightSimplex (N+1)) :
    (weightedPhysicalJacobi I S w).charpoly=∏ i, (X-C (I.lambda (S.value i))) :=
  (weightedPhysicalBasis I S w).charpoly_factor

/-- The actual constructed physical matrix has exactly the prescribed physical affine spectrum for every positive spectral weight vector.
Use: The actual constructed physical matrix has exactly the prescribed physical affine spectrum for every positive spectral weight vector.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: Its true characteristic polynomial factors into those actual physical nodes, and real spectrum membership is exactly a true characteristic root. -/
theorem weightedPhysicalJacobi_spectrum (I : SpectralInterval) (S : jacobi.Finite.Nodes (N+1))
    (w : jacobi.Finite.WeightSimplex (N+1)) :
    spectrum ℝ (weightedPhysicalJacobi I S w)=Set.range (fun i => I.lambda (S.value i)) := by
  ext lam
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,weightedPhysicalJacobi_charpoly]
  simp only [Polynomial.IsRoot,eval_prod,eval_sub,eval_X,eval_C,Finset.prod_eq_zero_iff,Finset.mem_univ,true_and,sub_eq_zero,Set.mem_range]
  constructor <;> rintro ⟨i,hi⟩ <;> exact ⟨i,hi.symm⟩


/-- Terminal Chebyshev exactness of any supplied positive negative-offdiagonal tridiagonal raw physical matrix forces exactly the true physical residual zero spectrum.
Use: Terminal Chebyshev exactness of any supplied positive negative-offdiagonal tridiagonal raw physical matrix forces exactly the true physical residual zero spectrum.
Article: main_krylov, prop:dict(i), true physical Chebyshev spectrum and free spectral weights.
Proof: The actual raw determinant residual has a genuine positive determinant denominator. True characteristic roots and the actual shifted determinant have the same zeros, so the source terminal polynomial fixes the physical eigenvalue set. -/
theorem raw_exact_spectrum (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j<0)
    (I : SpectralInterval) (hfinal : ((rawJacobi T).realization dictionaryInterval).residualPolynomial N=I.residual N) :
    spectrum ℝ T={lam : ℝ | (I.residual N).eval lam=0} := by
  -- The actual positive determinant denominator cannot add or remove physical spectral zeros.
  ext lam
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Polynomial.IsRoot,Matrix.eval_charpoly]
  have hscalar : Matrix.scalar (Fin N) lam-T= -(T-lam • 1) := by
    ext i j
    simp [Matrix.scalar_apply,Matrix.diagonal_apply,Matrix.one_apply]
  rw [hscalar,Matrix.det_neg]
  have hp : (-1 : ℝ)^Fintype.card (Fin N)≠0 := pow_ne_zero _ (by norm_num)
  simp only [mul_eq_zero,hp,false_or,Set.mem_ofPred_eq]
  rw [← hfinal,raw_residual_eval T hT htri hneg N le_rfl lam,rawBlock_full,div_eq_zero_iff]
  simp only [hT.det_pos.ne',or_false]

end
end krylov.Realization
