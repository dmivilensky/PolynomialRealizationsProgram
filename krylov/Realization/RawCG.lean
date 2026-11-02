import krylov.Realization.RawPolynomialAction
import krylov.Reference.GalerkinUniqueness
import krylov.Reference.GradientMeasure
import krylov.Reference.Lanczos

/-!
Article: main_krylov, prop:dict(i), genuine supplied-matrix CG dictionary.
Use: derive true first-site CG nonstagnation, full active spectral support,
actual residual polynomials and the real measured Lanczos matrix directly
from an arbitrary supplied positive negative-offdiagonal tridiagonal matrix.
Source: genuine raw polynomial site actions, positive Galerkin uniqueness,
finite root counting and the existing actual CG/Lanczos definitions.
-/

namespace krylov.Realization
noncomputable section
open Matrix Polynomial chebyshev1 krylov.Reference
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The actual CG gradient for the supplied physical matrix and genuine first site is exactly the action of its constructed raw determinant residual.
Use: the raw-matrix CG identification is derived from the real algorithm, with no supplied reference coefficients or nonstagnation assumptions.
Article: main_krylov, prop:dict(i).
Proof: strong induction derives every true preceding nonstagnation from
the proved positive raw site action. The actual normalized polynomial and
true Krylov orthogonality then identify the real CG gradient by positive
Galerkin uniqueness. -/
theorem raw_cg_gradient (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s<N) :
    CG.gradient (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0)) s=
      CG.polynomialAction (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0))
        ((rawJacobi T).residual dictionaryInterval s) := by
  -- Genuine earlier CG nonstagnation is proved from actual positive raw site actions.
  induction s using Nat.strong_induction_on with
  | h s ih =>
    have hpre (i : ℕ) (hi : i<s) : CG.gradient (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0)) i≠0 := by
      rw [ih i hi (by omega)]
      exact raw_residual_action_ne T hT htri hneg i (by omega)
    exact (CG.normalized_galerkin_unique (cgOperator T) (cgOperator_positive T hT).1 (cgOperator_positive T hT).2
      _ s hpre ((rawJacobi T).residual dictionaryInterval s)
      (by rw [natDegree_eq_of_degree_eq_some (raw_residual_degree T hT htri hneg s hs.le)])
      (raw_residual_zero T hT htri hneg s hs.le)
      (raw_residual_orthogonal_krylov T hT htri hneg s hs)).symm

/-- The genuine first-site CG run of every supplied positive irreducible negative-offdiagonal tridiagonal matrix does not stagnate before its full dimension.
Use: all actual raw-matrix reference denominators and stored bases are discharged from the original matrix.
Article: main_krylov, prop:dict(i).
Proof: the proved actual CG/raw action identity is a genuine nonzero positive site multiple. -/
theorem raw_cg_nonstagnation (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s<N) :
    CG.gradient (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0)) s≠0 := by
  rw [raw_cg_gradient T hT htri hneg s hs]
  exact raw_residual_action_ne T hT htri hneg s hs

/-- The actual first-site CG spectral measure of the supplied physical matrix has exactly the full physical number of distinct active atoms.
Use: neither simple spectrum nor positive first-site spectral weights are assumed in the raw dictionary.
Article: main_krylov, prop:dict(i).
Proof: actual spectral cardinality is at most ambient dimension. Genuine
CG nonstagnation at every earlier time and the proved true stopping theorem
force the opposite inequality, including dimension zero. -/
theorem raw_referenceAtomCount (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) :
    referenceAtomCount T hT (WithLp.toLp 2 (JacobiData.site N 0))=N := by
  have hu : referenceAtomCount T hT (WithLp.toLp 2 (JacobiData.site N 0))≤N := by
    apply (Finset.card_image_le).trans
    exact (Finset.card_filter_le _ _).trans_eq (by simp)
  apply le_antisymm hu
  by_contra hn
  have hstop := cg_terminates T hT (WithLp.toLp 2 (JacobiData.site N 0))
  exact raw_cg_nonstagnation T hT htri hneg _ (by omega) hstop

/-- On a genuine full-active positive reference, no nonzero polynomial below the true physical dimension annihilates the real initial vector.
Use: actual measured spectral data determine all low-degree polynomial actions uniquely.
Article: main_krylov, prop:dict(i).
Proof: true full active support supplies distinct eigenvalues and nonzero
actual spectral coordinates. The genuine polynomial eigenvector action
forces a zero at every actual node; finite root counting gives the result. -/
theorem full_atoms_polynomialAction_eq_zero (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (g : EuclideanSpace ℝ (Fin N)) (hcount : referenceAtomCount T hT g=N)
    (p : ℝ[X]) (hp : p.degree<N) (hz : CG.polynomialAction (cgOperator T) g p=0) : p=0 := by
  -- The actual full support supplies distinct true roots and nonzero real spectral weights.
  by_cases hp0 : p=0
  · exact hp0
  obtain ⟨hi,hcoord⟩ := full_atoms_coordinates T hT g hcount
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hi
  · intro i
    have hv : cgOperator T (hT.1.eigenvectorBasis i)=hT.1.eigenvalues i • hT.1.eigenvectorBasis i := by
      ext j
      exact congrFun (hT.1.mulVec_eigenvectorBasis i) j
    have he := CG.polynomialAction_eigenvector (cgOperator T) (cgOperator_positive T hT).1
      g (hT.1.eigenvectorBasis i) (hT.1.eigenvalues i) hv p
    rw [hz,inner_zero_right] at he
    have hne : inner ℝ (hT.1.eigenvectorBasis i) g≠0 := by
      rw [gradient_spectral_coordinate T hT g i]
      exact mul_ne_zero (Real.sqrt_pos.mpr (hT.eigenvalues_pos i)).ne' (hcoord i)
    exact (mul_eq_zero.mp he.symm).resolve_right hne
  · simpa only [Fintype.card_fin] using (natDegree_lt_iff_degree_lt hp0).mpr hp

/-- True full-active positive operator actions determine normalized polynomials uniquely through the actual terminal degree.
Use: include the genuine degree-N CG residual in the raw spectral dictionary, rather than asserting false unrestricted polynomial uniqueness.
Article: main_krylov, prop:dict(i).
Proof: divide the actual equal-constant difference by X. Positive true
operator energy forces its lower-degree action zero, and the proved real
full-active polynomial root obstruction then kills the polynomial difference. -/
theorem full_atoms_normalized_action_injective (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (g : EuclideanSpace ℝ (Fin N)) (hcount : referenceAtomCount T hT g=N)
    (p r : ℝ[X]) (hp : p.natDegree≤N) (hr : r.natDegree≤N) (h0 : p.eval 0=r.eval 0)
    (he : CG.polynomialAction (cgOperator T) g p=CG.polynomialAction (cgOperator T) g r) : p=r := by
  -- Only the actual zero-constant difference is divided by X, preserving terminal-degree uniqueness.
  obtain ⟨q,hq,hd⟩ := normalized_difference hp hr h0
  let v := CG.polynomialAction (cgOperator T) g q
  have hact : cgOperator T v=0 := by
    have hx : CG.polynomialAction (cgOperator T) g (X*q)=cgOperator T v := by
      change aeval (cgOperator T) (X*q) g=cgOperator T (aeval (cgOperator T) q g)
      rw [map_mul,aeval_X,mul_apply_eq_comp]
    rw [← hx,← hq,map_sub,he,sub_self]
  have hv : v=0 := by
    by_contra hv
    have hpos := (cgOperator_positive T hT).2 v hv
    rw [hact,inner_zero_right] at hpos
    exact lt_irrefl 0 hpos
  have hqzero := full_atoms_polynomialAction_eq_zero T hT g hcount q (mem_degreeLT.mp hd) hv
  rw [hqzero,mul_zero] at hq
  exact sub_eq_zero.mp hq

/-- The actual computed CG residual polynomial for the supplied positive raw tridiagonal matrix is exactly its genuine constructed normalized leading determinant polynomial through the terminal degree.
Use: proves the source CG-polynomial identification at the actual spectral measure of the original supplied matrix.
Article: main_krylov, prop:dict(i).
Proof: actual nonstagnation proves true full active support. The raw and
real CG normalized polynomial actions coincide internally by genuine
Galerkin uniqueness and terminally by actual stopping and Cayley--Hamilton.
True normalized action injectivity identifies the polynomials themselves. -/
theorem raw_cg_residualPolynomial (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s≤N) :
    CG.residualPolynomial (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0)) s=
      (rawJacobi T).residual dictionaryInterval s := by
  -- The real full active count was derived from the original matrix, not supplied as reference data.
  apply full_atoms_normalized_action_injective T hT _ (raw_referenceAtomCount T hT htri hneg)
    _ _ ((CG.polynomial_degree (cgOperator T) _ s).1.trans hs)
    (by rw [natDegree_eq_of_degree_eq_some (raw_residual_degree T hT htri hneg s hs)]; exact hs)
    ((CG.residualPolynomial_zero (cgOperator T) _ s).trans (raw_residual_zero T hT htri hneg s hs).symm)
  rw [(CG.polynomialAction_pair (cgOperator T) _ s).1]
  by_cases hlt : s<N
  · exact raw_cg_gradient T hT htri hneg s hlt
  · have he : s=N := by omega
    subst s
    rw [raw_residual_terminal_action T hT htri hneg]
    simpa only [raw_referenceAtomCount T hT htri hneg] using cg_terminates T hT (WithLp.toLp 2 (JacobiData.site N 0))


/-- The actual normalized CG residuals of the original supplied physical matrix are exactly its genuine physical site vectors.
Use: the real negative-offdiagonal Lanczos orientation is derived, rather than chosen as an independent basis.
Article: main_krylov, prop:dict(i).
Proof: the genuine raw/CG action formula is a strictly positive multiple
of a true unit coordinate site, so actual normalization gives that site. -/
theorem raw_cg_residualUnit (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s<N) :
    CG.residualUnit (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0)) s=
      WithLp.toLp 2 (JacobiData.site N s) := by
  rw [CG.residualUnit,raw_cg_gradient T hT htri hneg s hs,raw_residual_polynomial_action T hT htri hneg s hs]
  change NormedSpace.normalize (_ • WithLp.toLp 2 (JacobiData.site N s))=_
  rw [NormedSpace.normalize_smul_of_pos (mul_pos
    (inv_pos.mpr (rawJacobi_admissible T hT htri hneg s hs.le)) (raw_linkProduct_pos T hneg s hs))]
  apply NormedSpace.normalize_eq_self_of_norm_eq_one
  rw [JacobiData.site_eq_single N s hs]
  simp

/-- Every actual measured CG Lanczos prefix of the supplied raw physical matrix is its genuine leading principal block.
Use: true measured pivots and frozen coefficients belong to the original supplied matrix itself.
Article: main_krylov, prop:dict(i).
Proof: genuine normalized CG residuals are the actual physical sites;
the real operator compression in those sites selects exactly the original entries. -/
theorem raw_lanczosMatrix_prefix (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (m : ℕ) (hm : m≤N) :
    CG.lanczosMatrix (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0)) m=rawBlock T 0 m (by omega) := by
  ext i j
  rw [CG.lanczosMatrix,raw_cg_residualUnit T hT htri hneg i.val (by omega),
    raw_cg_residualUnit T hT htri hneg j.val (by omega)]
  change inner ℝ (WithLp.toLp 2 (JacobiData.site N i.val))
    (Matrix.toEuclideanCLM (𝕜 := ℝ) T (WithLp.toLp 2 (JacobiData.site N j.val)))=_
  rw [Matrix.toEuclideanCLM_toLp,JacobiData.site_eq_single N i.val (by omega),
    JacobiData.site_eq_single N j.val (by omega)]
  simp [EuclideanSpace.inner_single_left,rawBlock]

/-- The actual full first-site CG Lanczos matrix is precisely the original supplied physical tridiagonal matrix.
Use: closes the supplied-matrix/measured-CG direction of the realization dictionary.
Article: main_krylov, prop:dict(i).
Proof: specialize the true measured-prefix identity to the actual full physical block. -/
theorem raw_lanczosMatrix (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) :
    CG.lanczosMatrix (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0)) N=T := by
  rw [raw_lanczosMatrix_prefix T hT htri hneg N le_rfl,rawBlock_full]


/-- The supplied positive irreducible tridiagonal matrix has genuinely distinct true eigenvalues and nonzero actual first-site coordinates at every true spectral atom.
Use: the source free spectral-weight fibre uses positive real first-site weights, proved from the original matrix.
Article: main_krylov, prop:dict(i).
Proof: actual full active support gives distinct nodes and nonzero
canonical coordinates; the real positive root eigenvalue converts each to
its nonzero true physical first-site coordinate. -/
theorem raw_spectral_coordinates (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) :
    Function.Injective hT.1.eigenvalues ∧ ∀ i,
      inner ℝ (hT.1.eigenvectorBasis i) (WithLp.toLp 2 (JacobiData.site N 0))≠0 := by
  obtain ⟨hi,hcoord⟩ := full_atoms_coordinates T hT _ (raw_referenceAtomCount T hT htri hneg)
  refine ⟨hi,?_⟩
  intro i
  rw [gradient_spectral_coordinate T hT]
  exact mul_ne_zero (Real.sqrt_pos.mpr (hT.eigenvalues_pos i)).ne' (hcoord i)

/-- The actual CG residual at the original supplied matrix spectral measure has the printed genuine leading physical determinant ratio, including the terminal and empty degrees.
Use: no desired CG/determinant identification is left as a premise in the source dictionary.
Article: main_krylov, prop:dict(i), r_s(λ).
Proof: the proved actual polynomial identity and genuine raw affine
normalization reduce directly to the real shifted/unshifted leading determinants. -/
theorem raw_cg_determinant_eval (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s≤N) (lam : ℝ) :
    (CG.residualPolynomial (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0)) s).eval lam=
      (rawBlock T 0 s (by omega)-lam • 1).det/(rawBlock T 0 s (by omega)).det := by
  rw [raw_cg_residualPolynomial T hT htri hneg s hs,JacobiData.residual_eval,dictionaryInterval_z,
    JacobiData.leading,raw_block_eval T hT.1.isSymm htri hneg 0 s (by omega) lam,
    raw_den_det T hT.1.isSymm htri hneg s hs]

end
end krylov.Realization
