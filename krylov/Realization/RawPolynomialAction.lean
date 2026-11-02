import krylov.Realization.RawTail
import chebyshev1.Jacobi.InverseUniqueness
import chebyshev1.Jacobi.Orthogonality
import krylov.Reference.PolynomialAction
import krylov.Reference.CanonicalSteps

/-!
Article: main_krylov, prop:dict(i), genuine raw tridiagonal polynomial actions.
Use: identify actual normalized physical determinant polynomials with true
site vectors and Krylov orthogonality before identifying the measured CG run.
Source: reuse the proved Jacobi site-polynomial action of PasechnyukTakac26,
standard Cayley--Hamilton and the existing degree-graded polynomial Krylov span.
-/

namespace krylov.Realization
noncomputable section
open Matrix Polynomial chebyshev1 krylov.Reference
open scoped BigOperators
variable {N : ℕ}

/-- The actual raw matrix evaluates the reused affine spectral coordinate to its genuine constructed Jacobi matrix.
Use: transfer real operator polynomials without any assumed eigenvalue or spectral-measure identification.
Article: main_krylov, prop:dict(i).
Proof: evaluate the actual affine polynomial and use the proved real raw
matrix sign/normalization bridge; the true full physical block is the matrix itself. -/
theorem raw_affine_aeval (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) :
    aeval T (C dictionaryInterval.eta-C (2/dictionaryInterval.delta)*X)=(rawJacobi T).matrix 0 N := by
  rw [map_sub,map_mul,aeval_C,aeval_C,aeval_X,Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one,dictionaryInterval_eta]
  norm_num only [dictionaryInterval,SpectralInterval.delta]
  rw [one_smul,Matrix.one_mul,rawJacobi_matrix T hT.1.isSymm htri hneg 0 N (by omega),rawBlock_full]

/-- The genuine raw normalized residual polynomial sends the actual first physical site to its true scaled degree site.
Use: establish actual orthogonality and nonstagnation from the original physical matrix, before making any CG identification.
Article: main_krylov, prop:dict(i).
Proof: the real affine operator coordinate converts the actual residual
to the existing Jacobi leading-polynomial action; use its proved genuine site identity. -/
theorem raw_residual_matrix_site (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s<N) :
    aeval T ((rawJacobi T).residual dictionaryInterval s) *ᵥ JacobiData.site N 0=
      ((rawJacobi T).den dictionaryInterval s)⁻¹ •
        ((rawJacobi T).linkProduct s • JacobiData.site N s) := by
  rw [JacobiData.residual,map_mul,aeval_comp,raw_affine_aeval T hT htri hneg,aeval_C,
    Algebra.algebraMap_eq_smul_one,Matrix.smul_mul,Matrix.one_mul,Matrix.smul_mulVec,
    (rawJacobi T).leading_aeval_site N s (by omega) hs (rawJacobi_aSq_nonneg T)]

/-- Every genuine internal raw Jacobi squared coupling is strictly positive.
Use: no actual site-polynomial coefficient vanishes before the full physical dimension.
Article: main_krylov, prop:dict(i).
Proof: the actual coupling is the square of a supplied strictly negative true adjacent physical entry. -/
theorem rawCoupling_pos (T : Matrix (Fin N) (Fin N) ℝ)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : 0 < s ∧ s<N) :
    0 < (rawJacobi T).aSq s := by
  simp only [rawJacobi,dite_eq_left hs]
  exact sq_pos_of_neg (hneg ⟨s-1,by omega⟩ ⟨s,hs.2⟩ (by dsimp only; omega))

/-- Every actual used raw Jacobi link product is positive, including the empty product.
Use: true polynomial-site coefficients are nonzero at every genuine internal degree.
Article: main_krylov, prop:dict(i).
Proof: each actual internal coupling square root is positive; apply finite product positivity. -/
theorem raw_linkProduct_pos (T : Matrix (Fin N) (Fin N) ℝ)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s<N) :
    0 < (rawJacobi T).linkProduct s := by
  apply Finset.prod_pos
  intro i hi
  exact Real.sqrt_pos.mpr (rawCoupling_pos T hneg (i+1) ⟨by omega,by have := Finset.mem_range.mp hi; omega⟩)

/-- The actual Euclidean operator action of the genuine raw residual polynomial is precisely its positive pivot/link-scaled real site vector.
Use: the formula concerns the same real operator and initial vector as the actual CG reference.
Article: main_krylov, prop:dict(i).
Proof: polynomial evaluation commutes with the genuine matrix/operator
algebra identification; transfer the proved real matrix site action through it. -/
theorem raw_residual_polynomial_action (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s<N) :
    CG.polynomialAction (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0))
      ((rawJacobi T).residual dictionaryInterval s)=
      (((rawJacobi T).den dictionaryInterval s)⁻¹*(rawJacobi T).linkProduct s) •
        WithLp.toLp 2 (JacobiData.site N s) := by
  have he := (Polynomial.aeval_algHom_apply (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ)).toAlgEquiv.toAlgHom
    T ((rawJacobi T).residual dictionaryInterval s)).symm
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (aeval T ((rawJacobi T).residual dictionaryInterval s))=
    aeval (cgOperator T) ((rawJacobi T).residual dictionaryInterval s) at he
  change aeval (cgOperator T) ((rawJacobi T).residual dictionaryInterval s) (WithLp.toLp 2 (JacobiData.site N 0))=_
  rw [← he,Matrix.toEuclideanCLM_toLp,raw_residual_matrix_site T hT htri hneg s hs,smul_smul]
  rfl

/-- Every actual normalized raw determinant residual has its exact true indexed polynomial degree through the full dimension.
Use: the genuine raw residual prefix spans precisely the actual low-degree Krylov space.
Article: main_krylov, prop:dict(i).
Proof: the genuine leading continuant is monic of its true degree. Its real
affine coordinate has degree one, and the actual positive normalization
factor is nonzero, so composition and multiplication preserve that degree. -/
theorem raw_residual_degree (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s≤N) :
    ((rawJacobi T).residual dictionaryInterval s).degree=s := by
  -- The real positive leading normalization cannot erase the genuine indexed polynomial degree.
  have ha := rawJacobi_admissible T hT htri hneg
  have hz : C dictionaryInterval.eta-C (2/dictionaryInterval.delta)*X=(C (2 : ℝ)-X) := by
    norm_num [dictionaryInterval,SpectralInterval.eta,SpectralInterval.delta]
  have hdeg : (C (2 : ℝ)-X).degree=1 := by
    rw [degree_sub_eq_right_of_degree_lt (by norm_num),degree_X]
  have hl : ((rawJacobi T).leading s).degree=s := by
    rw [JacobiData.leading,degree_eq_natDegree ((rawJacobi T).block_monic (rawJacobi_aSq_nonneg T) 0 s).ne_zero,
      (rawJacobi T).block_natDegree (rawJacobi_aSq_nonneg T)]
  rw [JacobiData.residual,hz,degree_mul,degree_C (inv_ne_zero (ha s hs).ne'),
    degree_comp (by rw [hdeg]; norm_num),hl,hdeg]
  simp

/-- The actual raw determinant residual is genuinely normalized to one at zero at every used degree.
Use: the real normalized Galerkin uniqueness theorem applies to these true polynomials.
Article: main_krylov, prop:dict(i).
Proof: at zero the actual numerator is exactly its true positive leading normalization denominator. -/
theorem raw_residual_zero (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s≤N) :
    ((rawJacobi T).residual dictionaryInterval s).eval 0=1 := by
  rw [JacobiData.residual_eval,dictionaryInterval_z,sub_zero,← dictionaryInterval_eta]
  exact div_self ((rawJacobi_admissible T hT htri hneg) s hs).ne'


/-- Distinct actual physical site vectors are genuinely Euclidean orthogonal.
Use: true raw polynomial actions annihilate every preceding degree site.
Article: main_krylov, prop:dict(i).
Proof: the actual sites are distinct standard coordinate vectors, whose true inner product is zero. -/
theorem raw_site_inner_orth (s i : ℕ) (hs : s<N) (hi : i<N) (hne : s≠i) :
    inner ℝ (WithLp.toLp 2 (JacobiData.site N s)) (WithLp.toLp 2 (JacobiData.site N i))=0 := by
  rw [JacobiData.site_eq_single N s hs,JacobiData.site_eq_single N i hi]
  have he : (⟨s,hs⟩ : Fin N)≠⟨i,hi⟩ := fun he => hne (congrArg Fin.val he)
  simp [EuclideanSpace.inner_single_left,he]


/-- Every genuine internal raw residual polynomial action on the actual first site is nonzero.
Use: true CG nonstagnation will follow from actual Galerkin uniqueness rather than be assumed.
Article: main_krylov, prop:dict(i).
Proof: its real site coefficient is strictly positive by genuine leading
minor and link positivity; its actual degree-site coordinate is one. -/
theorem raw_residual_action_ne (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s<N) :
    CG.polynomialAction (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0))
      ((rawJacobi T).residual dictionaryInterval s)≠0 := by
  rw [raw_residual_polynomial_action T hT htri hneg s hs]
  apply smul_ne_zero
  · exact (mul_pos (inv_pos.mpr (rawJacobi_admissible T hT htri hneg s hs.le)) (raw_linkProduct_pos T hneg s hs)).ne'
  · intro hz
    have he := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v ⟨s,hs⟩) hz
    simp [JacobiData.site] at he

/-- The genuine internal raw residual polynomial action is orthogonal to the actual full preceding Krylov space.
Use: discharge real Galerkin orthogonality before identifying actual CG polynomials at the supplied matrix spectral measure.
Article: main_krylov, prop:dict(i).
Proof: exact raw polynomial degrees give the true preceding Krylov span.
The proved actual operator actions are multiples of earlier physical sites;
true site orthogonality extends from those actual generators to the real span. -/
theorem raw_residual_orthogonal_krylov (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s<N)
    (v : EuclideanSpace ℝ (Fin N))
    (hv : v∈CG.krylovSpace (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0)) s) :
    inner ℝ v (CG.polynomialAction (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0))
      ((rawJacobi T).residual dictionaryInterval s))=0 := by
  -- The true degree-graded Krylov span is generated by actual preceding physical site actions.
  let first : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (JacobiData.site N 0)
  let w := CG.polynomialAction (cgOperator T) first ((rawJacobi T).residual dictionaryInterval s)
  have hK := CG.polynomialAction_span (cgOperator T) first
    (fun i => (rawJacobi T).residual dictionaryInterval i) s
    (fun i hi => raw_residual_degree T hT htri hneg i (by omega))
  rw [hK] at hv
  have hle : Submodule.span ℝ ((fun i => CG.polynomialAction (cgOperator T) first
      ((rawJacobi T).residual dictionaryInterval i)) '' Set.Iio s)≤(innerSL ℝ w).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change i<s at hi
    change inner ℝ w (CG.polynomialAction (cgOperator T) first ((rawJacobi T).residual dictionaryInterval i))=0
    dsimp only [w,first]
    rw [raw_residual_polynomial_action T hT htri hneg s hs,
      raw_residual_polynomial_action T hT htri hneg i (by omega),real_inner_smul_left,real_inner_smul_right,
      raw_site_inner_orth s i hs (by omega) (by omega),mul_zero,mul_zero]
  have he : inner ℝ w v=0 := hle hv
  simpa only [real_inner_comm] using he


/-- The genuine terminal raw determinant residual annihilates the actual full physical matrix, including dimension zero.
Use: terminal exactness is derived from the supplied matrix rather than an assumed stopping polynomial.
Article: main_krylov, prop:dict(i).
Proof: the true affine operator evaluation converts the real terminal
continuant to the actual full Jacobi characteristic polynomial; use Cayley--Hamilton. -/
theorem raw_residual_matrix_terminal (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) :
    aeval T ((rawJacobi T).residual dictionaryInterval N)=0 := by
  rw [JacobiData.residual,map_mul,aeval_comp,raw_affine_aeval T hT htri hneg,JacobiData.leading,
    (rawJacobi T).block_eq_charpoly (rawJacobi_aSq_nonneg T),Matrix.aeval_self_charpoly,mul_zero]

/-- The genuine terminal raw residual polynomial has zero actual Euclidean first-site operator action.
Use: include the true terminal degree in the measured CG dictionary.
Article: main_krylov, prop:dict(i).
Proof: the actual matrix/operator algebra equivalence preserves the proved real terminal annihilation identity. -/
theorem raw_residual_terminal_action (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) :
    CG.polynomialAction (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0))
      ((rawJacobi T).residual dictionaryInterval N)=0 := by
  have he := Polynomial.aeval_algHom_apply (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ)).toAlgEquiv.toAlgHom
    T ((rawJacobi T).residual dictionaryInterval N)
  rw [raw_residual_matrix_terminal T hT htri hneg,map_zero] at he
  change aeval (cgOperator T) ((rawJacobi T).residual dictionaryInterval N)=0 at he
  change aeval (cgOperator T) ((rawJacobi T).residual dictionaryInterval N) (WithLp.toLp 2 (JacobiData.site N 0))=0
  rw [he,_root_.zero_apply]

end
end krylov.Realization
