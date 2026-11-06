import krylov.Realization.PhysicalJacobi
import krylov.Reference.CGCovariance
import jacobi.Finite.OrderedSpectrum
import chebyshev1.TwoTerm.VariableHessian

/-! Jacobi coefficients are actual CG coefficients recorded on the physical
diagonal spectral model and replayed on an arbitrary nonlinear objective. -/
namespace chebyshev1.Background
noncomputable section
open Matrix Polynomial Polynomial.Chebyshev chebyshev2 krylov.Realization krylov.Reference
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

theorem physicalJacobi_posDef_of_spectrum (I : SpectralInterval) (J : chebyshev2.Jacobi N)
    (hspec : spectrum ℝ J.matrix ⊆ Set.Icc (-1) 1) : (physicalJacobi I J).PosDef := by
  have hp := J.affine_posDef ((I.L+I.mu)/2) (-(I.delta/2)) (fun x hx => by
    have hi := hspec hx
    have hm := I.lambda_mem hi
    have hh := I.mu_pos.trans_le hm.1
    simpa only [SpectralInterval.lambda, neg_mul, sub_eq_add_neg] using hh)
  have hs : Matrix.scalar (Fin N) ((I.L+I.mu)/2) = ((I.L+I.mu)/2) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  rw [hs] at hp
  simpa only [physicalJacobi, sub_eq_add_neg, neg_smul] using hp

/-- Every leading physical determinant has the correct interval scale. -/
theorem physicalJacobi_leading_det (I : SpectralInterval) (J : chebyshev2.Jacobi N)
    (s : ℕ) (hs : s ≤ N) :
    (rawBlock (physicalJacobi I J) 0 s (by omega)).det = (I.delta/2)^s*J.data.den I s := by
  let e : Fin s → Fin N := fun i => ⟨0+i.val,by omega⟩
  have hi : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have he := congrArg (fun k : Fin N => k.val) hij
    dsimp [e] at he
    omega
  have hblock : rawBlock (physicalJacobi I J) 0 s (by omega) =
      ((I.L+I.mu)/2) • 1-(I.delta/2) • J.data.matrix 0 s := by
    change (((I.L+I.mu)/2) • (1 : Matrix (Fin N) (Fin N) ℝ)-
      (I.delta/2) • J.matrix).submatrix e e = _
    have hm := J.data.matrix_principal_block N 0 s (by omega)
    have hu := Matrix.submatrix_one e hi (α := ℝ)
    ext i j
    have hmij := congrArg (fun M : Matrix (Fin s) (Fin s) ℝ => M i j) hm
    have huij := congrArg (fun M : Matrix (Fin s) (Fin s) ℝ => M i j) hu
    simpa only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, chebyshev2.Jacobi.matrix] using
      congrArg₂ (fun x y : ℝ => ((I.L+I.mu)/2)*x-(I.delta/2)*y) huij hmij
  have hscale : I.delta/2*I.eta = (I.L+I.mu)/2 := by
    dsimp [SpectralInterval.eta]
    field_simp [I.delta_pos.ne']
  rw [hblock, show ((I.L+I.mu)/2) • (1 : Matrix (Fin s) (Fin s) ℝ)-
      (I.delta/2) • J.data.matrix 0 s = (I.delta/2) • (I.eta • 1-J.data.matrix 0 s) by
        rw [smul_sub, smul_smul, hscale], Matrix.det_smul, Fintype.card_fin]
  congr 1
  rw [JacobiData.den, JacobiData.leading, J.data.block_eq_charpoly J.coupling_nonneg, Matrix.eval_charpoly]
  congr 1
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

theorem physical_rawAlpha (I : SpectralInterval) (J : chebyshev2.Jacobi N) (hJ : J.Irreducible)
    (hspec : spectrum ℝ J.matrix ⊆ Set.Icc (-1) 1) (s : ℕ) (hs : s < N) :
    rawAlpha (physicalJacobi I J) s = (J.data.method I).gamma s := by
  have hT := physicalJacobi_posDef_of_spectrum I J hspec
  rw [rawAlpha_det _ hT (physicalJacobi_tridiagonal I J) (physicalJacobi_negative I J hJ) s hs,
    physicalJacobi_leading_det I J s hs.le, physicalJacobi_leading_det I J (s+1) (by omega),
    pow_succ]
  dsimp [JacobiData.method]
  have hc : (I.delta/2)^s ≠ 0 := pow_ne_zero _ (div_ne_zero I.delta_pos.ne' (by norm_num))
  field_simp [hc, I.delta_pos.ne']

/-- These are genuine measured CG line lengths, not prescribed dictionary data. -/
theorem physical_recorded_length (I : SpectralInterval) (J : chebyshev2.Jacobi N) (hJ : J.Irreducible)
    (hspec : spectrum ℝ J.matrix ⊆ Set.Icc (-1) 1) (s : ℕ) (hs : s < N) :
    CG.length (cgOperator (physicalJacobi I J)) (WithLp.toLp 2 (JacobiData.site N 0)) s =
      (J.data.method I).gamma s := by
  rw [raw_cg_length _ (physicalJacobi_posDef_of_spectrum I J hspec)
    (physicalJacobi_tridiagonal I J) (physicalJacobi_negative I J hJ) s hs]
  exact physical_rawAlpha I J hJ hspec s hs

theorem physical_recorded_beta (I : SpectralInterval) (J : chebyshev2.Jacobi N) (hJ : J.Irreducible)
    (hspec : spectrum ℝ J.matrix ⊆ Set.Icc (-1) 1) (s : ℕ) (hs : s+1 < N) :
    CG.beta (cgOperator (physicalJacobi I J)) (WithLp.toLp 2 (JacobiData.site N 0)) s =
      J.data.aSq (s+1)*(J.data.den I s/J.data.den I (s+1))^2 := by
  let i : Fin N := ⟨s,by omega⟩
  let j : Fin N := ⟨s+1,hs⟩
  rw [raw_cg_beta _ (physicalJacobi_posDef_of_spectrum I J hspec)
    (physicalJacobi_tridiagonal I J) (physicalJacobi_negative I J hJ) s (by omega),
    rawBeta_edge _ i j rfl, physical_rawAlpha I J hJ hspec i.val i.isLt]
  have he : physicalJacobi I J i j = -(I.delta/2)*Real.sqrt (J.data.aSq (s+1)) := by
    have hij : i ≠ j := by intro h; have hh := congrArg Fin.val h; dsimp [i,j] at hh; omega
    simp only [physicalJacobi, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_ne hij, mul_zero, chebyshev2.Jacobi.matrix, JacobiData.matrix_apply,
      Nat.zero_add, hij, ite_false, show i.val+1=j.val from rfl, ite_true, zero_sub]
    dsimp [i,j]
    ring
  rw [he]
  dsimp [JacobiData.method]
  dsimp [i,j]
  simp only [mul_pow, neg_sq, Real.sq_sqrt (J.coupling_nonneg _)]
  field_simp [I.delta_pos.ne']

/-- The ordinary recorded-CG two-memory coefficients, replayable on any gradient. -/
def recordedCGMethod {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Q : E →L[ℝ] E) (g : E) : TwoTerm where
  gamma := CG.length Q g
  b s := if s=0 then 0 else -(CG.length Q g s*CG.beta Q g (s-1)/CG.length Q g (s-1))
  a s := if s=0 then 1 else 1+CG.length Q g s*CG.beta Q g (s-1)/CG.length Q g (s-1)

theorem physical_recorded_momentum (I : SpectralInterval) (J : chebyshev2.Jacobi N) (hJ : J.Irreducible)
    (hspec : spectrum ℝ J.matrix ⊆ Set.Icc (-1) 1) (s : ℕ) (hs0 : 0 < s) (hs : s < N) :
    CG.length (cgOperator (physicalJacobi I J)) (WithLp.toLp 2 (JacobiData.site N 0)) s*
      CG.beta (cgOperator (physicalJacobi I J)) (WithLp.toLp 2 (JacobiData.site N 0)) (s-1)/
        CG.length (cgOperator (physicalJacobi I J)) (WithLp.toLp 2 (JacobiData.site N 0)) (s-1) =
      -(J.data.method I).b s := by
  have ha := J.data.admissible_of_spectrum I N J.coupling_nonneg hspec
  rw [physical_recorded_length I J hJ hspec s hs,
    physical_recorded_length I J hJ hspec (s-1) (by omega),
    physical_recorded_beta I J hJ hspec (s-1) (by omega)]
  simp only [show s-1+1=s by omega]
  dsimp [JacobiData.method]
  simp only [show s-1+1=s by omega]
  field_simp [I.delta_pos.ne', (ha s hs.le).ne', (ha (s-1) (by omega)).ne', (ha (s+1) (by omega)).ne']

theorem physical_recorded_coefficients (I : SpectralInterval) (J : chebyshev2.Jacobi N) (hJ : J.Irreducible)
    (hspec : spectrum ℝ J.matrix ⊆ Set.Icc (-1) 1) (s : ℕ) (hs : s < N) :
    let S := recordedCGMethod (cgOperator (physicalJacobi I J)) (WithLp.toLp 2 (JacobiData.site N 0))
    S.gamma s=(J.data.method I).gamma s ∧ S.b s=(J.data.method I).b s ∧ S.a s=(J.data.method I).a s := by
  have ha := J.data.admissible_of_spectrum I N J.coupling_nonneg hspec
  refine ⟨physical_recorded_length I J hJ hspec s hs, ?_, ?_⟩
  · by_cases hz : s=0
    · subst s; simp [recordedCGMethod, JacobiData.method, J.coupling_zero]
    · simp only [recordedCGMethod, ite_eq_right hz]
      rw [physical_recorded_momentum I J hJ hspec s (by omega) hs, neg_neg]
  · by_cases hz : s=0
    · subst s
      simp only [recordedCGMethod, ite_true, JacobiData.method, JacobiData.den_zero]
      rw [← J.data.den_one I]
      exact (one_div_mul_cancel (ha 1 (by omega)).ne').symm
    · simp only [recordedCGMethod, ite_eq_right hz]
      rw [physical_recorded_momentum I J hJ hspec s (by omega) hs]
      have hf := J.data.fixed_point I (s-1) (by simpa only [show s-1+2=s+1 by omega] using (ha (s+1) (by omega)).ne')
      simp only [show s-1+1=s by omega] at hf
      linarith

/-- The actual diagonal quadratic used to record CG coefficients. -/
def recordedDiagonal (I : SpectralInterval) (J : chebyshev2.Jacobi N)
    (B : SpectralBasis J.matrix) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun j => I.lambda (B.eigenvalues j))

/-- Orthogonal spectral coordinates, with their genuine first-site starting gradient. -/
def recordedCoordinates (J : chebyshev2.Jacobi N) (B : SpectralBasis J.matrix) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) B.Qᵀ

def recordedGradient (J : chebyshev2.Jacobi N) (B : SpectralBasis J.matrix) :
    EuclideanSpace ℝ (Fin N) :=
  recordedCoordinates J B (WithLp.toLp 2 (JacobiData.site N 0))

theorem recordedCoordinates_inner (J : chebyshev2.Jacobi N) (B : SpectralBasis J.matrix)
    (v w : EuclideanSpace ℝ (Fin N)) :
    inner ℝ (recordedCoordinates J B v) (recordedCoordinates J B w) = inner ℝ v w := by
  simp only [recordedCoordinates, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toEuclideanCLM, star_trivial]
  rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, B.mul_transpose,
    Matrix.one_mulVec, dotProduct_comm]

theorem recordedCoordinates_intertwine (I : SpectralInterval) (J : chebyshev2.Jacobi N)
    (B : SpectralBasis J.matrix) (v : EuclideanSpace ℝ (Fin N)) :
    cgOperator (recordedDiagonal I J B) (recordedCoordinates J B v) =
      recordedCoordinates J B (cgOperator (physicalJacobi I J) v) := by
  have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M*B.Qᵀ)
    (physicalJacobiBasis I J B).diagonalize
  dsimp [physicalJacobiBasis] at h
  have hi : recordedDiagonal I J B*B.Qᵀ = B.Qᵀ*physicalJacobi I J := by
    simpa only [Matrix.mul_assoc, B.mul_transpose, Matrix.mul_one, recordedDiagonal] using h.symm
  change Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (recordedDiagonal I J B)
    (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) B.Qᵀ v) =
      Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) B.Qᵀ
        (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (physicalJacobi I J) v)
  have hh := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ =>
    Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) M v) hi
  simpa only [map_mul, mul_apply_eq_comp] using hh

/-- The diagonal run records exactly the same genuine measured CG line lengths. -/
theorem diagonal_recorded_length (I : SpectralInterval) (J : chebyshev2.Jacobi N)
    (hJ : J.Irreducible) (hspec : spectrum ℝ J.matrix ⊆ Set.Icc (-1) 1)
    (B : SpectralBasis J.matrix) (s : ℕ) (hs : s < N) :
    CG.length (cgOperator (recordedDiagonal I J B)) (recordedGradient J B) s =
      (J.data.method I).gamma s := by
  rw [recordedGradient, cg_length_isometric (recordedCoordinates J B)
    (recordedCoordinates_inner J B) _ _ (recordedCoordinates_intertwine I J B)]
  exact physical_recorded_length I J hJ hspec s hs

theorem diagonal_recorded_beta (I : SpectralInterval) (J : chebyshev2.Jacobi N)
    (B : SpectralBasis J.matrix) (s : ℕ) :
    CG.beta (cgOperator (recordedDiagonal I J B)) (recordedGradient J B) s =
      CG.beta (cgOperator (physicalJacobi I J)) (WithLp.toLp 2 (JacobiData.site N 0)) s := by
  exact cg_beta_isometric (recordedCoordinates J B) (recordedCoordinates_inner J B)
    _ _ (recordedCoordinates_intertwine I J B) _ s

/-- The squared components of the recorded gradient are exactly the spectral weights. -/
theorem recordedGradient_sq (J : chebyshev2.Jacobi N) (B : SpectralBasis J.matrix)
    (hN : 0 < N) (j : Fin N) :
    (recordedGradient J B j)^2 = B.weight ⟨0,hN⟩ j := by
  change (B.Qᵀ.mulVec (JacobiData.site N 0) j)^2 = _
  rw [JacobiData.site_eq_single N 0 hN, Matrix.mulVec_single_one]
  rfl

theorem recordedGradient_sq_sum (J : chebyshev2.Jacobi N) (B : SpectralBasis J.matrix)
    (hN : 0 < N) : ∑ j, (recordedGradient J B j)^2 = 1 := by
  simp only [recordedGradient_sq J B hN]
  exact B.weight_sum _

theorem recordedGradient_sq_pos (J : chebyshev2.Jacobi N) (hJ : J.Irreducible)
    (B : SpectralBasis J.matrix) (hN : 0 < N) (j : Fin N) :
    0 < (recordedGradient J B j)^2 := by
  rw [recordedGradient_sq J B hN]
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  exact (J.data.spectral_endpoint_positive B J.coupling_nonneg hJ
    (jacobi.Finite.basis_values_injective J hJ B) j).1

/-- All recorded diagonal coefficients agree throughout the requested horizon. -/
theorem diagonal_recorded_coefficients (I : SpectralInterval) (J : chebyshev2.Jacobi N)
    (hJ : J.Irreducible) (hspec : spectrum ℝ J.matrix ⊆ Set.Icc (-1) 1)
    (B : SpectralBasis J.matrix) (s : ℕ) (hs : s < N) :
    let S := recordedCGMethod (cgOperator (recordedDiagonal I J B)) (recordedGradient J B)
    S.gamma s=(J.data.method I).gamma s ∧ S.b s=(J.data.method I).b s ∧ S.a s=(J.data.method I).a s := by
  have hl (t : ℕ) := cg_length_isometric (recordedCoordinates J B)
    (recordedCoordinates_inner J B) _ _ (recordedCoordinates_intertwine I J B)
    (WithLp.toLp 2 (JacobiData.site N 0)) t
  have hb (t : ℕ) := cg_beta_isometric (recordedCoordinates J B)
    (recordedCoordinates_inner J B) _ _ (recordedCoordinates_intertwine I J B)
    (WithLp.toLp 2 (JacobiData.site N 0)) t
  simpa only [recordedCGMethod, recordedGradient, hl, hb] using
    physical_recorded_coefficients I J hJ hspec s hs

/-- Coefficient agreement implies equality of the actual nonlinear executor. -/
theorem nonlinearError_eq_of_coefficients_upto {d : Type*} (S T : TwoTerm)
    (hcoeff : ∀ s < N, S.gamma s=T.gamma s ∧ S.b s=T.b s ∧ S.a s=T.a s)
    (g : (d → ℝ) → d → ℝ) (e0 : d → ℝ) (n : ℕ) (hn : n ≤ N) :
    S.nonlinearError g e0 n = T.nonlinearError g e0 n := by
  have he : ∀ n, n ≤ N → S.nonlinearError g e0 n = T.nonlinearError g e0 n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => intro _; rfl
    | one =>
      intro hn
      simp only [TwoTerm.nonlinearError, (hcoeff 0 (by omega)).1]
    | more n ih0 ih1 =>
      intro hn
      rw [TwoTerm.nonlinearError, TwoTerm.nonlinearError, ih0 (by omega), ih1 (by omega),
        (hcoeff (n+1) (by omega)).1, (hcoeff (n+1) (by omega)).2.1,
        (hcoeff (n+1) (by omega)).2.2]
  exact he n hn

/-- The genuine diagonal-CG transcript can be replayed on every actual objective. -/
theorem diagonal_recorded_nonlinearError {d : Type*} (I : SpectralInterval)
    (J : chebyshev2.Jacobi N) (hJ : J.Irreducible)
    (hspec : spectrum ℝ J.matrix ⊆ Set.Icc (-1) 1) (B : SpectralBasis J.matrix)
    (g : (d → ℝ) → d → ℝ) (e0 : d → ℝ) (n : ℕ) (hn : n ≤ N) :
    (recordedCGMethod (cgOperator (recordedDiagonal I J B)) (recordedGradient J B)).nonlinearError g e0 n =
      (J.data.method I).nonlinearError g e0 n :=
  nonlinearError_eq_of_coefficients_upto _ _
    (diagonal_recorded_coefficients I J hJ hspec B) g e0 n hn

/-- The model eigenvalues are precisely all roots of the minimax residual. -/
theorem recordedDiagonal_roots (I : SpectralInterval) (J : chebyshev2.Jacobi N)
    (hN : 0 < N) (hterm : J.Terminal) (B : SpectralBasis J.matrix) :
    Set.range (fun j => I.lambda (B.eigenvalues j)) = {lam | (I.residual N).eval lam=0} := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have hpoly : J.matrix.charpoly = C ((1/2 : ℝ)^n)*T ℝ (n+1) :=
    (J.charpoly_eq hterm).trans (fiberPolynomial_succ n)
  have hroot (x : ℝ) : J.matrix.charpoly.eval x=0 ↔ (T ℝ (n+1)).eval x=0 := by
    rw [hpoly, eval_mul, eval_C]
    exact mul_eq_zero.trans (or_iff_right (pow_ne_zero n (by norm_num : (1/2 : ℝ)≠0)))
  have hres (lam : ℝ) : (I.residual (n+1)).eval lam=0 ↔ (T ℝ (n+1)).eval (I.z lam)=0 := by
    rw [I.residual_eval]
    exact div_eq_zero_iff.trans (or_iff_left (I.den_ne (n+1)))
  ext lam
  rw [Set.mem_range, Set.mem_ofPred_eq, hres, ← hroot, B.charpoly_factor, eval_prod]
  simp only [eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨j,by rw [I.z_lambda, sub_self]⟩
  · rintro ⟨j,hj⟩
    refine ⟨j,?_⟩
    rw [← sub_eq_zero.mp hj, I.lambda_z]

theorem recordedDiagonal_posDef (I : SpectralInterval) (J : chebyshev2.Jacobi N)
    (hspec : spectrum ℝ J.matrix ⊆ Set.Icc (-1) 1) (B : SpectralBasis J.matrix) :
    (recordedDiagonal I J B).PosDef := by
  have hT := physicalJacobi_posDef_of_spectrum I J hspec
  have hq := hT.conjTranspose_mul_mul_same (B := B.Q) (by
    intro x y h
    have hh := congrArg B.Qᵀ.mulVec h
    simpa only [Matrix.mulVec_mulVec, B.transpose_mul, Matrix.one_mulVec] using hh)
  have hd : B.Qᵀ*physicalJacobi I J*B.Q=recordedDiagonal I J B :=
    (physicalJacobiBasis I J B).diagonalize
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hd] using hq

/-- Every terminal Jacobi method is genuine CG recorded on a positive diagonal
quadratic at the minimax roots, with positive probability gradient squares, and
replayed on the given actual objective. The spectral basis is constructed. -/
theorem terminal_recordedCG {d : Type*} (I : SpectralInterval)
    (J : chebyshev2.Jacobi N) (hN : 0 < N) (hJ : J.Irreducible) (hterm : J.Terminal)
    (g : (d → ℝ) → d → ℝ) (e0 : d → ℝ) :
    ∃ (node weight : Fin N → ℝ) (gmodel : EuclideanSpace ℝ (Fin N)),
      (Matrix.diagonal node).PosDef ∧ Function.Injective node ∧
      Set.range node = {lam | (I.residual N).eval lam=0} ∧
      (∀ j, 0 < weight j) ∧ (∑ j, weight j)=1 ∧ (∀ j, (gmodel j)^2=weight j) ∧
      (∀ s < N,
        let S := recordedCGMethod (cgOperator (Matrix.diagonal node)) gmodel
        S.gamma s=(J.data.method I).gamma s ∧ S.b s=(J.data.method I).b s ∧ S.a s=(J.data.method I).a s) ∧
      ∀ n ≤ N,
        (recordedCGMethod (cgOperator (Matrix.diagonal node)) gmodel).nonlinearError g e0 n =
          (J.data.method I).nonlinearError g e0 n := by
  let B := SpectralBasis.ofHermitian J.matrix J.matrix_isHermitian
  have hspec := J.spectrum_subset hN hterm
  refine ⟨fun j => I.lambda (B.eigenvalues j), B.weight ⟨0,hN⟩, recordedGradient J B,
    recordedDiagonal_posDef I J hspec B, ?_, recordedDiagonal_roots I J hN hterm B,
    ?_, B.weight_sum _, recordedGradient_sq J B hN,
    diagonal_recorded_coefficients I J hJ hspec B,
    diagonal_recorded_nonlinearError I J hJ hspec B g e0⟩
  · intro i j hij
    apply jacobi.Finite.basis_values_injective J hJ B
    simpa only [I.z_lambda] using congrArg I.z hij
  · intro j
    rw [← recordedGradient_sq J B hN j]
    exact recordedGradient_sq_pos J hJ B hN j

end
end chebyshev1.Background
