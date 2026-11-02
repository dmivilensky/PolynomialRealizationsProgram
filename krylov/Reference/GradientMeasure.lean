import krylov.Reference.EnergyMinimum
import krylov.Reference.Gauss

/-!
Article: main_krylov, Section 3, gradient spectral measure and Gauss remainder.
Use: connect the actual CG residual polynomial to the orthogonal polynomial
and leading Jacobi determinant of its actual gradient spectral measure.
Source: the classical CG/Gauss dictionary (Meurant06, GolubMeurant10).
-/

namespace krylov.Reference
noncomputable section
open Matrix Polynomial jacobi.Finite krylov.Secant
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
variable {n : ℕ}

/-- The physical gradient and the canonical initial error have exactly the same distinct active spectral values.
Use: all gradient-measure quadrature degrees are governed by the same actual CG stopping time.
Article: main_krylov, s2:eq:cg, dσ proportional to t dν.
Proof: each physical coordinate is its canonical coordinate times a strictly positive square-root eigenvalue. -/
theorem activeSpectralValues_gradient (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) :
    activeSpectralValues base hb.1 g=activeSpectralValues base hb.1 (cgCanonicalError base g 0) := by
  -- Compare the actual eigen-coordinate support before taking its image in the distinct eigenvalues.
  unfold activeSpectralValues
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have he := gradient_spectral_coordinate base hb g i
  change inner ℝ (hb.1.eigenvectorBasis i) g=Real.sqrt (hb.1.eigenvalues i)*
    inner ℝ (hb.1.eigenvectorBasis i) (cgCanonicalError base g 0) at he
  rw [he, mul_ne_zero_iff]
  exact and_iff_right (Real.sqrt_pos.mpr (hb.eigenvalues_pos i)).ne'

/-- The actual normalized gradient spectral probability measure.
Use: its leading Jacobi matrices give the Gaussian rules for inverse curvature.
Article: main_krylov, Section 3, σ, the spectral measure of g₀/‖g₀‖. -/
def gradientSpectralData (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) :
    DiscreteMeasure (activeSpectralValues base hb.1 g).card :=
  vectorSpectralData base hb.1 g hg

/-- The gradient spectral measure has exactly the actual CG active atom count.
Use: transfers every pre-exhaustion polynomial and quadrature assertion to the constructed measure.
Article: main_krylov, s2:eq:cg, common support of σ and ν.
Proof: take cardinalities of the proved equality of distinct active supports. -/
theorem gradientSpectralData_count (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) :
    (activeSpectralValues base hb.1 g).card=referenceAtomCount base hb g :=
  congrArg Finset.card (activeSpectralValues_gradient base hb g)

/-- Actual polynomial gradient actions have their exact inner products in the actual normalized gradient spectral measure.
Use: turns the executed CG Galerkin equations into genuine orthogonal-polynomial equations.
Article: main_krylov, Section 3, Lanczos/gradient-measure dictionary.
Proof: actual eigenbasis Parseval, the proved polynomial eigenvector pairing,
and the proved distinct-eigenspace aggregation identify both sides. -/
theorem gradientSpectralData_inner (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) (p q : ℝ[X]) :
    inner ℝ (CG.polynomialAction (cgOperator base) g p) (CG.polynomialAction (cgOperator base) g q)=
      ‖g‖^2*inner ℝ ((gradientSpectralData base hb g hg).evaluate p)
        ((gradientSpectralData base hb g hg).evaluate q) := by
  -- Work in the actual physical eigenbasis before grouping repeated eigenvalues.
  have hp (r : ℝ[X]) (i : Fin n) : inner ℝ (hb.1.eigenvectorBasis i)
      (CG.polynomialAction (cgOperator base) g r)=r.eval (hb.1.eigenvalues i)*inner ℝ (hb.1.eigenvectorBasis i) g := by
    apply CG.polynomialAction_eigenvector (cgOperator base) (cgOperator_positive base hb).1
    ext j
    exact congrFun (hb.1.mulVec_eigenvectorBasis i) j
  have he := hb.1.eigenvectorBasis.sum_inner_mul_inner
    (CG.polynomialAction (cgOperator base) g p) (CG.polynomialAction (cgOperator base) g q)
  have hsum : inner ℝ (CG.polynomialAction (cgOperator base) g p) (CG.polynomialAction (cgOperator base) g q)=
      ∑ i : Fin n, (inner ℝ (hb.1.eigenvectorBasis i) g)^2*
        (p.eval (hb.1.eigenvalues i)*q.eval (hb.1.eigenvalues i)) := by
    rw [← he]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (hb.1.eigenvectorBasis i) (CG.polynomialAction (cgOperator base) g p), hp, hp]
    ring
  have hs := vectorSpectralData_integral base hb.1 g hg (fun t => p.eval t*q.eval t)
  simp only [← mul_assoc] at hs
  rw [← jacobi.Finite.DiscreteMeasure.inner_evaluate] at hs
  rw [hsum]
  have hnorm : ‖g‖^2≠0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
  change _=‖g‖^2*inner ℝ ((vectorSpectralData base hb.1 g hg).evaluate p) ((vectorSpectralData base hb.1 g hg).evaluate q)
  rw [hs, mul_div_cancel₀ _ hnorm]
  simp only [mul_assoc]

/-- The actual CG residual polynomial is orthogonal to every lower-degree polynomial in its actual gradient measure.
Use: identifies the measured Lanczos orthogonal polynomial without a prescribed terminal polynomial.
Article: main_krylov, Section 3, residual orthogonality in σ.
Proof: apply the computed Krylov Galerkin condition and divide the actual gradient spectral inner product by the positive initial residual energy. -/
theorem residualPolynomial_gradient_orthogonal (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) {m : ℕ} (hm : m≤referenceAtomCount base hb g)
    {q : ℝ[X]} (hq : q.degree<m) :
    inner ℝ ((gradientSpectralData base hb g hg).evaluate q)
      ((gradientSpectralData base hb g hg).evaluate (CG.residualPolynomial (cgOperator base) g m))=0 := by
  have hk : CG.polynomialAction (cgOperator base) g q∈CG.krylovSpace (cgOperator base) g m :=
    ⟨q, mem_degreeLT.mpr hq, rfl⟩
  have he := CG.gradient_orthogonal_krylov (cgOperator base) (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 g m (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hm)) hk
  rw [← (CG.polynomialAction_pair (cgOperator base) g m).1,
    gradientSpectralData_inner base hb g hg] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 (norm_ne_zero_iff.mpr hg))

/-- Before exhaustion, the computed residual is a scalar multiple of the actual degree-m orthogonal polynomial in σ.
Use: connects actual CG zeros to the actual Gaussian quadrature nodes.
Article: main_krylov, Section 3, CG/Gauss polynomial dictionary.
Proof: expand the actual residual in the existing orthogonal polynomial basis;
all earlier coefficients vanish by the proved computed Galerkin condition. -/
theorem residualPolynomial_orthogonal_factor (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) {m : ℕ} (hm : m<referenceAtomCount base hb g) :
    ∃ c : ℝ, CG.residualPolynomial (cgOperator base) g m=
      c • (gradientSpectralData base hb g hg).orthogonalPolynomial ⟨m, by rwa [gradientSpectralData_count]⟩ := by
  -- The expansion is in the actually constructed measure, whose support size has been proved to equal the stopping time.
  let M := gradientSpectralData base hb g hg
  have hmM : m<(activeSpectralValues base hb.1 g).card := by rwa [gradientSpectralData_count]
  have he := polynomial_prefix_expansion M hmM (CG.polynomial_degree (cgOperator base) g m).1
  refine ⟨inner ℝ (M.polynomialBasis ⟨m, hmM⟩) (M.evaluate (CG.residualPolynomial (cgOperator base) g m)), ?_⟩
  nth_rw 1 [he]
  rw [Finset.sum_eq_single ⟨m, hmM⟩]
  · intro i hi him
    have hil : i.val<m := by
      have hle := (Finset.mem_filter.mp hi).2
      have hne : i.val≠m := fun h => him (Fin.ext h)
      omega
    have hdeg : (M.orthogonalPolynomial i).degree<m := by
      rw [degree_eq_natDegree (leadingCoeff_ne_zero.mp (M.orthogonalPolynomial_degree i).2.ne'),
        (M.orthogonalPolynomial_degree i).1]
      exact_mod_cast hil
    have hz := residualPolynomial_gradient_orthogonal base hb g hg hm.le hdeg
    rw [M.evaluate_orthogonalPolynomial] at hz
    rw [hz, zero_smul]
  · simp

/-- The actual computed CG residual is the normalized actual leading Jacobi determinant of its gradient spectral measure.
Use: provides the measured determinant formula required for the Gaussian inverse-error interpretation.
Article: main_krylov, prop:dict(i), r_m(t)=det(T_m−tI)/det T_m.
Proof: the already proved normalized-continuant identity identifies the actual
orthogonal polynomial; evaluation at zero fixes its unique normalization. -/
theorem residualPolynomial_leading (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) {m : ℕ} (hm : m<referenceAtomCount base hb g) :
    let J := (gradientSpectralData base hb g hg).reconstructed
    CG.residualPolynomial (cgOperator base) g m=C ((J.data.leading m).eval 0)⁻¹*J.data.leading m := by
  -- Normalization is fixed by the computed r_m(0)=1, so no nonzero determinant is assumed.
  dsimp only
  let M := gradientSpectralData base hb g hg
  have hmM : m<(activeSpectralValues base hb.1 g).card := by rwa [gradientSpectralData_count]
  obtain ⟨c, hc⟩ := residualPolynomial_orthogonal_factor base hb g hg hm
  rw [← normalizedLeading_eq_orthogonalPolynomial M ⟨m, hmM⟩, normalizedLeading, smul_eq_C_mul, ← mul_assoc,
    ← C_mul] at hc
  have h0 := congrArg (fun p : ℝ[X] => p.eval 0) hc
  rw [CG.residualPolynomial_zero, eval_mul, eval_C] at h0
  have hp : (M.reconstructed.data.leading m).eval 0≠0 := by intro h; rw [h, mul_zero] at h0; exact one_ne_zero h0
  have hscale : c*(M.reconstructed.data.linkProduct m)⁻¹=((M.reconstructed.data.leading m).eval 0)⁻¹ := by
    apply (mul_left_inj' hp).mp
    rw [inv_mul_cancel₀ hp]
    exact h0.symm
  rw [hc, hscale]

end
end krylov.Reference
