import krylov.Reference.GradientMeasure
import krylov.Reference.Contraction
import krylov.Reference.Exhaustion

/-!
Article: main_krylov, Section 3, the inverse-curvature Gaussian remainder.
Use: identify the actual CG energy error with the remainder of the constructed
Gaussian rule for 1/t at the actual gradient spectral measure.
Source: classical Gaussian quadrature for inverse moments (GolubMeurant10),
proved by the polynomial (1-r_m²)/t and the already proved 2m−1 exactness.
-/

namespace krylov.Reference
noncomputable section
open Matrix Polynomial jacobi.Finite krylov.Secant chebyshev1
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
variable {n : ℕ}

/-- The actual Gaussian inverse-moment approximation, with nodes and weights obtained from the leading Jacobi block.
Use: the quadrature is constructed from the measured finite spectral data.
Article: main_krylov, Section 3, the m-point Gauss rule for ∫t⁻¹dσ. -/
def gaussInverse {N : ℕ} (M : DiscreteMeasure N) (m : ℕ) (hm : 0<m) : ℝ :=
  let J := M.reconstructed.data.matrix 0 m
  let B := SpectralBasis.ofHermitian J (M.reconstructed.data.matrix_isHermitian 0 m)
  ∑ i : Fin m, B.weight ⟨0, hm⟩ i/B.eigenvalues i

/-- A normalized degree-m polynomial produces the degree-below-2m inverse interpolation polynomial.
Use: the classical inverse-moment remainder is reduced to the proved polynomial exactness theorem.
Article: main_krylov, Section 3, h(t)=(1-r_m(t)²)/t.
Proof: the zero constant term gives divisibility by X, and the exact product degree gives the required bound. -/
theorem inverse_interpolation {r : ℝ[X]} {m : ℕ} (hm : 0<m) (hd : r.natDegree≤m) (h0 : r.eval 0=1) :
    ∃ h : ℝ[X], X*h=1-r^2 ∧ h.natDegree<2*m := by
  -- Divisibility is established before the scalar expression is divided by any spectral node.
  have hdiv : X∣1-r^2 := X_dvd_iff.mpr (by simp only [coeff_zero_eq_eval_zero, eval_sub, eval_one, eval_pow, h0, one_pow, sub_self])
  obtain ⟨h, hh⟩ := hdiv
  refine ⟨h, hh.symm, ?_⟩
  by_cases hz : h=0
  · simp only [hz, natDegree_zero]
    omega
  · have hp : (1-r^2).natDegree≤2*m :=
      (natDegree_sub_le _ _).trans (max_le (by simp) ((natDegree_pow_le).trans (Nat.mul_le_mul_left 2 hd)))
    rw [hh, natDegree_mul X_ne_zero hz, natDegree_X] at hp
    omega

/-- A normalized actual leading-continuant residual vanishes at every constructed Gaussian node.
Use: the inverse interpolation polynomial equals 1/t on all quadrature nodes.
Article: main_krylov, prop:dict(i), Gaussian nodes are residual zeros.
Proof: the existing continuant/characteristic-polynomial theorem and actual spectral factorization make each node a root. -/
theorem gauss_residual_zero {N : ℕ} (M : DiscreteMeasure N) (m : ℕ)
    {r : ℝ[X]} {c : ℝ} (hr : r=C c*M.reconstructed.data.leading m) (i : Fin m) :
    r.eval ((SpectralBasis.ofHermitian (M.reconstructed.data.matrix 0 m)
      (M.reconstructed.data.matrix_isHermitian 0 m)).eigenvalues i)=0 := by
  -- The quadrature eigenvalues are roots of the actual block characteristic polynomial.
  let B := SpectralBasis.ofHermitian (M.reconstructed.data.matrix 0 m)
    (M.reconstructed.data.matrix_isHermitian 0 m)
  have hchar := M.reconstructed.data.block_eq_charpoly M.reconstructed.coupling_nonneg 0 m
  change (M.reconstructed.data.leading m)=(M.reconstructed.data.matrix 0 m).charpoly at hchar
  rw [hr, eval_mul, eval_C, hchar, B.charpoly_factor, eval_prod]
  have hz : (∏ j : Fin m, (X-C (B.eigenvalues j)).eval (B.eigenvalues i))=0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [eval_sub, eval_X, eval_C, sub_self])
  rw [hz, mul_zero]

/-- The actual Gaussian inverse-moment remainder is the residual-square inverse moment.
Use: the quadrature error is identified without an external error formula or an assumed optimizer.
Article: main_krylov, Section 3, Gaussian inverse-curvature remainder.
Proof: (1-r²)/t has degree below 2m and hence exact quadrature; r vanishes
at the constructed Gaussian nodes, and all node divisions are proved nonzero. -/
theorem gauss_inverse_remainder {N : ℕ} (M : DiscreteMeasure N) (hn : ∀ i, M.node i≠0)
    {m : ℕ} (hm : 0<m) (hmN : m≤N) {r : ℝ[X]} {c : ℝ}
    (hr : r=C c*M.reconstructed.data.leading m) (hd : r.natDegree≤m) (h0 : r.eval 0=1) :
    (∑ i, M.weight i/M.node i)-gaussInverse M m hm=
      ∑ i, M.weight i*(r.eval (M.node i))^2/M.node i := by
  -- Polynomial exactness supplies the error identity; nonzero normalization rules out a zero Gaussian node.
  obtain ⟨h, hh, hdeg⟩ := inverse_interpolation hm hd h0
  let B := SpectralBasis.ofHermitian (M.reconstructed.data.matrix 0 m)
    (M.reconstructed.data.matrix_isHermitian 0 m)
  have hnode (i : Fin m) : B.eigenvalues i≠0 := by
    intro hz
    have he := gauss_residual_zero M m hr i
    rw [show B.eigenvalues i=0 from hz, h0] at he
    exact one_ne_zero he
  have hval (t : ℝ) (ht : t≠0) : h.eval t=(1-(r.eval t)^2)/t := by
    have he := congrArg (fun p : ℝ[X] => p.eval t) hh
    simp only [eval_mul, eval_X, eval_sub, eval_one, eval_pow] at he
    exact (eq_div_iff ht).mpr ((mul_comm _ _).trans he)
  have hgauss : jacobiFunctional M.reconstructed.data m hm h=gaussInverse M m hm := by
    rw [jacobiFunctional_spectral]
    apply Finset.sum_congr rfl
    intro i _
    rw [hval _ (hnode i), gauss_residual_zero M m hr i, zero_pow (by omega : 2≠0), sub_zero, mul_one_div]
  have hexact := gauss_exact_le M hm hmN hdeg
  rw [hgauss] at hexact
  rw [hexact]
  change (∑ i, M.weight i/M.node i)-(∑ i, M.weight i*h.eval (M.node i))=_
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hval _ (hn i)]
  ring

/-- The actual CG energy is its gradient spectral residual-square inverse moment.
Use: fixes the normalization in the source's relative Gaussian remainder.
Article: main_krylov, Section 3, dσ proportional to t dν.
Proof: the genuine positive-root coordinate relation converts gradient spectral
weights divided by the eigenvalue into the actual canonical energy weights. -/
theorem cg_error_inverse_moment (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) (k : ℕ) :
    (∑ i, (gradientSpectralData base hb g hg).weight i*
      ((CG.residualPolynomial (cgOperator base) g k).eval ((gradientSpectralData base hb g hg).node i))^2/
        (gradientSpectralData base hb g hg).node i)=‖cgCanonicalError base g k‖^2/‖g‖^2 := by
  -- Grouping repeated eigenvalues does not change the true inverse-energy integral.
  let r := CG.residualPolynomial (cgOperator base) g k
  have hs := vectorSpectralData_integral base hb.1 g hg (fun t => (r.eval t)^2/t)
  simp only [← mul_div_assoc] at hs
  change (∑ i, (gradientSpectralData base hb g hg).weight i*(r.eval ((gradientSpectralData base hb g hg).node i))^2/
    (gradientSpectralData base hb g hg).node i)=_ at hs
  rw [hs, ← canonicalPolynomial_residual base g k, canonicalPolynomial_parseval base hb]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [gradient_spectral_coordinate base hb g i, mul_pow, Real.sq_sqrt (hb.eigenvalues_pos i).le]
  change hb.1.eigenvalues i*(inner ℝ (hb.1.eigenvectorBasis i) (cgCanonicalError base g 0))^2*
    (r.eval (hb.1.eigenvalues i))^2/hb.1.eigenvalues i=_
  field_simp [(hb.eigenvalues_pos i).ne']
  rfl

/-- The Gaussian inverse-moment error of the actual gradient measure is exactly the actual remaining CG energy.
Use: fixes the absolute normalization of the article's Gauss interpretation.
Article: main_krylov, Section 3, CG error as Gaussian inverse-curvature remainder.
Proof: the computed residual is the actual normalized leading determinant;
insert it in the proved Gaussian remainder identity and use the genuine inverse-energy spectral integral. -/
theorem cg_gauss_remainder (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) {m : ℕ}
    (hm : 0<m) (hmN : m≤referenceAtomCount base hb g) :
    ‖cgCanonicalError base g 0‖^2-‖g‖^2*gaussInverse (gradientSpectralData base hb g hg) m hm=
      ‖cgCanonicalError base g m‖^2 := by
  -- Both inverse moments use the same actual gradient probability normalization.
  let M := gradientSpectralData base hb g hg
  have hnodes (i) : M.node i≠0 := (vectorSpectralData_node_pos base hb g hg i).ne'
  have hdeg : m≤(activeSpectralValues base hb.1 g).card := by rwa [gradientSpectralData_count]
  have hr := residualPolynomial_leading_le base hb g hg hmN
  dsimp only at hr
  have he := gauss_inverse_remainder M hnodes hm hdeg hr
    (CG.polynomial_degree (cgOperator base) g m).1 (CG.residualPolynomial_zero (cgOperator base) g m)
  have hi := cg_error_inverse_moment base hb g hg 0
  simp only [CG.residualPolynomial, CG.polynomialRun, eval_one, one_pow, mul_one] at hi
  rw [hi, cg_error_inverse_moment base hb g hg m] at he
  have hn : ‖g‖^2≠0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
  apply (div_left_inj' hn).mp
  simpa only [sub_div, mul_div_cancel_left₀ _ hn] using he

/-- The relative Gaussian inverse-moment remainder is the actual energy Christoffel minimum.
Use: identifies precisely the coefficient of the article's later first-variation formulas.
Article: main_krylov, Section 3, relative Gauss remainder λ_m(0;ν).
Proof: combine the proved absolute Gaussian remainder with the actual CG/energy-measure Christoffel identity. -/
theorem cg_gauss_relative_remainder (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) {m : ℕ}
    (hm : 0<m) (hmN : m<referenceAtomCount base hb g) :
    (‖cgCanonicalError base g 0‖^2-‖g‖^2*gaussInverse (gradientSpectralData base hb g hg) m hm)/
      ‖cgCanonicalError base g 0‖^2=(christoffelKernel (energySpectralData base hb g hg) m 0)⁻¹ := by
  have hn : ‖cgCanonicalError base g 0‖^2≠0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (cgCanonicalError_initial_ne_zero base hb g hg))
  rw [cg_gauss_remainder base hb g hg hm hmN.le, cg_energy_christoffel base hb g hg hmN,
    mul_div_cancel_left₀ _ hn]

/-- The complete relative Gaussian inverse-moment identity includes the zero terminal remainder.
Use: the actual quadrature/CG dictionary holds through every positive degree up to the active atom count.
Article: main_krylov, Section 3 and lem:chris, the complete relative Gaussian remainder.
Proof: divide the actual absolute remainder by its positive initial energy and apply the all-degree Christoffel profile. -/
theorem cg_gauss_relative_remainder_le (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) {m : ℕ}
    (hm : 0<m) (hmN : m≤referenceAtomCount base hb g) :
    (‖cgCanonicalError base g 0‖^2-‖g‖^2*gaussInverse (gradientSpectralData base hb g hg) m hm)/
      ‖cgCanonicalError base g 0‖^2=finiteChristoffelValue (energySpectralData base hb g hg) m := by
  have hn : ‖cgCanonicalError base g 0‖^2≠0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (cgCanonicalError_initial_ne_zero base hb g hg))
  rw [cg_gauss_remainder base hb g hg hm hmN, cg_energy_christoffel_all base hb g hg m,
    mul_div_cancel_left₀ _ hn]

end
end krylov.Reference
