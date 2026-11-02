import jacobi.Variational.TopPerturbation

/-!
Article: jacobi, Appendix D.1 (ground parameter).
Every nonzero nonnegative L1 source has a genuine bounded continuous gradient.
For every admissible signed L1 perturbation its actual leading eigenvalue
has the printed quadratic remainder with its actual spectral gap. Ground-state
normalization is eliminated explicitly. No isolation, eigenvector or derivative
hypothesis is left to an application of this theorem.
Source: the spectral-gap proof and the exact Sobolev feature form.
Use: the linear term in the actual leading-eigenvalue expansion and multiplier rule.
-/
namespace jacobi.Variational
noncomputable section
open Real MeasureTheory chebyshev2.Continuum chebyshev2.Sobolev
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The top spectral gradient expressed in a unit Sobolev ground vector.
Use: the linear term in the actual leading-eigenvalue expansion and multiplier rule.
Article: jacobi, Appendix D.1 (ground parameter).
-/
def topGradient (e : H1) (x : ℝ) : ℝ := 2*H1.rep e x^2

/-- The actual top spectral gradient is continuous and uniformly bounded.
Use: supplies regularity of the first variation required by the multiplier rule.
Article: jacobi, Appendix D.1 (ground parameter).
Proof: the Sobolev representative is continuous and its evaluation norm is at most norm(e)/sqrt(2). -/
theorem topGradient_regular (e : H1) : Continuous (topGradient e) ∧
    ∀ x, 0≤topGradient e x ∧ topGradient e x≤‖e‖^2 := by
  -- The feature normalization gives the exact uniform square bound.
  refine ⟨continuous_const.mul ((H1.continuous_rep e).pow 2),fun x => ⟨by unfold topGradient; positivity,?_⟩⟩
  have h := H1.evaluation_bound e x
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤‖e‖/sqrt 2)).mpr h
  rw [sq_abs,div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)] at hs
  change 2*H1.rep e x^2≤‖e‖^2
  linarith

/-- The literal gradient pairing equals the actual signed operator matrix element.
Use: identifies the first-order term in the abstract perturbation theorem with the article's integral.
Article: jacobi, Appendix D.1 (ground parameter).
Proof: reuse the established Sobolev density form and distribute the constant two inside the integral. -/
theorem topGradient_pairing {δ : ℝ → ℝ} (hδ : Integrable δ) (e : H1) :
    inner ℝ e (densityOperator δ e)=∫ x, topGradient e x*δ x := by
  rw [sobolevDensityOperator_quadratic hδ,← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by dsimp only [topGradient]; ring

/-- The unit-vector expression equals the article's normalization-independent formula.
Use: the variation theorem may be read with exactly the printed ground-state gradient.
Article: jacobi, Appendix D.1 (ground parameter).
Proof: the unit ground eigenvalue equation gives integral m e²=lambda_1/2;
positivity of the leading eigenvalue licenses cancellation. -/
theorem topGradient_formula (m : L1Source) (hm : 0<m.mass) {e : H1} (he : ‖e‖=1)
    (hTe : densityOperator m.value e=m.spectrum 0 • e) (x : ℝ) :
    topGradient e x=m.spectrum 0*H1.rep e x^2/(∫ y, m.value y*H1.rep e y^2) := by
  -- All denominator information comes from the actual eigenvector equation.
  have h := sobolevDensityOperator_quadratic m.integrable e
  rw [hTe,real_inner_smul_right,real_inner_self_eq_norm_sq,he] at h
  have hp : 0<m.spectrum 0 := (chebyshev2.GroundState.top_density_attained m.integrable m.nonneg hm).1
  have hi : (∫ y, m.value y*H1.rep e y^2)=m.spectrum 0/2 := by linarith [h]
  rw [hi,topGradient]
  field_simp [hp.ne']

/-- The full actual-density leading-eigenvalue expansion, with all spectral premises proved.
Use: establishes the first-variation and quadratic-remainder input to the top-constraint multiplier rule.
Article: jacobi, Appendix D.1 (ground parameter).
Proof: construct the simple actual top gap, apply the quantitative operator
lemma to K_(q-m), use its L1 norm bound and identify both actual sorted spectra. -/
theorem top_variation (m : L1Source) (hm : 0<m.mass) :
    ∃ e : H1, ‖e‖=1 ∧ densityOperator m.value e=m.spectrum 0 • e ∧
      0<m.spectrum 0-m.spectrum 1 ∧ Continuous (topGradient e) ∧
      (∀ x, 0≤topGradient e x ∧ topGradient e x≤1) ∧
      ∀ q : L1Source, (∫ x, |q.value x-m.value x|)≤(m.spectrum 0-m.spectrum 1)/4 →
        |q.spectrum 0-m.spectrum 0-(∫ x, topGradient e x*(q.value x-m.value x))|≤
          2*(∫ x, |q.value x-m.value x|)^2/(m.spectrum 0-m.spectrum 1) := by
  -- The real spectral gap is constructed for this density and never assumed.
  obtain ⟨e,he,hTe,hgap,hcomp⟩ := density_top_gap m hm
  refine ⟨e,he,hTe,hgap,(topGradient_regular e).1,?_,?_⟩
  · simpa only [he,one_pow] using (topGradient_regular e).2
  · intro q hsmall
    let D := densitySpectralData m.integrable m.nonneg
    let Q := densitySpectralData q.integrable q.nonneg
    have hD : D.eigenvalue=m.spectrum := density_kernel_eigenvalue_eq m.integrable m.nonneg D
    have hQ : Q.eigenvalue=q.spectrum := density_kernel_eigenvalue_eq q.integrable q.nonneg Q
    have hsum : densityOperator q.value=densityOperator m.value+densityOperator (q.value-m.value) := by
      rw [densityOperator_sub q.integrable m.integrable]
      abel
    have hs := (densityOperator_positive q.integrable q.nonneg).isSymmetric.sub
      (densityOperator_positive m.integrable m.nonneg).isSymmetric
    have hB : (densityOperator (q.value-m.value)).IsSymmetric := by
      rwa [densityOperator_sub q.integrable m.integrable]
    have hn : 0≤m.spectrum 1 := (kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg 1
    have h := top_eigenvalue_expansion D Q hsum
      (densityOperator_positive m.integrable m.nonneg).isSymmetric hB he
      (by simpa only [hD] using hTe) hgap
      (by rw [hD]; linarith)
      (by simpa only [Pi.sub_apply] using densityOperator_norm (q.value-m.value)) hsmall
      (by intro h hh; rw [hD]; convert hcomp h hh using 1; ring)
    rw [hD,hQ,topGradient_pairing (q.integrable.sub m.integrable)] at h
    change 0≤q.spectrum 0-m.spectrum 0-(∫ x, topGradient e x*(q.value x-m.value x)) ∧ _ at h
    rw [abs_of_nonneg h.1]
    exact h.2

end
end jacobi.Variational
