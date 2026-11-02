import jacobi.Variational.Truncation
import chebyshev2.GroundState.Variational

/-!
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
All ordered eigenvalues are monotone in the density. A bounded positive
perturbation changes the top eigenvalue by at most twice its density bound.
This proves the article's M/R tail estimate using the existing literal H1
representation, without introducing an unproved convolution operator norm.
Source: the variational principle proved in chebyshev2, Theorem 3.1.
Use: positivity of spectral truncation errors and of spectral observations.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real chebyshev2.Continuum chebyshev2.Sobolev
open chebyshev2.GroundState
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Pointwise ordering of densities orders every actual eigenvalue.
Use: positivity of spectral truncation errors and of spectral observations.
Article: jacobi, Lemma D.1.
Proof: compare the actual H1 quadratic forms and reuse the proved min-max order theorem. -/
theorem Density.spectrum_mono (m q : Density) (hmq : ∀ x, m.value x ≤ q.value x) (j : ℕ) :
    m.spectrum j ≤ q.spectrum j := by
  -- The H1 form and the feature operator are the same already verified operator.
  let Dm := densitySpectralData m.integrable m.nonneg
  let Dq := densitySpectralData q.integrable q.nonneg
  have h := eigenvalue_mono Dm Dq (fun u => by
    rw [sobolevDensityOperator_quadratic m.integrable,sobolevDensityOperator_quadratic q.integrable]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    exact integral_mono (weighted_square_integrable m.integrable u)
      (weighted_square_integrable q.integrable u)
      (fun x => mul_le_mul_of_nonneg_right (hmq x) (sq_nonneg _))) j
  simpa only [density_kernel_eigenvalue_eq m.integrable m.nonneg Dm,
    density_kernel_eigenvalue_eq q.integrable q.nonneg Dq,L1Source.spectrum] using h

/-- A bounded density difference gives an explicit upper bound for the H1 form difference.
Use: the quantitative upper half of the spectral truncation estimate.
Article: jacobi, Lemma D.1.
Proof: integrate (m-q)u²≤Bu² and bound the L2 term by the full H1 norm squared. -/
theorem density_form_difference_le (m q : Density) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, m.value x-q.value x ≤ B) (u : H1) :
    inner ℝ u (densityOperator m.value u) ≤
      inner ℝ u (densityOperator q.value u)+2*B*‖u‖^2 := by
  -- The derivative term in the H1 norm is nonnegative, so only the L2 part is needed.
  have hi := (H1.regular u).value_memLp.integrable_sq
  have h := integral_mono (weighted_square_integrable m.integrable u)
    ((weighted_square_integrable q.integrable u).add (hi.const_mul B))
    (fun x => show m.value x*H1.rep u x^2 ≤ q.value x*H1.rep u x^2+B*H1.rep u x^2 by
      nlinarith [mul_le_mul_of_nonneg_right (hb x) (sq_nonneg (H1.rep u x))])
  have he := integral_add (weighted_square_integrable q.integrable u) (hi.const_mul B)
  change (∫ x, m.value x*H1.rep u x^2) ≤
    ∫ x, q.value x*H1.rep u x^2+B*H1.rep u x^2 at h
  rw [he,integral_const_mul] at h
  have hl2 : (∫ x, H1.rep u x^2) ≤ ‖u‖^2 := by
    rw [H1.norm_sq_energy]
    exact le_add_of_nonneg_left (integral_nonneg (fun x => sq_nonneg (H1.slope u x)))
  rw [sobolevDensityOperator_quadratic m.integrable,sobolevDensityOperator_quadratic q.integrable]
  nlinarith [mul_le_mul_of_nonneg_left hl2 hB]

/-- The actual top eigenvalue is Lipschitz for bounded nonnegative density perturbations.
Use: removes tails without requiring their L1 masses to tend uniformly to zero.
Article: jacobi, Lemma D.1.
Proof: positivity gives the lower bound; test the form comparison on an attained
unit top eigenvector, treating the zero-mass case separately. -/
theorem top_difference_of_uniform_bound (m q : Density) {B : ℝ} (hB : 0 ≤ B)
    (hn : ∀ x, q.value x ≤ m.value x) (hb : ∀ x, m.value x-q.value x ≤ B) :
    0 ≤ m.spectrum 0-q.spectrum 0 ∧ m.spectrum 0-q.spectrum 0 ≤ 2*B := by
  -- The zero spectrum needs no eigenvector; every nonzero positive trace has a maximizer.
  refine ⟨sub_nonneg.mpr (q.spectrum_mono m hn 0), ?_⟩
  by_cases hp : 0 < m.mass
  · obtain ⟨_,u,hu,he⟩ := top_density_attained m.integrable m.nonneg hp
    have hf := density_form_difference_le m q hB hb u
    have hq := (densitySpectralData q.integrable q.nonneg).top_quadratic_bound u
    rw [density_kernel_eigenvalue_eq] at hq
    rw [he,real_inner_smul_right,real_inner_self_eq_norm_sq,hu] at hf
    rw [hu] at hq
    change m.spectrum 0*1^2 ≤ inner ℝ u (densityOperator q.value u)+2*B*1^2 at hf
    change inner ℝ u (densityOperator q.value u) ≤ q.spectrum 0*1^2 at hq
    nlinarith
  · have hm := (kernelSpectralData m.integrable m.nonneg).eigenvalue_summable.le_tsum 0
      (fun i _ => (kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg i)
    change m.spectrum 0 ≤ ∑' i, kernelEigenvalue m.integrable m.nonneg i at hm
    rw [kernelEigenvalue_mass] at hm
    have hq := (kernelSpectralData q.integrable q.nonneg).eigenvalue_nonneg 0
    change 0 ≤ q.spectrum 0 at hq
    change ¬ 0 < (∫ x, m.value x) at hp
    linarith

/-- The printed top-eigenvalue tail bound for symmetric decreasing densities.
Use: global convergence of G_∞ from local L1 convergence in Compactness.
Article: jacobi, Lemma D.1.
Proof: the removed tail is bounded by M/(2R), and the H1 form costs a factor two. -/
theorem top_truncation_bound (m : Density) (hs : SymmetricDecreasing m.value)
    {M R : ℝ} (hM : m.mass ≤ M) (hR : 0 < R) :
    0 ≤ observe m .top-observe (m.truncate R) .top ∧
      observe m .top-observe (m.truncate R) .top ≤ M/R := by
  have hM0 : 0 ≤ M := (integral_nonneg m.nonneg).trans hM
  have h := top_difference_of_uniform_bound m (m.truncate R) (B := M/(2*R))
    (by positivity) (m.truncate_le R) (truncation_tail_bound m hs hM hR)
  have he : 2*(M/(2*R)) = M/R := by ring
  simpa only [he,observe] using h

end
end jacobi.Variational
