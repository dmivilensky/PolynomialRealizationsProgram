import jacobi.Continuum.Moments
import chebyshev2.Continuum.SpectralPerturbation

/-!
Article: jacobi, Lemma 1.3.
Mass, the largest eigenvalue and the second moment are controlled by the same
spectral l1 distance. For actual densities this distance is bounded by their
L1 difference, reusing the trace-bound and spectral perturbation theory of
chebyshev2. Source: trace-class spectral perturbation and elementary l1 estimates.
Use: one common error controls every constraint in the moment Transfer theorem.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory chebyshev2.Continuum
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The spectral l1 distance between two summable real sequences.
Use: one common error controls every constraint in the moment Transfer theorem.
Article: jacobi, Appendix D.1 (lower semicontinuity).
-/
def distance (a b : ℕ → ℝ) : ℝ := ∑' j, |a j-b j|

/-- A single spectral error is no larger than the total spectral error.
Use: controls the largest eigenvalue in Transfer and compactness.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: a nonnegative summand is bounded by the convergent total sum. -/
theorem entry_distance {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (j : ℕ) :
    |a j-b j| ≤ distance a b :=
  (ha.sub hb).abs.le_tsum j (fun _ _ => abs_nonneg _)

/-- Spectral l1 distance controls the difference of masses.
Use: transfers the finite resolvent trace to the limiting spectral mass.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: apply the absolute-value triangle inequality to the summable difference. -/
theorem mass_distance {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) :
    |(∑' j, a j)-(∑' j, b j)| ≤ distance a b := by
  rw [← ha.tsum_sub hb]
  have h : ‖(∑' j : ℕ, (a j-b j))‖ ≤ ∑' j : ℕ, ‖a j-b j‖ :=
    norm_tsum_le_tsum_norm (f := fun j : ℕ => a j-b j) (ha.sub hb).norm
  simpa only [Real.norm_eq_abs, distance] using h

/-- Spectral l1 distance controls the actual quadratic spectral moment.
Use: the second-moment error in the arbitrary-spectrum Transfer theorem.
Article: jacobi, Appendix D.1 (ground parameter).
Proof: factor each difference of squares and bound each nonnegative entry by
its own total mass, then sum the resulting absolute-value estimate. -/
theorem square_distance {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    (hna : ∀ i, 0 ≤ a i) (hnb : ∀ i, 0 ≤ b i) :
    |(∑' j, a j^2)-(∑' j, b j^2)| ≤
      ((∑' j, a j)+(∑' j, b j)) * distance a b := by
  -- Keep the two actual masses; neither sequence is normalized to mass one.
  have ha2 := jacobi.Continuum.summable_powers ha hna (by decide : 0 < 2)
  have hb2 := jacobi.Continuum.summable_powers hb hnb (by decide : 0 < 2)
  calc
    _ ≤ ∑' j, |a j^2-b j^2| := mass_distance ha2 hb2
    _ ≤ ∑' j, ((∑' i, a i)+(∑' i, b i)) * |a j-b j| := by
      apply (ha2.sub hb2).abs.tsum_le_tsum _ ((ha.sub hb).abs.mul_left _)
      intro j
      have hj : a j+b j ≤ (∑' i, a i)+(∑' i, b i) :=
        add_le_add (ha.le_tsum j (fun i _ => hna i)) (hb.le_tsum j (fun i _ => hnb i))
      calc
        _ = |a j-b j| * (a j+b j) := by
          rw [show a j^2-b j^2 = (a j-b j)*(a j+b j) by ring, abs_mul,
            abs_of_nonneg (add_nonneg (hna j) (hnb j))]
        _ ≤ _ := by nlinarith [abs_nonneg (a j-b j)]
    _ = _ := tsum_mul_left

/-- The feature operator is linear under integrable density differences.
Use: applies the existing signed trace bound directly to an L1 perturbation.
Article: jacobi, Appendix D.1 (lower semicontinuity).
Proof: distribute the scalar difference in the Bochner integral and integrate it. -/
theorem densityOperator_sub {m q : ℝ → ℝ} (hm : Integrable m) (hq : Integrable q) :
    densityOperator (m-q) = densityOperator m-densityOperator q := by
  unfold densityOperator
  have he : (fun x => (m-q) x • featureProjection x) =
      (fun x => m x • featureProjection x-q x • featureProjection x) := by
    funext x
    exact sub_smul (m x) (q x) (featureProjection x)
  rw [he]
  exact integral_sub (densityOperator_integrable hm) (densityOperator_integrable hq)

/-- The actual ordered kernel spectra are Lipschitz in the L1 norm of densities.
Use: the spectral continuity step in compactness, dilation and Transfer.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: use the already proved trace-bound perturbation theorem on the same
feature Hilbert space and identify its spectra with the actual kernel spectra. -/
theorem kernel_distance {m q : ℝ → ℝ} (hm : Integrable m) (hq : Integrable q)
    (hnm : ∀ x, 0 ≤ m x) (hnq : ∀ x, 0 ≤ q x) :
    distance (kernelEigenvalue hm hnm) (kernelEigenvalue hq hnq) ≤ ∫ x, |m x-q x| := by
  -- The signed density difference gives the entire trace-bound error directly.
  have ht := densityOperator_traceBound (hm.sub hq)
  rw [densityOperator_sub hm hq] at ht
  have h := eigenvalue_l1_le_traceBound (densityOperator_isCompact hm)
    (densityOperator_isCompact hq) (densityOperator_positive hm hnm)
    (densityOperator_positive hq hnq) (densitySpectralData hm hnm) (densitySpectralData hq hnq) ht
  rw [density_kernel_eigenvalue_eq hm hnm, density_kernel_eigenvalue_eq hq hnq] at h
  exact h

/-- The largest actual eigenvalue changes by at most the density L1 distance.
Use: continuity of G_infinity under local L1 convergence and tail control.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: use the single-entry bound followed by the actual density spectral estimate. -/
theorem kernel_top_distance {m q : ℝ → ℝ} (hm : Integrable m) (hq : Integrable q)
    (hnm : ∀ x, 0 ≤ m x) (hnq : ∀ x, 0 ≤ q x) :
    |kernelEigenvalue hm hnm 0-kernelEigenvalue hq hnq 0| ≤ ∫ x, |m x-q x| :=
  (entry_distance (kernelSpectralData hm hnm).eigenvalue_summable
    (kernelSpectralData hq hnq).eigenvalue_summable 0).trans (kernel_distance hm hq hnm hnq)

/-- The actual second moment obeys the printed L1 continuity estimate at arbitrary mass.
Use: the second spectral constraint survives the compactness limit.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: combine the spectral moment estimate, the trace identities and density stability. -/
theorem kernel_square_distance {m q : ℝ → ℝ} (hm : Integrable m) (hq : Integrable q)
    (hnm : ∀ x, 0 ≤ m x) (hnq : ∀ x, 0 ≤ q x) :
    |(∑' j, kernelEigenvalue hm hnm j^2)-(∑' j, kernelEigenvalue hq hnq j^2)| ≤
      ((∫ x, m x)+(∫ x, q x)) * ∫ x, |m x-q x| := by
  -- Sorting preserves the trace, so the spectral modulus uses these densities' actual masses.
  have h := square_distance (kernelSpectralData hm hnm).eigenvalue_summable
    (kernelSpectralData hq hnq).eigenvalue_summable
    (kernelSpectralData hm hnm).eigenvalue_nonneg (kernelSpectralData hq hnq).eigenvalue_nonneg
  change |(∑' j, kernelEigenvalue hm hnm j^2)-(∑' j, kernelEigenvalue hq hnq j^2)| ≤
    ((∑' j, kernelEigenvalue hm hnm j)+(∑' j, kernelEigenvalue hq hnq j)) *
      distance (kernelEigenvalue hm hnm) (kernelEigenvalue hq hnq) at h
  rw [kernelEigenvalue_mass hm hnm, kernelEigenvalue_mass hq hnq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (kernel_distance hm hq hnm hnq)
    (add_nonneg (integral_nonneg hnm) (integral_nonneg hnq)))

end
end jacobi.Variational
