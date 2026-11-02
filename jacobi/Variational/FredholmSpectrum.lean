import jacobi.Variational.FredholmScalar
import jacobi.Variational.SpectralOrder

/-!
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
This is the regularized determinant with the article's negative spectral
parameter, including infinity at every spectral pole. The estimates concern
actual spectra of the existing compact positive operators.
Source: summable spectral functional calculus and the scalar mean value theorem.
Use: defines the Fredholm relaxation even for supercritical densities.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set chebyshev2.Continuum
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Extended regularized logarithm, retaining the true spectral pole.
Use: defines the Fredholm relaxation even for supercritical densities.
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
-/
def fredholmTerm (s x : ℝ) : ℝ≥0∞ :=
  if 1 ≤ s*x then ∞ else ENNReal.ofReal (fredholmLog s x)

/-- The regularized logarithmic determinant of a spectral sequence.
Use: the same functional defines edge thresholds and actual density constraints.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def fredholmSpectrum (s : ℝ) (a : ℕ → ℝ) : ℝ≥0∞ := ∑' j, fredholmTerm s (a j)

/-- A uniform spectral pole margin guarantees absolute convergence of the real series.
Use: legitimizes subtraction and comparison of subcritical Fredholm observations.
Article: jacobi, Lemma D.1.
Proof: the scalar Lipschitz bound against zero is dominated by a summable multiple of a. -/
theorem fredholmLog_summable {ι : Type*} {s ε : ℝ} {a : ι → ℝ} (hs : 0 ≤ s) (hε : 0 < ε)
    (ha : Summable a) (hn : ∀ j, 0 ≤ a j) (hp : ∀ j, s*a j ≤ 1-ε) :
    Summable (fun j => fredholmLog s (a j)) := by
  apply Summable.of_nonneg_of_le (fun j => fredholmLog_nonneg (by linarith [hp j]))
    _ (ha.mul_left (s/ε))
  intro j
  have hz : s*0 ≤ 1-ε := by nlinarith [mul_nonneg hs (hn j),hp j]
  have h := fredholmLog_lipschitz hs hε (hn j) le_rfl (hp j) hz
  have hj : 0 ≤ fredholmLog s (a j) := fredholmLog_nonneg (by linarith [hp j])
  simpa only [fredholmLog_zero,sub_zero,abs_of_nonneg (hn j),
    abs_of_nonneg hj] using h

/-- Below the pole, the extended determinant is exactly the convergent real sum.
Use: connects all quantitative real estimates with the extended variational domain.
Article: jacobi, Lemma D.1.
Proof: every term uses its subcritical branch, and ofReal commutes with the summable sum. -/
theorem fredholmSpectrum_eq {s ε : ℝ} {a : ℕ → ℝ} (hs : 0 ≤ s) (hε : 0 < ε)
    (ha : Summable a) (hn : ∀ j, 0 ≤ a j) (hp : ∀ j, s*a j ≤ 1-ε) :
    fredholmSpectrum s a = ENNReal.ofReal (∑' j, fredholmLog s (a j)) := by
  unfold fredholmSpectrum
  have he (j : ℕ) : fredholmTerm s (a j)=ENNReal.ofReal (fredholmLog s (a j)) := by
    exact ite_eq_right (by linarith [hp j])
  simp only [he]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun j => fredholmLog_nonneg (by linarith [hp j]))
    (fredholmLog_summable hs hε ha hn hp)).symm

/-- A single spectral pole makes the full observation infinite.
Use: no finite real logarithm is substituted for the divergent branch.
Article: jacobi, Lemma D.1.
Proof: one infinite nonnegative summand forces its whole sum to be infinite. -/
theorem fredholmSpectrum_eq_top {s : ℝ} {a : ℕ → ℝ} {j : ℕ} (hj : 1 ≤ s*a j) :
    fredholmSpectrum s a = ∞ := by
  apply top_unique
  have h := ENNReal.le_tsum (f := fun k => fredholmTerm s (a k)) j
  change fredholmTerm s (a j) ≤ fredholmSpectrum s a at h
  rwa [fredholmTerm,ite_eq_left hj] at h

/-- Spectral l1 stability of the real regularized determinant, away from poles.
Use: the Fredholm observation error in the arbitrary-spectrum Transfer theorem.
Article: jacobi, Lemma D.1.
Proof: subtract absolutely convergent series and sum the proved scalar Lipschitz estimate. -/
theorem fredholmSpectrum_distance {s ε : ℝ} {a b : ℕ → ℝ} (hs : 0 ≤ s) (hε : 0 < ε)
    (ha : Summable a) (hb : Summable b) (hna : ∀ j, 0 ≤ a j) (hnb : ∀ j, 0 ≤ b j)
    (hpa : ∀ j, s*a j ≤ 1-ε) (hpb : ∀ j, s*b j ≤ 1-ε) :
    |(∑' j, fredholmLog s (a j))-(∑' j, fredholmLog s (b j))| ≤ (s/ε)*distance a b := by
  have hfa := fredholmLog_summable hs hε ha hna hpa
  have hfb := fredholmLog_summable hs hε hb hnb hpb
  calc
    _ ≤ ∑' j, |fredholmLog s (a j)-fredholmLog s (b j)| := mass_distance hfa hfb
    _ ≤ ∑' j, (s/ε)*|a j-b j| := (hfa.sub hfb).abs.tsum_le_tsum
      (fun j => fredholmLog_lipschitz hs hε (hna j) (hnb j) (hpa j) (hpb j))
      ((ha.sub hb).abs.mul_left _)
    _ = _ := tsum_mul_left

/-- Ordered spectra admit a stronger second-moment modulus.
Use: Fredholm tails vanish uniformly even when their density masses do not.
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
Proof: sum the quadratic scalar secant bound over all eigenvalues. -/
theorem fredholmSpectrum_order_bound {s ε : ℝ} {a b : ℕ → ℝ}
    (hs : 0 ≤ s) (hε : 0 < ε) (ha : Summable a) (hb : Summable b)
    (hna : ∀ j, 0 ≤ a j) (hnb : ∀ j, 0 ≤ b j) (hba : ∀ j, b j ≤ a j)
    (hp : ∀ j, s*a j ≤ 1-ε) :
    0 ≤ (∑' j, fredholmLog s (a j))-(∑' j, fredholmLog s (b j)) ∧
    (∑' j, fredholmLog s (a j))-(∑' j, fredholmLog s (b j)) ≤
      (s^2/(2*ε))*((∑' j, a j^2)-(∑' j, b j^2)) := by
  -- Ordering keeps both spectra in the same subcritical interval.
  have hpb (j : ℕ) : s*b j ≤ 1-ε := (mul_le_mul_of_nonneg_left (hba j) hs).trans (hp j)
  have hfa := fredholmLog_summable hs hε ha hna hp
  have hfb := fredholmLog_summable hs hε hb hnb hpb
  refine ⟨sub_nonneg.mpr (hfb.tsum_le_tsum
    (fun j => fredholmLog_mono hs (hnb j) (hba j) (by linarith [hp j])) hfa),?_⟩
  have ha2 := jacobi.Continuum.summable_powers ha hna (by decide : 0 < 2)
  have hb2 := jacobi.Continuum.summable_powers hb hnb (by decide : 0 < 2)
  rw [← hfa.tsum_sub hfb,← ha2.tsum_sub hb2,← tsum_mul_left]
  exact (hfa.sub hfb).tsum_le_tsum
    (fun j => fredholmLog_quadratic hs hε (hnb j) (hba j) (hp j))
    ((ha2.sub hb2).mul_left _)

/-- The actual density's extended regularized determinant.
Use: the common functional in Fredholm minimizers, compactness and Transfer.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
-/
def L1Source.fredholm (m : L1Source) (s : ℝ) : ℝ≥0∞ := fredholmSpectrum s m.spectrum

/-- Its real subcritical branch, used only with a proved pole margin.
Use: quantitative Fredholm stability and compactness before applying ofReal.
Article: jacobi, Appendix D.1 (strict concentration gain).
-/
def L1Source.fredholmReal (m : L1Source) (s : ℝ) : ℝ := ∑' j, fredholmLog s (m.spectrum j)

/-- A top-eigenvalue margin controls every eigenvalue in the ordered spectrum.
Use: every later subcritical estimate needs only the single printed pole condition.
Article: jacobi, Lemma D.1.
Proof: the actual positive compact spectrum is antitone. -/
theorem L1Source.spectral_margin (m : L1Source) {s ε : ℝ} (hs : 0 ≤ s)
    (hp : s*observe m .top ≤ 1-ε) (j : ℕ) : s*m.spectrum j ≤ 1-ε :=
  (mul_le_mul_of_nonneg_left ((kernelSpectralData m.integrable m.nonneg).eigenvalue_antitone
    (Nat.zero_le j)) hs).trans hp

/-- Exact agreement of the extended density functional with its real subcritical branch.
Use: transports scalar spectral estimates to the actual variational constraint.
Article: jacobi, Lemma D.1.
Proof: the top margin bounds every term and the real series is summable. -/
theorem L1Source.fredholm_eq (m : L1Source) {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε)
    (hp : s*observe m .top ≤ 1-ε) : m.fredholm s = ENNReal.ofReal (m.fredholmReal s) :=
  fredholmSpectrum_eq hs hε (kernelSpectralData m.integrable m.nonneg).eigenvalue_summable
    (kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg (m.spectral_margin hs hp)

/-- L1 stability of actual subcritical density determinants.
Use: local L1 convergence handles the truncated Fredholm observations.
Article: jacobi, Lemma D.1.
Proof: apply the spectral Lipschitz estimate and the existing actual density l1 estimate. -/
theorem L1Source.fredholmReal_distance (m q : L1Source) {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε)
    (hpm : s*observe m .top ≤ 1-ε) (hpq : s*observe q .top ≤ 1-ε) :
    |m.fredholmReal s-q.fredholmReal s| ≤ (s/ε)*(∫ x, |m.value x-q.value x|) :=
  (fredholmSpectrum_distance hs hε (kernelSpectralData m.integrable m.nonneg).eigenvalue_summable
    (kernelSpectralData q.integrable q.nonneg).eigenvalue_summable
    (kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg
    (kernelSpectralData q.integrable q.nonneg).eigenvalue_nonneg
    (m.spectral_margin hs hpm) (q.spectral_margin hs hpq)).trans
    (mul_le_mul_of_nonneg_left (kernel_distance m.integrable q.integrable m.nonneg q.nonneg)
      (div_nonneg hs hε.le))

/-- Uniform Fredholm truncation bound under the printed spectral pole margin.
Use: the missing uniform tail estimate in Compactness (c).
Article: jacobi, Lemma D.1.
Proof: spectral ordering and the quadratic secant estimate reduce to the proved
second-moment tail bound; the resulting constant is twice as strong. -/
theorem fredholm_truncation_bound (m : Density) (hm : SymmetricDecreasing m.value)
    {s ε M R : ℝ} (hs : 0 ≤ s) (hε : 0 < ε) (hM : m.mass ≤ M) (hR : 0 < R)
    (hp : s*observe m .top ≤ 1-ε) :
    0 ≤ m.fredholmReal s-(m.truncate R).fredholmReal s ∧
    |m.fredholmReal s-(m.truncate R).fredholmReal s| ≤ (s^2*M^2/(2*ε))/R := by
  -- The same actual truncation is used for both spectral moments and the determinant.
  have h := fredholmSpectrum_order_bound hs hε
    (kernelSpectralData m.integrable m.nonneg).eigenvalue_summable
    (kernelSpectralData (m.truncate R).integrable (m.truncate R).nonneg).eigenvalue_summable
    (kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg
    (kernelSpectralData (m.truncate R).integrable (m.truncate R).nonneg).eigenvalue_nonneg
    ((m.truncate R).spectrum_mono m (m.truncate_le R)) (m.spectral_margin hs hp)
  change 0 ≤ m.fredholmReal s-(m.truncate R).fredholmReal s ∧
    m.fredholmReal s-(m.truncate R).fredholmReal s ≤
      (s^2/(2*ε))*(observe m .second-observe (m.truncate R) .second) at h
  refine ⟨h.1,?_⟩
  rw [abs_of_nonneg h.1]
  have ht := (second_truncation_bound m hm hM hR).2
  have hb := le_trans (le_abs_self _) ht
  exact h.2.trans ((mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by ring))

end
end jacobi.Variational
