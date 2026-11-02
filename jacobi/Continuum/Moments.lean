import chebyshev2.Continuum.KernelSquareIntegral
import chebyshev2.Continuum.TraceClassFeature

/-!
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
All positive integer spectral moments are traces of actual operator powers,
without the mass-one hypothesis of the earlier square-trace wrapper.
The operator, ordered spectrum, trace-class space and spectral sorting are reused
from chebyshev2. Source: Simon, Trace Ideals and Their Applications, spectral traces.
Use: makes every spectral moment and every trace power a convergent sum.
-/

namespace jacobi.Continuum
noncomputable section
open chebyshev2.Continuum MeasureTheory
open scoped InnerProductSpace BigOperators

/-- Positive powers of a nonnegative summable family are summable.
Use: makes every spectral moment and every trace power a convergent sum.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: dominate aⁿ⁺¹ by (Σa)ⁿa and use summability of the latter. -/
theorem summable_powers {ι : Type*} {a : ι → ℝ} (ha : Summable a)
    (hn : ∀ i, 0 ≤ a i) {p : ℕ} (hp : 0 < p) : Summable (fun i => a i^p) := by
  -- The total mass bounds each summand and therefore all remaining factors of its power.
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hle (i : ι) : a i ≤ ∑' j, a j := ha.le_tsum i (fun j _ => hn j)
  apply (ha.mul_left ((∑' j, a j)^n)).of_nonneg_of_le (fun i => pow_nonneg (hn i) _)
  intro i
  calc
    a i^(n+1) = a i * a i^n := by ring
    _ ≤ a i * (∑' j, a j)^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hn i) (hle i) n) (hn i)
    _ = _ := by ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A complete spectral basis diagonalizes every operator power on the same basis.
Use: constructs trace-class spectral data for a positive power without new choices.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: induction on the power, using linearity at each eigenvector. -/
theorem power_equation {T : E →L[ℝ] E} (D : PositiveSpectralData T) (p : ℕ) (i : D.Index) :
    (T^p) (D.basis i) = D.eig i^p • D.basis i := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ, mul_apply_eq_comp, D.equation, map_smul, ih, smul_smul]
    congr 1
    ring

/-- The complete spectral data of a positive integer power of a trace-class operator.
Use: applies the existing basis-independent trace theorem to Tᵖ.
Article: jacobi, Appendix D.1 (strict concentration gain).
-/
def powerData {T : E →L[ℝ] E} (D : PositiveSpectralData T) {p : ℕ} (hp : 0 < p) :
    PositiveSpectralData (T^p) where
  Index := D.Index
  basis := D.basis
  eig i := D.eig i^p
  equation := power_equation D p
  nonneg i := pow_nonneg (D.nonneg i) p
  summable := summable_powers D.summable D.nonneg hp

/-- The spectral moment is the trace of Tᵖ in every Hilbert basis, at any finite mass.
Use: identifies the continuum constraints with genuine operator traces.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: apply the existing trace theorem to the same eigenbasis with powered eigenvalues,
then use the already proved invariance of spectral sums under sorting. -/
theorem hasSum_power_trace {T : E →L[ℝ] E} (D : PositiveSpectralData T)
    {p : ℕ} (hp : 0 < p) {κ : Type*} (b : HilbertBasis κ ℝ E) :
    HasSum (fun j => inner ℝ (b j) ((T^p) (b j))) (∑' n, D.eigenvalue n^p) := by
  have h := (powerData D hp).hasSum_trace b
  have he := (spectralSorted_moment D.summable D.nonneg (fun x => x^p)
    (zero_pow hp.ne') (fun x hx => pow_nonneg hx p)
    (summable_powers D.summable D.nonneg hp)).2
  change HasSum _ (∑' i, D.eig i^p) at h
  rwa [← he] at h

/-- The density kernel has these spectral trace moments without a mass-one assumption.
Use: specializes the general trace theorem to every density allowed in the relaxation.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: use the actual kernel operator and its existing complete spectral data. -/
theorem kernel_hasSum_power_trace {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    {p : ℕ} (hp : 0 < p) {κ : Type*} (b : HilbertBasis κ ℝ FeatureSpace) :
    HasSum (fun j => inner ℝ (b j) ((kernelOperator hm hn ^ p) (b j)))
      (∑' n, kernelEigenvalue hm hn n^p) :=
  hasSum_power_trace (kernelSpectralData hm hn) hp b

end
end jacobi.Continuum
