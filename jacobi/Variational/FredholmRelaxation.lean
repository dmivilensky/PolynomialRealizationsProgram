import jacobi.Variational.FredholmSeries

/-!
Article: jacobi, Section 3.2 (sharp comparison at U).
The admissible sets use the actual extended determinant, including poles, and
the actual density energy. General moment comparison transfers to this same
functional; no separate Fredholm comparison assumption is introduced.
Use: the target observation in the general Fredholm Transfer theorem.
-/
namespace jacobi.Variational
noncomputable section
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The Fredholm threshold of an arbitrary positive summable edge spectrum.
Use: the target observation in the general Fredholm Transfer theorem.
Article: jacobi, Section 3.2 (sharp comparison at U).
-/
def EdgeSpectrum.fredholm (S : EdgeSpectrum) (s : ℝ) : ℝ≥0∞ := fredholmSpectrum s S.value

/-- The actual mass-constrained Fredholm variational infimum.
Use: common domain for the Fredholm calibration in jacobi, Appendix D.
Article: jacobi, Theorem 3.2.
-/
def fredholmInfimum (s M : ℝ) (d : ℝ≥0∞) : ℝ≥0∞ :=
  sInf (Density.cost '' {m | m.mass ≤ M ∧ d ≤ m.fredholm s})

/-- The stronger Fredholm infimum retaining exact mass and bounded root mass.
Use: the direct continuum relaxation of finite polynomial realizations.
Article: jacobi, Theorem 3.2.
-/
def rootFredholmInfimum (s M : ℝ) (d : ℝ≥0∞) : ℝ≥0∞ :=
  sInf (Density.cost '' {m | m.mass = M ∧ m.rootMass ≤ 1 ∧ d ≤ m.fredholm s})

/-- Relaxing the exact mass and root-mass constraints can only lower the Fredholm infimum.
Use: the last inequality in the Fredholm branch of Transfer.
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
Proof: every density admissible for the stronger problem is admissible for the relaxation. -/
theorem fredholm_le_root (s M : ℝ) (d : ℝ≥0∞) :
    fredholmInfimum s M d ≤ rootFredholmInfimum s M d := by
  apply sInf_le_sInf
  apply Set.image_mono
  intro m hm
  exact ⟨hm.1.le,hm.2.2⟩

/-- All positive integer moment comparisons imply Fredholm comparison, including at poles.
Use: once rearrangement is proved for the cyclic moments, its Fredholm conclusion follows here.
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
Proof: use the proved extended moment expansion and compare each nonnegative summand. -/
theorem fredholm_mono_of_moments (m q : L1Source) {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ n : ℕ, (∑' j, m.spectrum j^(n+2)) ≤ ∑' j, q.spectrum j^(n+2)) :
    m.fredholm s ≤ q.fredholm s := by
  rw [m.fredholm_series hs,q.fredholm_series hs]
  apply ENNReal.tsum_le_tsum
  intro n
  exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (h n)) (by positivity)

/-- Pointwise ordering of actual densities orders their extended Fredholm observations.
Use: monotonicity of truncated Fredholm constraints, including possible spectral poles.
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
Proof: min-max orders every eigenvalue; its positive integer powers and their sums are ordered. -/
theorem Density.fredholm_mono (m q : Density) {s : ℝ} (hs : 0 ≤ s)
    (hmq : ∀ x, m.value x ≤ q.value x) : m.fredholm s ≤ q.fredholm s := by
  -- Every moment below belongs to the actual operator spectrum, not an independently specified sequence.
  apply fredholm_mono_of_moments m q hs
  intro n
  have hm : Summable m.spectrum :=
    (chebyshev2.Continuum.kernelSpectralData m.integrable m.nonneg).eigenvalue_summable
  have hq : Summable q.spectrum :=
    (chebyshev2.Continuum.kernelSpectralData q.integrable q.nonneg).eigenvalue_summable
  have hn : ∀ j, 0 ≤ m.spectrum j :=
    (chebyshev2.Continuum.kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg
  have hp : ∀ j, 0 ≤ q.spectrum j :=
    (chebyshev2.Continuum.kernelSpectralData q.integrable q.nonneg).eigenvalue_nonneg
  exact (jacobi.Continuum.summable_powers hm hn
    (by omega : 0 < n+2)).tsum_le_tsum
    (fun j => pow_le_pow_left₀ (hn j) (m.spectrum_mono q hmq j) _)
    (jacobi.Continuum.summable_powers hq hp
      (by omega : 0 < n+2))

/-- The second moment is a genuine lower bound for the regularized determinant.
Use: the leading positive Fredholm coefficient in feasibility and dilation arguments.
Article: jacobi, Equation (3.5) (regularized Fredholm functional).
Proof: retain the zeroth summand of the proved nonnegative extended moment series. -/
theorem L1Source.fredholm_second_lower (m : L1Source) {s : ℝ} (hs : 0 ≤ s) :
    ENNReal.ofReal (s^2/2)*ENNReal.ofReal (observe m .second) ≤ m.fredholm s := by
  rw [m.fredholm_series hs]
  have h := ENNReal.le_tsum (f := fun n : ℕ => ENNReal.ofReal (s^(n+2)/((n : ℝ)+2))*
    ENNReal.ofReal (∑' j, m.spectrum j^(n+2))) 0
  simpa only [Nat.zero_add,Nat.cast_zero,zero_add,observe] using h

end
end jacobi.Variational
