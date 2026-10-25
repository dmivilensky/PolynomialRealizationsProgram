import polyak.Waves.Interpolation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
Article: finite orthogonal sums of waves in the first part.
Use: the canonical realization of r weighted atoms in r complex coordinates,
regarded as a real Euclidean Hilbert space; zero weights are permitted.
Proof: the square-root weighted sampling map preserves exactly the integrals
of inner products for the corresponding finite probability spectrum.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace polyak.Waves

open Interpolation Spectral

variable {J : Type*} [Fintype J]

/-- Article: a finitely supported probability spectrum.
Use: explicit nonnegative normalized weights, with repeated atoms allowed. -/
def finiteSpectrum (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j, w j = 1) : Spectrum :=
  ⟨∑ j, (w j : ℝ≥0∞) • Measure.dirac (c j), ⟨by simp [← ENNReal.ofNNReal_finsetSum, hw]⟩⟩

/-- Article: integration against a finite spectrum.
Use: identify finite sums with the general probability-spectrum formulas.
Proof: linearity over a finite sum of scaled Dirac measures. -/
theorem finiteSpectrum_integral (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j, w j = 1)
    (f : Frequency → ℝ) :
    (∫ a, f a ∂finiteSpectrum w c hw) = ∑ j, (w j : ℝ) * f (c j) := by
  have hi (j : J) : Integrable f ((w j : ℝ≥0∞) • Measure.dirac (c j)) :=
    (integrable_dirac (by finiteness)).smul_measure (by simp)
  simpa [finiteSpectrum, integral_smul_measure, NNReal.smul_def, smul_eq_mul] using
    (integral_finsetSum_measure (s := Finset.univ) (fun j _ => hi j))

/-- Article: square-root-weighted direct sum of planar coordinates.
Use: a concrete real linear map into r complex, equivalently 2r real, coordinates. -/
def finiteLift (w : J → ℝ≥0) (c : J → Frequency) :
    C(Frequency, ℂ) →ₗ[ℝ] EuclideanSpace ℂ J where
  toFun f := WithLp.toLp 2 (fun j => Real.sqrt (w j : ℝ) • f (c j))
  map_add' f g := by
    ext j
    change Real.sqrt (w j : ℝ) • (f (c j) + g (c j)) = _
    exact smul_add _ _ _
  map_smul' a f := by
    ext j
    change Real.sqrt (w j : ℝ) • (a • f (c j)) = a • (Real.sqrt (w j : ℝ) • f (c j))
    exact smul_comm _ _ _

/-- Article: orthogonality of distinct coordinates in a finite mixture.
Use: exact weighted inner product, preserving zero weights.
Proof: sum the coordinate inner products and square each nonnegative square root. -/
theorem inner_finiteLift (w : J → ℝ≥0) (c : J → Frequency)
    (f g : C(Frequency, ℂ)) :
    inner ℝ (finiteLift w c f) (finiteLift w c g) =
      ∑ j, (w j : ℝ) * inner ℝ (f (c j)) (g (c j)) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  change inner ℝ (Real.sqrt (w j : ℝ) • f (c j))
    (Real.sqrt (w j : ℝ) • g (c j)) = _
  rw [real_inner_smul_left, inner_smul_right, ← mul_assoc,
    ← pow_two, Real.sq_sqrt (NNReal.coe_nonneg _)]

/-- Article: agreement of finite sums with general spectral realization.
Use: the same discrete spectrum, rather than an unrelated finite-dimensional model.
Proof: both inner products equal the identical weighted sum. -/
theorem inner_finiteLift_eq_lift (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j, w j = 1)
    (f g : C(Frequency, ℂ)) :
    inner ℝ (finiteLift w c f) (finiteLift w c g) =
      inner ℝ (lift (finiteSpectrum w c hw) f) (lift (finiteSpectrum w c hw) g) := by
  rw [inner_lift, finiteSpectrum_integral, inner_finiteLift]

/-- Article: squared lengths in finite and probability mixtures agree.
Proof: specialize preservation of the real inner product. -/
theorem norm_sq_finiteLift_eq_lift (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j, w j = 1)
    (f : C(Frequency, ℂ)) :
    ‖finiteLift w c f‖ ^ 2 = ‖lift (finiteSpectrum w c hw) f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_finiteLift_eq_lift]

/-- Article: finite mixtures have exactly the same R as their discrete spectrum.
Proof: preservation of squared norms of both linear differences. -/
theorem datumR_finiteLift {I : Type*} (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j, w j = 1)
    (x σ : I → C(Frequency, ℂ)) (i j : I) :
    datumR (fun k => finiteLift w c (x k)) (fun k => finiteLift w c (σ k)) i j =
      datumR (fun k => lift (finiteSpectrum w c hw) (x k))
        (fun k => lift (finiteSpectrum w c hw) (σ k)) i j := by
  simp only [datumR, ← map_sub, norm_sq_finiteLift_eq_lift w c hw]

/-- Article: finite mixtures have exactly the same T as their discrete spectrum.
Proof: preservation of inner products of gradient sums and position differences. -/
theorem datumT_finiteLift {I : Type*} (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j, w j = 1)
    (x σ : I → C(Frequency, ℂ)) (values : I → ℝ) (i j : I) :
    datumT (fun k => finiteLift w c (x k)) (fun k => finiteLift w c (σ k)) values i j =
      datumT (fun k => lift (finiteSpectrum w c hw) (x k))
        (fun k => lift (finiteSpectrum w c hw) (σ k)) values i j := by
  simp only [datumT, ← map_add, ← map_sub, inner_finiteLift_eq_lift w c hw]

/-- Article: a finite orthogonal sum of waves. Use: actual r-complex-coordinate positions. -/
def finitePosition (w : J → ℝ≥0) (c : J → Frequency) (t : ℝ) (i : Option ℕ) :
    EuclideanSpace ℂ J := finiteLift w c (positionMap t i)

/-- Article: gradients of a finite wave sum. Use: its table in the same r complex coordinates. -/
def finiteGradient (w : J → ℝ≥0) (c : J → Frequency) (m : C(Frequency, ℂ))
    (t : ℝ) (i : Option ℕ) : EuclideanSpace ℂ J := finiteLift w c (gradientMap m t i)

/-- Article: values of a finite orthogonal wave sum.
Use: an explicit finite weighted sum, with the common value parameter C. -/
def finiteValue (w : J → ℝ≥0) (c : J → Frequency) (m : C(Frequency, ℂ))
    (C t : ℝ) (i : Option ℕ) : ℝ := ∑ j, (w j : ℝ) * valueMap m C t i (c j)

/-- Article: agreement of finite values with the same discrete spectrum.
Proof: integrate explicitly over the weighted Dirac measures. -/
theorem finiteValue_eq_mixtureValue (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j, w j = 1)
    (m : C(Frequency, ℂ)) (C t : ℝ) (i : Option ℕ) :
    finiteValue w c m C t i = mixtureValue (finiteSpectrum w c hw) m C t i := by
  rw [mixtureValue, finiteSpectrum_integral]
  rfl

omit [Fintype J] in
/-- Article: the canonical finite coordinates. Proof: unfold the weighted sampling map. -/
theorem finitePosition_apply (w : J → ℝ≥0) (c : J → Frequency) (t : ℝ) (k : ℕ) (j : J) :
    finitePosition w c t (some k) j = Real.sqrt (w j : ℝ) • z t (Real.arccos (c j)) ^ k := rfl

/-- Article: finite-mixture signed lag slacks.
Use: the exact same discrete probability spectrum in the finite Euclidean realization.
Proof: preserve T and R under the weighted sampling map, then use spectralinterp. -/
theorem finite_slack (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j, w j = 1)
    (m : C(Frequency, ℂ)) (C t δ : ℝ) (j n : ℕ) :
    datumR (finitePosition w c t) (finiteGradient w c m t) (some j) (some (j + n)) +
      δ * datumT (finitePosition w c t) (finiteGradient w c m t) (finiteValue w c m C t)
        (some j) (some (j + n)) =
      (1 / 2 : ℝ) * Real.exp ((2 * j + n) * t) *
        (spectrumA (finiteSpectrum w c hw) m t n - δ * spectrumB (finiteSpectrum w c hw) m n +
          δ * C * Real.sinh (n * t)) := by
  have hval : finiteValue w c m C t = mixtureValue (finiteSpectrum w c hw) m C t :=
    funext (finiteValue_eq_mixtureValue w c hw m C t)
  rw [hval]
  unfold finitePosition finiteGradient
  rw [datumR_finiteLift w c hw, datumT_finiteLift w c hw]
  exact mixture_slack (finiteSpectrum w c hw) m C t δ j n

/-- Article: finite-mixture signed minimizer slacks.
Proof: preserve T and R and apply the exact minimizer spectral identity. -/
theorem finite_star_slack (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j, w j = 1)
    (m : C(Frequency, ℂ)) (C t δ : ℝ) (j : ℕ) :
    datumR (finitePosition w c t) (finiteGradient w c m t) none (some j) +
      δ * datumT (finitePosition w c t) (finiteGradient w c m t) (finiteValue w c m C t)
        none (some j) = (1 / 4 : ℝ) * Real.exp (2 * j * t) *
          (spectrumG (finiteSpectrum w c hw) m + δ * C) := by
  have hval : finiteValue w c m C t = mixtureValue (finiteSpectrum w c hw) m C t :=
    funext (finiteValue_eq_mixtureValue w c hw m C t)
  rw [hval]
  unfold finitePosition finiteGradient
  rw [datumR_finiteLift w c hw, datumT_finiteLift w c hw]
  exact mixture_star_slack (finiteSpectrum w c hw) m C t δ j

/-- Article: exact finite-wave norm. Use: normalization and the common growth exponent.
Proof: equality of squared norms with the same probability spectrum in L². -/
theorem norm_finitePosition (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j, w j = 1)
    (t : ℝ) (k : ℕ) : ‖finitePosition w c t (some k)‖ = Real.exp (k * t) := by
  have hs := norm_sq_finiteLift_eq_lift w c hw (positionMap t (some k))
  change ‖finitePosition w c t (some k)‖ ^ 2 =
    ‖mixturePosition (finiteSpectrum w c hw) t (some k)‖ ^ 2 at hs
  rw [norm_mixturePosition] at hs
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hs

/-- Article: r planar atoms occupy 2r real dimensions.
Use: exact real dimension of the canonical finite-mixture realization.
Proof: the real/complex dimension tower and the Euclidean complex dimension. -/
theorem finiteMixture_real_finrank :
    Module.finrank ℝ (EuclideanSpace ℂ J) = 2 * Fintype.card J := by
  rw [finrank_real_of_complex, finrank_euclideanSpace]

/-- Article: finite-sum spectral interpolation.
Use: one genuine function in r complex coordinates interpolates every time index
iff the discrete spectrum is feasible; no time-horizon bound is introduced.
Proof: exact T/R preservation, the discrete-spectrum equivalence, and Hilbert interpolation. -/
theorem finite_interpolation_iff (w : J → ℝ≥0) (c : J → Frequency) (hw : ∑ j, w j = 1)
    (m : C(Frequency, ℂ)) (C t : ℝ) :
    (∃ ψ : EuclideanSpace ℂ J → ℝ, polyak.NormalizedSmooth ψ ∧ ∀ i,
      ψ (finitePosition w c t i) = finiteValue w c m C t i ∧
        _root_.gradient ψ (finitePosition w c t i) = finiteGradient w c m t i) ↔
      MixtureFeasible (finiteSpectrum w c hw) m C t := by
  simp only [finiteValue_eq_mixtureValue w c hw]
  have hx : finitePosition w c t none = 0 := by
    have he : positionMap t none = 0 := by ext a; rfl
    simp [finitePosition, he]
  have hσ : finiteGradient w c m t none = 0 := by
    have he : gradientMap m t none = 0 := by ext a; simp [gradientMap, positionMap, position]
    simp [finiteGradient, he]
  rw [interpolation_iff none hx hσ (mixtureValue_none _ _ _ _)]
  rw [← mixture_tableFeasible_iff]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro j
  unfold finitePosition finiteGradient
  rw [datumT_finiteLift w c hw, datumR_finiteLift w c hw]
  rfl

end polyak.Waves
