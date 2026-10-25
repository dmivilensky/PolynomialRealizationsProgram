import chebyshev2.Continuum.SpectralSorting

/-!
Article: chebyshev2, Theorem 2.4.
The article's sorted continuum spectrum, including multiplicities and zeros.
Use: `chebyshev2.Continuum.kernelEigenvalue_mass` feeds
`chebyshev2.Packing.packedEigenvalue_mass` (packed Eigenvalue mass).
Proof chain: `chebyshev2.Packing.packedKernel_hasSum_square_trace` — chebyshev2, Theorem 2.4;
Uniform l1 spectral transfer, ground parameter and Fredholm/cosh observations.
-/
namespace chebyshev2.Continuum
noncomputable section
open MeasureTheory Real
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Complete actual spectral data. Existence is proved for positive compact trace-class operators
below; this is not a spectral certificate assumption.

Use: `chebyshev2.Continuum.PositiveSpectralData.eigenvalue` uses this record of data and
proof obligations in the displayed construction of `eigenvalue`. Its inputs and component
formulas are fixed by that definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
structure PositiveSpectralData (T : E →L[ℝ] E) where
  /-- Index type of the complete Hilbert eigenbasis. -/
  Index : Type u
  /-- Orthonormal complete eigenbasis of the operator. -/
  basis : HilbertBasis Index ℝ E
  /-- Nonnegative eigenvalue attached to each eigenbasis vector. -/
  eig : Index → ℝ
  /-- The operator acts on each basis vector by its stated eigenvalue. -/
  equation : ∀ i, T (basis i) = eig i • basis i
  /-- Nonnegativity of every eigenvalue, encoding operator positivity in this decomposition. -/
  nonneg : ∀ i, 0 ≤ eig i
  /-- Finite spectral sum, needed for trace and spectral-moment identities. -/
  summable : Summable eig

/--
The precise assertion is `Nonempty (PositiveSpectralData T)`.

Use: `chebyshev2.Continuum.positiveSpectralData` uses this assertion in the displayed
construction of `positiveSpectralData`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.exists_compact_eigenbasis`,
`chebyshev2.Continuum.nuclearNorm_eigenbasis` with the arguments shown in the proof.
-/
theorem exists_positiveSpectralData (T : E →L[ℝ] E) (hc : IsCompactOperator T)
    (hp : T.IsPositive) (ht : IsTraceClass T) : Nonempty (PositiveSpectralData T) := by
  -- Use the identities/estimates `chebyshev2.Continuum.exists_compact_eigenbasis`,
  -- `chebyshev2.Continuum.nuclearNorm_eigenbasis` with the arguments shown in the proof.
  obtain ⟨ι,b,eig,he⟩ := exists_compact_eigenbasis T hc hp.isSymmetric
  have hn (i : ι) : 0 ≤ eig i := by
    have h := hp.re_inner_nonneg_right (b i)
    change 0 ≤ inner ℝ (b i) (T (b i)) at h
    rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one] at h
    simpa only [one_pow,mul_one] using h
  obtain ⟨hs,_⟩ := nuclearNorm_eigenbasis b T he ht
  -- Prove the summability hs needed for the later infinite-sum manipulations.
  have hs' : Summable eig := by simpa only [abs_of_nonneg (hn _)] using hs
  exact ⟨⟨ι,b,eig,he,hn,hs'⟩⟩

/--
Defines `positiveSpectralData` of type `PositiveSpectralData T` by `Classical.choice
(exists_positiveSpectralData T hc hp ht)`.

Use: `chebyshev2.Continuum.kernelSpectralData` uses this definition in the displayed
construction of `kernelSpectralData`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def positiveSpectralData (T : E →L[ℝ] E) (hc : IsCompactOperator T)
    (hp : T.IsPositive) (ht : IsTraceClass T) : PositiveSpectralData T :=
  Classical.choice (exists_positiveSpectralData T hc hp ht)

namespace PositiveSpectralData
variable {T : E →L[ℝ] E} (D : PositiveSpectralData T)

/--
Defines `eigenvalue` of type `ℕ → ℝ` by `spectralSorted D.summable`.

Use: `chebyshev2.Continuum.kernelEigenvalue` uses this definition in the displayed
construction of `kernelEigenvalue`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def eigenvalue : ℕ → ℝ := spectralSorted D.summable

omit [CompleteSpace E] in
/--
The stated quantitative bound `0 ≤ D.eigenvalue n`.

Use: `chebyshev2.Continuum.PositiveSpectralData.eigenvalue_le_trace` uses this bound to
establish the stated quantitative bound `D.eigenvalue n ≤ ∑' i, D.eig i`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Packing.packed_fredholm_observation_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.spectralSorted_nonneg` with the
arguments shown in the proof.
-/
theorem eigenvalue_nonneg (n : ℕ) : 0 ≤ D.eigenvalue n := spectralSorted_nonneg D.summable n

omit [CompleteSpace E] in
/--
Monotonicity in decreasing order: `Antitone D.eigenvalue`.

Use: `chebyshev2.Packing.packedEigenvalue_zero_pos` uses this assertion to establish the
stated quantitative bound `0 < packedEigenvalue J hN ht 0`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `chebyshev2.Continuum.spectralSorted_antitone` with the
arguments shown in the proof.
-/
theorem eigenvalue_antitone : Antitone D.eigenvalue := spectralSorted_antitone D.summable

omit [CompleteSpace E] in
/--
Summability of the displayed sequence: `Summable D.eigenvalue`.

Use: `chebyshev2.Continuum.PositiveSpectralData.eigenvalue_le_trace` uses this summability
result to prove the bound `D.eigenvalue n ≤ ∑' i, D.eig i`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.spectralSorted_summable` with the
arguments shown in the proof.
-/
theorem eigenvalue_summable : Summable D.eigenvalue := spectralSorted_summable D.summable D.nonneg

omit [CompleteSpace E] in
/--
Exact identity `(∑' n, D.eigenvalue n) = ∑' i, D.eig i`.

Use: `chebyshev2.Continuum.PositiveSpectralData.eigenvalue_le_trace` rewrites with this
identity to prove the bound `D.eigenvalue n ≤ ∑' i, D.eig i`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Packing.packedKernel_hasSum_square_trace`.

Proof: Use the identities/estimates `chebyshev2.Continuum.spectralSorted_tsum` with the
arguments shown in the proof.
-/
theorem eigenvalue_tsum : (∑' n, D.eigenvalue n) = ∑' i, D.eig i :=
  spectralSorted_tsum D.summable D.nonneg

omit [CompleteSpace E] in
/--
Exact identity `inner ℝ (D.basis i) (T (D.basis i)) = D.eig i`.

Use: `chebyshev2.Continuum.kernelEigenvalue_mass` uses this identity to establish exact
identity `(∑' j, kernelEigenvalue hm hn j) = ∫ x, m x`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Continuum.kernelEigenvalue_square_integral`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem diagonal_eq (i : D.Index) : inner ℝ (D.basis i) (T (D.basis i)) = D.eig i := by
  rw [D.equation,real_inner_smul_right,real_inner_self_eq_norm_sq,D.basis.orthonormal.norm_eq_one]
  simp

omit [CompleteSpace E] in
/--
The stated quantitative bound `D.eigenvalue n ≤ ∑' i, D.eig i`.

Use: `chebyshev2.HalfLine.operator_norm_strict` uses this bound to establish the stated
quantitative bound `‖operator hm hn x‖ < 1/groundParameter hm hn`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates
`chebyshev2.Continuum.PositiveSpectralData.eigenvalue_tsum`,
`chebyshev2.Continuum.PositiveSpectralData.eigenvalue_summable`,
`chebyshev2.Continuum.PositiveSpectralData.eigenvalue_nonneg` with the arguments shown in
the proof.
-/
theorem eigenvalue_le_trace (n : ℕ) : D.eigenvalue n ≤ ∑' i, D.eig i := by
  rw [← D.eigenvalue_tsum]
  exact D.eigenvalue_summable.le_tsum n (fun j _ => D.eigenvalue_nonneg j)

end PositiveSpectralData

/--
The article's sorted continuum spectrum, including multiplicities and zeros.

Use: `chebyshev2.Continuum.kernelEigenvalue` uses this definition in the displayed
construction of `kernelEigenvalue`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Packing.packedKernel_hasSum_square_trace`.
-/
def kernelSpectralData {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    PositiveSpectralData (kernelOperator hm hn) :=
  positiveSpectralData _ (kernelOperator_isCompact hm hn) (kernelOperator_positive hm hn)
    (kernelOperator_isTraceClass hm hn)

/--
Defines `kernelEigenvalue` of type `ℕ → ℝ` by `(kernelSpectralData hm hn).eigenvalue`.

Use: `chebyshev2.Calibration.ReferenceData.selfConsistent_minimum` uses this definition to
establish the stated quantitative bound `ENNReal.ofReal (∫ x, (sqrt (R.density x))^3) ≤ ∫⁻ x,
ENNReal.ofReal (m x^(3/2:ℝ))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def kernelEigenvalue {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) : ℕ → ℝ :=
  (kernelSpectralData hm hn).eigenvalue

/--
Exact identity `(∑' j, kernelEigenvalue hm hn j) = ∫ x, m x`.

Use: `chebyshev2.Filters.leftLogDeterminant_bound` rewrites with this identity to establish
the stated quantitative bound `|leftLogDeterminant hm hn s x| ≤ s/2*cumulative m x`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Packing.packedKernel_hasSum_square_trace`.

Proof: Use the identities/estimates
`chebyshev2.Continuum.PositiveSpectralData.eigenvalue_tsum`,
`chebyshev2.Continuum.kernelOperator_trace`,
`chebyshev2.Continuum.PositiveSpectralData.diagonal_eq` with the arguments shown in the
proof.
-/
theorem kernelEigenvalue_mass {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    (∑' j, kernelEigenvalue hm hn j) = ∫ x, m x := by
  rw [kernelEigenvalue, PositiveSpectralData.eigenvalue_tsum]
  have h := kernelOperator_trace (kernelSpectralData hm hn).basis hm hn
  simpa only [PositiveSpectralData.diagonal_eq] using h

end
end chebyshev2.Continuum
