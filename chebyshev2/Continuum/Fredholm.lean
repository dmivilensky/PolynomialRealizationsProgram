import chebyshev2.Continuum.ReferenceDeterminant
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
Article: chebyshev2, Theorem 2.4.
The reference infinite Fredholm product equals cosh(sqrt(s)).
Result: `chebyshev2.Continuum.reference_fredholmDeterminant` supplies the stated article
conclusion.
Source: Simon, Trace Ideals and Their Applications — Fredholm determinant product and logarithmic
trace. The needed form is proved here.
-/
namespace chebyshev2.Continuum
noncomputable section
open Real
open scoped BigOperators

/--
Fredholm determinant in the paper's spectral definition.

Use: `chebyshev2.Continuum.fredholmDeterminant_eq_exp` uses this definition to establish
exact identity `fredholmDeterminant a s = exp (logDeterminant a s)`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Continuum.reference_fredholmDeterminant`.

Source: Simon, Trace Ideals and Their Applications — Fredholm determinant product and
logarithmic trace.
-/
def fredholmDeterminant (a : ℕ → ℝ) (s : ℝ) : ℝ := ∏' j, (1+s/2*a j)

/--
The stated quantitative bound `Multipliable (fun j => 1+s/2*a j)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 2.4.

Source: Simon, Trace Ideals and Their Applications — Fredholm determinant product and
logarithmic trace.

Proof: Use the identities/estimates `chebyshev2.Continuum.log_spectral_summable` with the
arguments shown in the proof.
-/
theorem fredholmDeterminant_multipliable {a : ℕ → ℝ} (ha : Summable a) (hn : ∀ j, 0 ≤ a j)
    {s : ℝ} (hs : 0 ≤ s) : Multipliable (fun j => 1+s/2*a j) :=
  multipliable_of_summable_log (fun j => by have hj := hn j; positivity) (log_spectral_summable ha hn hs)

/--
Exact identity `fredholmDeterminant a s = exp (logDeterminant a s)`.

Use: `chebyshev2.Continuum.log_fredholmDeterminant` rewrites with this identity to
establish exact identity `log (fredholmDeterminant a s) = logDeterminant a s`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Continuum.reference_fredholmDeterminant`.

Source: Simon, Trace Ideals and Their Applications — Fredholm determinant product and
logarithmic trace.

Proof: Use the identities/estimates `chebyshev2.Continuum.log_spectral_summable` with the
arguments shown in the proof.
-/
theorem fredholmDeterminant_eq_exp {a : ℕ → ℝ} (ha : Summable a) (hn : ∀ j, 0 ≤ a j)
    {s : ℝ} (hs : 0 ≤ s) : fredholmDeterminant a s = exp (logDeterminant a s) :=
  (rexp_tsum_eq_tprod (fun j => by have hj := hn j; positivity) (log_spectral_summable ha hn hs)).symm

/--
Exact identity `log (fredholmDeterminant a s) = logDeterminant a s`.

Use: `chebyshev2.Packing.packed_fredholm_observation_distance` rewrites with this identity
to prove the bound `|log (fredholmDeterminant (packedEigenvalue J hN
ht) s)-log (cosh (sqrt s))| ≤ s/2*transferError N`.

Article: chebyshev2, Theorem 2.4 via
`chebyshev2.Packing.packed_fredholm_observation_distance`.

Source: Simon, Trace Ideals and Their Applications — Fredholm determinant product and
logarithmic trace.

Proof: Use the identities/estimates `chebyshev2.Continuum.fredholmDeterminant_eq_exp` with
the arguments shown in the proof.
-/
theorem log_fredholmDeterminant {a : ℕ → ℝ} (ha : Summable a) (hn : ∀ j, 0 ≤ a j)
    {s : ℝ} (hs : 0 ≤ s) : log (fredholmDeterminant a s) = logDeterminant a s := by rw [fredholmDeterminant_eq_exp ha hn hs,log_exp]

/--
The reference infinite Fredholm product equals cosh(sqrt(s)).

Exact identity `fredholmDeterminant referenceEigenvalue s = cosh (sqrt s)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 2.4.

Source: Simon, Trace Ideals and Their Applications — Fredholm determinant product and
logarithmic trace.

Proof: Use the identities/estimates `chebyshev2.Continuum.fredholmDeterminant_eq_exp`,
`chebyshev2.Continuum.summable_reference`,
`chebyshev2.Continuum.referenceEigenvalue_pos` with the arguments shown in the proof.
-/
theorem reference_fredholmDeterminant {s : ℝ} (hs : 0 ≤ s) :
    fredholmDeterminant referenceEigenvalue s = cosh (sqrt s) := by
  rw [fredholmDeterminant_eq_exp summable_reference (fun j => (referenceEigenvalue_pos j).le) hs,
    reference_logDeterminant hs,exp_log (cosh_pos _)]

end
end chebyshev2.Continuum
