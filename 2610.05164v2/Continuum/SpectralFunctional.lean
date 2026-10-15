import «2610.05164v2».Continuum.Fredholm
import «2610.05164v2».Continuum.MatrixSpectrum

/-!
Article: 2610.05164v2, Proposition 3.
Sorting, including zero padding, preserves nonnegative spectral functions which vanish at zero.
Use: `«2610.05164v2».Continuum.PositiveSpectralData.logDeterminant_eq` feeds
`«2610.05164v2».Continuum.matrix_logDeterminant` (The literal finite determinant equals the same
sorted spectral product used for the infinite-dimensional Fredholm determinant).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` — 2610.05164v2,
Theorem 3.4; Signed determinant and square-trace comparisons.
Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory. The needed
form is proved here.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open Real
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} {a : ι → ℝ}

/--
Sorting, including zero padding, preserves nonnegative spectral functions which vanish at zero.
No injectivity or simplicity of the spectrum is needed.

Exact identity `(∑' n, f (spectralSorted ha n)) = ∑' i, f (a i)`.

Use: `«2610.05164v2».Continuum.spectralSorted_logDeterminant` uses this identity to establish
exact identity `logDeterminant (spectralSorted ha) s = ∑' i, log (1+s/2*a i)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem spectralSorted_function_tsum (ha : Summable a) (hn : ∀ i, 0 ≤ a i)
    {f : ℝ → ℝ} (hf0 : f 0 = 0) (hfn : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hf : Summable (fun i => f (a i)))
    (hfs : Summable (fun n => f (spectralSorted ha n))) :
    (∑' n, f (spectralSorted ha n)) = ∑' i, f (a i) := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  have he (n : ℕ) : (∑ i ∈ spectralSelected ha n, f (a i)) =
      ∑ j ∈ Finset.range n, f (spectralSorted ha j) := by
    induction n with
    | zero => simp [spectralSelected]
    | succ n ih =>
      rw [Finset.sum_range_succ, spectralSelected]
      cases h : spectralNext ha (spectralSelected ha n) with
      | none => simp only [ih, spectralSorted, h, Option.elim_none, hf0, add_zero]
      | some i =>
        rw [Finset.sum_insert (spectralNext_some ha h).1, ih, spectralSorted_eq ha h]
        exact add_comm _ _
  apply le_antisymm
  · apply Real.tsum_le_of_sum_range_le (fun n => hfn _ (spectralSorted_nonneg ha n))
    intro n
    rw [← he]
    exact hf.sum_le_tsum _ (fun i _ => hfn _ (hn i))
  · apply Real.tsum_le_of_sum_le (fun i => hfn _ (hn i))
    intro s
    obtain ⟨n, hcover⟩ := spectralSelected_contains_finite ha hn s
    let t := s.filter (fun i => 0 < a i)
    have ht : t ⊆ spectralSelected ha n := by
      intro i hi
      obtain ⟨his, hip⟩ := Finset.mem_filter.mp hi
      exact hcover i his hip
    have hz : (∑ i ∈ s, f (a i)) = ∑ i ∈ t, f (a i) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hit
      have hp : ¬0 < a i := fun hp => hit (Finset.mem_filter.mpr ⟨hi, hp⟩)
      rw [le_antisymm (le_of_not_gt hp) (hn i), hf0]
    rw [hz]
    calc
      _ ≤ ∑ i ∈ spectralSelected ha n, f (a i) :=
        Finset.sum_le_sum_of_subset_of_nonneg ht (fun i _ _ => hfn _ (hn i))
      _ = ∑ j ∈ Finset.range n, f (spectralSorted ha j) := he n
      _ ≤ _ := hfs.sum_le_tsum _ (fun j _ => hfn _ (spectralSorted_nonneg ha j))

/--
Exact identity `logDeterminant (spectralSorted ha) s = ∑' i, log (1+s/2*a i)`.

Use: `«2610.05164v2».Continuum.PositiveSpectralData.logDeterminant_eq` uses this identity to
establish exact identity `logDeterminant D.eigenvalue s = ∑' i, log (1+s/2*D.eig i)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.spectralSorted_function_tsum`,
`«2610.05164v2».Continuum.log_spectral_summable`,
`«2610.05164v2».Continuum.spectralSorted_summable` with the arguments shown in the proof.
-/
theorem spectralSorted_logDeterminant (ha : Summable a) (hn : ∀ i, 0 ≤ a i)
    {s : ℝ} (hs : 0 ≤ s) :
    logDeterminant (spectralSorted ha) s = ∑' i, log (1+s/2*a i) := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.spectralSorted_function_tsum`,
  -- `«2610.05164v2».Continuum.log_spectral_summable`,
  -- `«2610.05164v2».Continuum.spectralSorted_summable` with the arguments shown in the proof.
  apply spectralSorted_function_tsum ha hn (f := fun x => log (1+s/2*x))
  · simp
  · intro x hx
    exact log_nonneg (by nlinarith)
  · apply (ha.mul_left (s/2)).of_nonneg_of_le
    · intro i
      exact log_nonneg (by nlinarith [hn i])
    · intro i
      have h := log_le_sub_one_of_pos (show 0 < 1+s/2*a i by nlinarith [hn i])
      linarith
  · exact log_spectral_summable (spectralSorted_summable ha hn)
      (spectralSorted_nonneg ha) hs

/--
Exact identity `logDeterminant D.eigenvalue s = ∑' i, log (1+s/2*D.eig i)`.

Use: `«2610.05164v2».Continuum.matrix_logDeterminant` rewrites with this identity to establish
exact identity `logDeterminant (matrixSpectralData A hA).eigenvalue s = log (1+(s/2) • A).det`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.spectralSorted_logDeterminant`
with the arguments shown in the proof.
-/
theorem PositiveSpectralData.logDeterminant_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {T : E →L[ℝ] E}
    (D : PositiveSpectralData T) {s : ℝ} (hs : 0 ≤ s) :
    logDeterminant D.eigenvalue s = ∑' i, log (1+s/2*D.eig i) :=
  spectralSorted_logDeterminant D.summable D.nonneg hs

end
end «2610.05164v2».Continuum
