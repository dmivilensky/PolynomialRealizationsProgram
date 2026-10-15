import «2610.05164v2».Continuum.SpectralTrace

/-!
Article: 2610.05164v2, Theorem 2.4.
The spectral square sum is the trace of the actual composed operator in every Hilbert basis.
Use: `«2610.05164v2».Continuum.PositiveSpectralData.hasSum_square_trace` feeds
`«2610.05164v2».Packing.packedKernel_hasSum_square_trace` (The quadratic observation is the trace of
the actual squared integral operator in every Hilbert basis).
Proof chain: `«2610.05164v2».Packing.packedKernel_hasSum_square_trace` — 2610.05164v2, Theorem 2.4;
Uniform l1 spectral transfer, ground parameter and Fredholm/cosh observations.
Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory. The needed
form is proved here.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open Set
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} {a : ι → ℝ}

/--
Exact identity `(∑ i ∈ spectralSelected hs n, φ (a i)) = ∑ j ∈ Finset.range n, φ
(spectralSorted hs j)`.

Use: `«2610.05164v2».Continuum.spectralSorted_moment` rewrites with this identity to establish
summability of the displayed sequence: `Summable (fun n => φ (spectralSorted hs n)) ∧ (∑' n, φ
(spectralSorted hs n)) = ∑' i, φ (a i)`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem spectralSelected_sum_map (hs : Summable a) (φ : ℝ → ℝ) (hφ : φ 0 = 0) (n : ℕ) :
    (∑ i ∈ spectralSelected hs n, φ (a i)) = ∑ j ∈ Finset.range n, φ (spectralSorted hs j) := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => simp [spectralSelected]
  | succ n ih =>
    rw [Finset.sum_range_succ,spectralSelected]
    cases h : spectralNext hs (spectralSelected hs n) with
    | none => simp only [ih,spectralSorted,h,Option.elim_none,hφ,add_zero]
    | some i =>
      rw [Finset.sum_insert (spectralNext_some hs h).1,ih,spectralSorted_eq hs h]
      exact add_comm _ _

/--
Sorting preserves every summable nonnegative spectral moment.

Summability of the displayed sequence: `Summable (fun n => φ (spectralSorted hs n)) ∧ (∑' n, φ
(spectralSorted hs n)) = ∑' i, φ (a i)`.

Use: `«2610.05164v2».Continuum.PositiveSpectralData.hasSum_square_trace` uses this summability
result to establish the value of a convergent infinite sum: `HasSum (fun j => inner ℝ (c j) ((T
∘L T) (c j))) (∑' n, D.eigenvalue n^2)`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.spectralSorted_nonneg`,
`«2610.05164v2».Continuum.spectralSelected_sum_map`,
`«2610.05164v2».Continuum.spectralSelected_contains_finite` with the arguments shown in the
proof.
-/
theorem spectralSorted_moment (hs : Summable a) (hn : ∀ i, 0 ≤ a i) (φ : ℝ → ℝ) (hφ : φ 0 = 0)
    (hp : ∀ x, 0 ≤ x → 0 ≤ φ x) (hm : Summable (fun i => φ (a i))) :
    Summable (fun n => φ (spectralSorted hs n)) ∧
      (∑' n, φ (spectralSorted hs n)) = ∑' i, φ (a i) := by
  -- Prove the summability hsorted needed for the later infinite-sum manipulations.
  have hsorted : Summable (fun n => φ (spectralSorted hs n)) := by
    apply summable_of_sum_range_le (fun n => hp _ (spectralSorted_nonneg hs n))
    intro n
    rw [← spectralSelected_sum_map hs φ hφ]
    exact hm.sum_le_tsum _ (fun i _ => hp _ (hn i))
  refine ⟨hsorted,le_antisymm ?_ ?_⟩
  · apply Real.tsum_le_of_sum_range_le (fun n => hp _ (spectralSorted_nonneg hs n))
    intro n
    rw [← spectralSelected_sum_map hs φ hφ]
    exact hm.sum_le_tsum _ (fun i _ => hp _ (hn i))
  · apply Real.tsum_le_of_sum_le (fun i => hp _ (hn i))
    intro s
    obtain ⟨n,hcover⟩ := spectralSelected_contains_finite hs hn s
    let t := s.filter (fun i => 0 < a i)
    have he : (∑ i ∈ s, φ (a i)) = ∑ i ∈ t, φ (a i) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hit
      have hp : ¬0 < a i := fun hp => hit (Finset.mem_filter.mpr ⟨hi,hp⟩)
      rw [le_antisymm (le_of_not_gt hp) (hn i),hφ]
    have ht : t ⊆ spectralSelected hs n := by
      intro i hi
      obtain ⟨his,hip⟩ := Finset.mem_filter.mp hi
      exact hcover i his hip
    rw [he]
    calc
      _ ≤ ∑ i ∈ spectralSelected hs n, φ (a i) :=
        Finset.sum_le_sum_of_subset_of_nonneg ht (fun i _ _ => hp _ (hn i))
      _ = ∑ j ∈ Finset.range n, φ (spectralSorted hs j) := spectralSelected_sum_map hs φ hφ n
      _ ≤ _ := hsorted.sum_le_tsum _ (fun j _ => hp _ (spectralSorted_nonneg hs j))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
The spectral square sum is the trace of the actual composed operator in every Hilbert basis.

The value of a convergent infinite sum: `HasSum (fun j => inner ℝ (c j) ((T ∘L T) (c j))) (∑'
n, D.eigenvalue n^2)`.

Use: `«2610.05164v2».Packing.packedKernel_hasSum_square_trace` uses this infinite-sum formula
to establish the value of a convergent infinite sum: `HasSum (fun i => inner ℝ (b i)
((packedKernelOperator J hN ht ∘L packedKernelOperator J hN ht) (b i))) (∑' j, packedEigenvalue
J hN ht j^2)`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packedKernel_hasSum_square_trace`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates
`«2610.05164v2».Continuum.PositiveSpectralData.hasSum_trace`,
`«2610.05164v2».Continuum.spectralSorted_moment` with the arguments shown in the proof.
-/
theorem PositiveSpectralData.hasSum_square_trace {T : E →L[ℝ] E} (D : PositiveSpectralData T)
    (hM : (∑' i, D.eig i) = 1) {κ : Type*} (c : HilbertBasis κ ℝ E) :
    HasSum (fun j => inner ℝ (c j) ((T ∘L T) (c j))) (∑' n, D.eigenvalue n^2) := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.PositiveSpectralData.hasSum_trace`,
  -- `«2610.05164v2».Continuum.spectralSorted_moment` with the arguments shown in the proof.
  have hle (i : D.Index) : D.eig i ≤ 1 := by
    rw [← hM]
    exact D.summable.le_tsum i (fun j _ => D.nonneg j)
  -- Prove the summability hs needed for the later infinite-sum manipulations.
  have hs : Summable (fun i => D.eig i^2) :=
    D.summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => by nlinarith [D.nonneg i,hle i])
  let D2 : PositiveSpectralData (T ∘L T) := {
    Index := D.Index
    basis := D.basis
    eig i := D.eig i^2
    equation i := by
      change T (T (D.basis i)) = _
      rw [D.equation,map_smul,D.equation,smul_smul,pow_two]
    nonneg i := sq_nonneg _
    summable := hs }
  have h := D2.hasSum_trace c
  have he := (spectralSorted_moment D.summable D.nonneg (fun x => x^2) (by norm_num)
    (fun x _ => sq_nonneg x) hs).2
  rwa [← he] at h

end
end «2610.05164v2».Continuum
