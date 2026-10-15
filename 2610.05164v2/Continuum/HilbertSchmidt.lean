import «2610.05164v2».Continuum.GramCompact

/-!
Article: 2610.05164v2, Theorem 2.4.
Both Gram products have the same trace, in arbitrary Hilbert bases.
Use: `«2610.05164v2».Continuum.kernelOperator_trace` feeds
`«2610.05164v2».Continuum.kernelEigenvalue_mass` (kernel Eigenvalue mass).
Proof chain: `«2610.05164v2».Packing.packedKernel_hasSum_square_trace` — 2610.05164v2, Theorem 2.4;
Uniform l1 spectral transfer, ground parameter and Fredholm/cosh observations.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open MeasureTheory Real
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

omit [CompleteSpace E] in
/--
The value of a convergent infinite sum: `HasSum (fun i => inner ℝ (b i) x ^ 2) (‖x‖^2)`.

Use: `«2610.05164v2».Continuum.adjoint_frame_bound` uses this infinite-sum formula to establish
the stated quantitative bound `(∑ i, ‖A.adjoint (u i)‖^2) ≤ C`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem basis_hasSum_sq {ι : Type*} (b : HilbertBasis ι ℝ E) (x : E) :
    HasSum (fun i => inner ℝ (b i) x ^ 2) (‖x‖^2) := by
  have h := b.hasSum_inner_mul_inner x x
  rw [real_inner_self_eq_norm_sq] at h
  simpa only [real_inner_comm x (b _), ← pow_two] using h

/--
A basis-independent finite-frame bound for a Hilbert--Schmidt adjoint.

The stated quantitative bound `(∑ i, ‖A.adjoint (u i)‖^2) ≤ C`.

Use: `«2610.05164v2».Continuum.gram_traceBound` uses this bound to establish the precise
assertion is `TraceBound (A ∘L A.adjoint) C`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packedKernel_hasSum_square_trace`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.basis_hasSum_sq` with the
arguments shown in the proof.
-/
theorem adjoint_frame_bound {ι : Type*} (b : HilbertBasis ι ℝ E) (A : E →L[ℝ] F)
    {C : ℝ} (hC : HasSum (fun k => ‖A (b k)‖^2) C)
    {n : ℕ} {u : Fin n → F} (hu : Orthonormal ℝ u) :
    (∑ i, ‖A.adjoint (u i)‖^2) ≤ C := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.basis_hasSum_sq` with the arguments
  -- shown in the proof.
  classical
  have hs (i : Fin n) : HasSum (fun k => inner ℝ (A (b k)) (u i)^2) (‖A.adjoint (u i)‖^2) := by
    simpa only [ContinuousLinearMap.adjoint_inner_right] using
      basis_hasSum_sq b (A.adjoint (u i))
  have hsum := hasSum_sum (s := Finset.univ) (fun i _ => hs i)
  have hb (k : ι) : (∑ i, inner ℝ (A (b k)) (u i)^2) ≤ ‖A (b k)‖^2 := by
    simpa only [real_inner_comm (A (b k)), Real.norm_eq_abs, sq_abs] using
      hu.sum_inner_products_le (A (b k)) (s := Finset.univ)
  rw [← hsum.tsum_eq, ← hC.tsum_eq]
  exact hsum.summable.tsum_le_tsum hb hC.summable

/--
The finite-frame dual nuclear bound for A A*, derived from its squared Hilbert--Schmidt norm
rather than postulated trace-class membership.

The precise assertion is `TraceBound (A ∘L A.adjoint) C`.

Use: `«2610.05164v2».Continuum.kernelOperator_traceBound` uses this assertion to establish the
precise assertion is `TraceBound (kernelOperator hm hn) (∫ x, m x)`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packedKernel_hasSum_square_trace`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem gram_traceBound {ι : Type*} (b : HilbertBasis ι ℝ E) (A : E →L[ℝ] F)
    {C : ℝ} (hC : HasSum (fun k => ‖A (b k)‖^2) C) : TraceBound (A ∘L A.adjoint) C := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hn : 0 ≤ C := hC.nonneg (fun _ => sq_nonneg _)
  intro n u v hu hv
  have hau := adjoint_frame_bound b A hC hu
  have hav := adjoint_frame_bound b A hC hv
  have hi : (∑ i, inner ℝ (u i) ((A ∘L A.adjoint) (v i))) =
      ∑ i, inner ℝ (A.adjoint (u i)) (A.adjoint (v i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left]
  rw [hi]
  have hb : |∑ i, inner ℝ (A.adjoint (u i)) (A.adjoint (v i))| ≤
      ∑ i, ‖A.adjoint (u i)‖ * ‖A.adjoint (v i)‖ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact abs_real_inner_le_norm _ _
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖A.adjoint (u i)‖) (fun i => ‖A.adjoint (v i)‖)
  have hp := mul_le_mul hau hav (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hn
  have hn' : 0 ≤ ∑ i, ‖A.adjoint (u i)‖ * ‖A.adjoint (v i)‖ :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact hb.trans ((sq_le_sq₀ hn' hn).mp (hs.trans (by simpa only [← pow_two] using hp)))

/--
Both Gram products have the same trace, in arbitrary Hilbert bases.

The value of a convergent infinite sum: `HasSum (fun j => inner ℝ (c j) ((A ∘L A.adjoint) (c
j))) C`.

Use: `«2610.05164v2».Continuum.kernelOperator_hasSum_trace` uses this infinite-sum formula to
establish the value of a convergent infinite sum: `HasSum (fun j => inner ℝ (c j)
(kernelOperator hm hn (c j))) (∫ x, m x)`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packedKernel_hasSum_square_trace`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem gram_hasSum_trace {ι κ : Type*} (b : HilbertBasis ι ℝ E) (c : HilbertBasis κ ℝ F)
    (A : E →L[ℝ] F) {C : ℝ} (hC : HasSum (fun k => ‖A (b k)‖^2) C) :
    HasSum (fun j => inner ℝ (c j) ((A ∘L A.adjoint) (c j))) C := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hs (k : ι) := basis_hasSum_sq c (A (b k))
  -- Prove the summability hprod needed for the later infinite-sum manipulations.
  have hprod : Summable (fun p : ι × κ => inner ℝ (c p.2) (A (b p.1))^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    constructor
    · exact fun k => (hs k).summable
    · simpa only [(hs _).tsum_eq] using hC.summable
  have he (j : κ) : inner ℝ (c j) ((A ∘L A.adjoint) (c j)) = ‖A.adjoint (c j)‖^2 := by
    rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left,
      real_inner_self_eq_norm_sq]
  have ht (j : κ) : HasSum (fun k => inner ℝ (c j) (A (b k))^2) (‖A.adjoint (c j)‖^2) := by
    have h := basis_hasSum_sq b (A.adjoint (c j))
    have he' (k : ι) : inner ℝ (b k) (A.adjoint (c j)) = inner ℝ (c j) (A (b k)) := by
      rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
    simpa only [he'] using h
  -- Prove the summability hsum needed for the later infinite-sum manipulations.
  have hsum : Summable (fun j => inner ℝ (c j) ((A ∘L A.adjoint) (c j))) := by
    have h := hprod.prod_symm.prod
    change Summable (fun j => ∑' k, inner ℝ (c j) (A (b k))^2) at h
    simpa only [(ht _).tsum_eq, he] using h
  apply hsum.hasSum_iff.mpr
  calc
    _ = ∑' j, ∑' k, inner ℝ (c j) (A (b k))^2 :=
      tsum_congr (fun j => (he j).trans (ht j).tsum_eq.symm)
    _ = ∑' k, ∑' j, inner ℝ (c j) (A (b k))^2 := hprod.tsum_comm
    _ = ∑' k, ‖A (b k)‖^2 := tsum_congr (fun k => (hs k).tsum_eq)
    _ = C := hC.tsum_eq

/--
The value of a convergent infinite sum: `HasSum (fun i => ‖evaluationOperator hm hn (b i)‖^2)
(∫ x, m x)`.

Use: `«2610.05164v2».Continuum.kernelOperator_hasSum_trace` uses this infinite-sum formula to
establish the value of a convergent infinite sum: `HasSum (fun j => inner ℝ (c j)
(kernelOperator hm hn (c j))) (∫ x, m x)`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packedKernel_hasSum_square_trace`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.evaluationOperator_inner`,
`«2610.05164v2».Continuum.densityOperator_hasSum_trace` with the arguments shown in the proof.
-/
theorem evaluationOperator_hasSum_norm {ι : Type*} (b : HilbertBasis ι ℝ FeatureSpace)
    {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    HasSum (fun i => ‖evaluationOperator hm hn (b i)‖^2) (∫ x, m x) := by
  have he (i : ι) : ‖evaluationOperator hm hn (b i)‖^2 =
      inner ℝ (b i) (densityOperator m (b i)) := by
    rw [← evaluationOperator_inner hm hn, real_inner_self_eq_norm_sq]
  simpa only [he] using densityOperator_hasSum_trace b hm

/--
The precise assertion is `TraceBound (kernelOperator hm hn) (∫ x, m x)`.

Use: `«2610.05164v2».Continuum.kernelOperator_isTraceClass` uses this assertion to establish
the trace-class property: `IsTraceClass (kernelOperator hm hn)`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packedKernel_hasSum_square_trace`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.gram_traceBound`,
`«2610.05164v2».Continuum.evaluationOperator_hasSum_norm` with the arguments shown in the
proof.
-/
theorem kernelOperator_traceBound {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    TraceBound (kernelOperator hm hn) (∫ x, m x) := by
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℝ FeatureSpace
  exact gram_traceBound b _ (evaluationOperator_hasSum_norm b hm hn)

/--
The trace-class property: `IsTraceClass (kernelOperator hm hn)`.

Use: `«2610.05164v2».Continuum.kernelSpectralData` uses this assertion in the displayed
construction of `kernelSpectralData`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packedKernel_hasSum_square_trace`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.TraceBound.isTraceClass`,
`«2610.05164v2».Continuum.kernelOperator_traceBound` with the arguments shown in the proof.
-/
theorem kernelOperator_isTraceClass {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    IsTraceClass (kernelOperator hm hn) := (kernelOperator_traceBound hm hn).isTraceClass


/--
The value of a convergent infinite sum: `HasSum (fun j => inner ℝ (c j) (kernelOperator hm hn
(c j))) (∫ x, m x)`.

Use: `«2610.05164v2».Continuum.kernelOperator_trace` uses this infinite-sum formula to
establish exact identity `(∑' j, inner ℝ (c j) (kernelOperator hm hn (c j))) = ∫ x, m x`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packedKernel_hasSum_square_trace`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.gram_hasSum_trace`,
`«2610.05164v2».Continuum.evaluationOperator_hasSum_norm` with the arguments shown in the
proof.
-/
theorem kernelOperator_hasSum_trace {κ : Type*} (c : HilbertBasis κ ℝ FeatureSpace)
    {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    HasSum (fun j => inner ℝ (c j) (kernelOperator hm hn (c j))) (∫ x, m x) := by
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℝ FeatureSpace
  exact gram_hasSum_trace b c _ (evaluationOperator_hasSum_norm b hm hn)

/--
Exact identity `(∑' j, inner ℝ (c j) (kernelOperator hm hn (c j))) = ∫ x, m x`.

Use: `«2610.05164v2».Continuum.kernelEigenvalue_mass` uses this identity to establish exact
identity `(∑' j, kernelEigenvalue hm hn j) = ∫ x, m x`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packedKernel_hasSum_square_trace`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.kernelOperator_hasSum_trace` with
the arguments shown in the proof.
-/
theorem kernelOperator_trace {κ : Type*} (c : HilbertBasis κ ℝ FeatureSpace)
    {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    (∑' j, inner ℝ (c j) (kernelOperator hm hn (c j))) = ∫ x, m x :=
  (kernelOperator_hasSum_trace c hm hn).tsum_eq

end
end «2610.05164v2».Continuum
