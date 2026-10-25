import chebyshev2.Continuum.SpectralOrder

/-!
Article: chebyshev2, Theorem 2.3.
Trace in every Hilbert basis, derived from the actual positive eigenbasis.
Use: `chebyshev2.Continuum.PositiveSpectralData.hasSum_trace_eigenvalues` feeds
`chebyshev2.Continuum.eigenvalue_l1_le_traceBound` (Lemma 4(iv), in the finite-frame formulation
of the nuclear bound).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory. The needed
form is proved here.
-/
namespace chebyshev2.Continuum
noncomputable section
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
Trace in every Hilbert basis, derived from the actual positive eigenbasis.

The value of a convergent infinite sum: `HasSum (fun j => inner ℝ (c j) (T (c j))) (∑' i, D.eig
i)`.

Use: `chebyshev2.Continuum.PositiveSpectralData.hasSum_trace_eigenvalues` uses this
infinite-sum formula to establish the value of a convergent infinite sum: `HasSum (fun j =>
inner ℝ (c j) (T (c j))) (∑' n, D.eigenvalue n)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem PositiveSpectralData.hasSum_trace {T : E →L[ℝ] E} (D : PositiveSpectralData T)
    {κ : Type*} (c : HilbertBasis κ ℝ E) :
    HasSum (fun j => inner ℝ (c j) (T (c j))) (∑' i, D.eig i) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hs (i : D.Index) : HasSum (fun j => D.eig i * inner ℝ (D.basis i) (c j)^2) (D.eig i) := by
    have h := (basis_hasSum_sq c (D.basis i)).mul_left (D.eig i)
    simpa only [real_inner_comm (c _) (D.basis i),D.basis.orthonormal.norm_eq_one,one_pow,mul_one] using h
  -- Prove the summability hprod needed for the later infinite-sum manipulations.
  have hprod : Summable (fun p : D.Index × κ => D.eig p.1 * inner ℝ (D.basis p.1) (c p.2)^2) := by
    apply (summable_prod_of_nonneg (fun p => mul_nonneg (D.nonneg p.1) (sq_nonneg _))).mpr
    exact ⟨fun i => (hs i).summable,by simpa only [(hs _).tsum_eq] using D.summable⟩
  have ht (j : κ) := eigenbasis_quadratic_hasSum D.basis T D.equation (c j)
  -- Prove the summability hsum needed for the later infinite-sum manipulations.
  have hsum : Summable (fun j => inner ℝ (c j) (T (c j))) := by
    have h := hprod.prod_symm.prod
    change Summable (fun j => ∑' i, D.eig i * inner ℝ (D.basis i) (c j)^2) at h
    simpa only [(ht _).tsum_eq] using h
  apply hsum.hasSum_iff.mpr
  calc
    _ = ∑' j, ∑' i, D.eig i * inner ℝ (D.basis i) (c j)^2 := tsum_congr (fun j => (ht j).tsum_eq.symm)
    _ = ∑' i, ∑' j, D.eig i * inner ℝ (D.basis i) (c j)^2 := hprod.tsum_comm
    _ = _ := tsum_congr (fun i => (hs i).tsum_eq)

/--
The value of a convergent infinite sum: `HasSum (fun j => inner ℝ (c j) (T (c j))) (∑' n,
D.eigenvalue n)`.

Use: `chebyshev2.Continuum.eigenvalue_l1_le_traceBound` uses this infinite-sum formula to
establish the stated quantitative bound `(∑' n, |DA.eigenvalue n - DB.eigenvalue n|) ≤ C`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates
`chebyshev2.Continuum.PositiveSpectralData.eigenvalue_tsum`,
`chebyshev2.Continuum.PositiveSpectralData.hasSum_trace` with the arguments shown in the
proof.
-/
theorem PositiveSpectralData.hasSum_trace_eigenvalues {T : E →L[ℝ] E} (D : PositiveSpectralData T)
    {κ : Type*} (c : HilbertBasis κ ℝ E) :
    HasSum (fun j => inner ℝ (c j) (T (c j))) (∑' n, D.eigenvalue n) := by
  rw [D.eigenvalue_tsum]
  exact D.hasSum_trace c

end
end chebyshev2.Continuum
