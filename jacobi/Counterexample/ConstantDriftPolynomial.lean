import jacobi.Counterexample.ConstantDriftMinimum
import Mathlib.Analysis.Matrix.PosDef

/-!
Article: jacobi, Proposition 6.1.
The attaining chain's complete characteristic polynomial is the exact
printed affine image of the original B*B^T polynomial. Thus its proved
full-fibre minimum concerns precisely the source's original spectrum,
not a newly specified fibre with only the same limiting edge data.
Use: identifies the complete original fibre in constantDriftChain_minimum with the source polynomial whose zeros are 1-lambda_j(Y)/H.
-/
namespace jacobi.Counterexample
noncomputable section
open Matrix Polynomial jacobi.Finite chebyshev1 chebyshev2
set_option backward.isDefEq.respectTransparency false

/-- The actual attaining chain has exactly the full source affine-image characteristic polynomial.
Use: identifies the complete original fibre in constantDriftChain_minimum with the source polynomial whose zeros are 1-lambda_j(Y)/H.
Article: jacobi, Proposition 6.1.
Proof: the already proved genuine finite affine continuant identity
gives the factor H^(-n) and the change x to H*(x-1). The exact positive
Jacobi reflection supplies (-1)^n and the opposite argument. The
independently proved original Cholesky swap preserves the complete
characteristic polynomial. -/
theorem constantDriftChain_charpoly {N:ℕ} (d l:ℕ→ℝ) {kappa H:ℝ}
    (hk:0<kappa) (hH:0<H) (hdiag:∀i<N,0<d i)
    (hlower:∀ i, 0 < i → i < N → 0 < l i) (hd:∀i<N,(d i)^2-(l i)^2=kappa) (x:ℝ) :
    (constantDriftChain d l N H).matrix.charpoly.eval x=
      (-1/H)^N*(bidiagonal d l N*(bidiagonal d l N)ᵀ).charpoly.eval (H*(1-x)) := by
  -- The original finite characteristic degree is used; this is not an edge or asymptotic comparison.
  have h := leading_affine_eval (reflect (swappedJacobi d l N))
    (inv_ne_zero hH.ne') 1 x N le_rfl
  change ((constantDriftChain d l N H).data.leading N).eval x=
    H⁻¹^N*((reflect (swappedJacobi d l N)).data.leading N).eval ((x-1)/H⁻¹) at h
  simp only [JacobiData.leading,
    (reflect (swappedJacobi d l N)).data.block_eq_charpoly
      (reflect (swappedJacobi d l N)).coupling_nonneg,
    (constantDriftChain d l N H).data.block_eq_charpoly
      (constantDriftChain d l N H).coupling_nonneg] at h
  change (constantDriftChain d l N H).matrix.charpoly.eval x=
    H⁻¹^N*(reflect (swappedJacobi d l N)).matrix.charpoly.eval ((x-1)/H⁻¹) at h
  rw [reflect_charpoly_eval,swappedJacobi_matrix d l hk hdiag hlower hd,swapped_charpoly] at h
  rw [h]
  have harg : -((x-1)/H⁻¹)=H*(1-x) := by
    rw [div_inv_eq_mul]
    ring
  rw [harg]
  have hscalar : H⁻¹^N*(-1:ℝ)^N=(-1/H)^N := by
    rw [← mul_pow]
    congr 1
    ring
  rw [← mul_assoc,hscalar]

/-- The original attaining spectrum is exactly the printed affine image of the unswapped source spectrum.
Use: constantDriftChain_spectrum_interval verifies that the attaining chain has all source nodes in (-1,1) under the original spectral-window condition.
Article: jacobi, Proposition 6.1.
Proof: the exact complete characteristic identity has a nonzero scalar
factor. The community characterization of matrix spectrum by actual
characteristic roots converts that identity into the stated equivalence. -/
theorem constantDriftChain_spectrum {N:ℕ} (d l:ℕ→ℝ) {kappa H:ℝ}
    (hk:0<kappa) (hH:0<H) (hdiag:∀i<N,0<d i)
    (hlower:∀ i, 0 < i → i < N → 0 < l i) (hd:∀i<N,(d i)^2-(l i)^2=kappa) (x:ℝ) :
    x∈spectrum ℝ (constantDriftChain d l N H).matrix ↔
      H*(1-x)∈spectrum ℝ (bidiagonal d l N*(bidiagonal d l N)ᵀ) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Matrix.mem_spectrum_iff_isRoot_charpoly]
  change (constantDriftChain d l N H).matrix.charpoly.eval x=0 ↔
    (bidiagonal d l N*(bidiagonal d l N)ᵀ).charpoly.eval (H*(1-x))=0
  rw [constantDriftChain_charpoly d l hk hH hdiag hlower hd,mul_eq_zero,
    or_iff_right (pow_ne_zero N (div_ne_zero (by norm_num) hH.ne'))]

/-- The actual constructed attaining Jacobi chain has every original spectral node in (-1,1) under the source's upper spectral window.
Use: completes admissibility of the actual full-fibre optimizer in Section 6; the condition is the source's H>lambda_max(Y)/2 expressed over its genuine full spectrum.
Article: jacobi, Section 6 (bidiagonal swap identity).
Proof: the original swap preserves the complete spectrum, whose
eigenvalues are positive by its proved positive definiteness. Combine
that strict lower sign and the given actual upper spectral window with
the exact original affine spectral equivalence. -/
theorem constantDriftChain_spectrum_interval {N:ℕ} (d l:ℕ→ℝ) {kappa H:ℝ}
    (hk:0<kappa) (hH:0<H) (hdiag:∀i<N,0<d i)
    (hlower:∀ i, 0 < i → i < N → 0 < l i) (hd:∀i<N,(d i)^2-(l i)^2=kappa)
    (hupper:∀y∈spectrum ℝ (bidiagonal d l N*(bidiagonal d l N)ᵀ),y<2*H)
    {x:ℝ} (hx:x∈spectrum ℝ (constantDriftChain d l N H).matrix) : x∈Set.Ioo (-1:ℝ) 1 := by
  -- The spectral window is imposed on the original unswapped matrix from the source statement.
  have hy := (constantDriftChain_spectrum d l hk hH hdiag hlower hd x).mp hx
  have hswap : H*(1-x)∈spectrum ℝ (swappedGram d l N) := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly,swapped_charpoly]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hy
  have hpos := swapped_posDef d l hk hd
  rw [hpos.isHermitian.spectrum_real_eq_range_eigenvalues] at hswap
  obtain ⟨i,hi⟩ := hswap
  have hp := hpos.eigenvalues_pos i
  rw [hi] at hp
  have hu := hupper _ hy
  constructor <;> nlinarith

end
end jacobi.Counterexample
