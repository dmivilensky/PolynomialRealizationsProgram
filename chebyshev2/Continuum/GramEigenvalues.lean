import chebyshev2.Continuum.Eigenframe

/-!
Article: chebyshev2, Theorem 2.3.
Equality of sorted, zero-padded Gram spectra, in possibly different Hilbert spaces; this includes
nonzero multiplicities.
Use: `chebyshev2.Continuum.gram_eigenvalue_eq` feeds
`chebyshev2.Continuum.density_kernel_eigenvalue_eq` (The article's two continuum operators have
equal sorted spectra, with the same zero-padding convention even when their kernels differ).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
Source: Riesz and Sz.-Nagy, Functional Analysis — nonzero spectra of Gram operators. The needed form
is proved here.
-/
namespace chebyshev2.Continuum
noncomputable section
open Real
open scoped InnerProductSpace BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

/--
The stated quantitative bound `D.eigenvalue n ≤ D'.eigenvalue n`.

Use: `chebyshev2.Continuum.gram_eigenvalue_eq` uses this bound to establish the identity
`D.eigenvalue = D'.eigenvalue`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — nonzero spectra of Gram operators.

Proof: Separate `0 < D.eigenvalue n` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Clear the denominators using the available nonzero hypotheses,
then verify the remaining algebraic identity.
-/
theorem gram_eigenvalue_le (A : E →L[ℝ] F) (D : PositiveSpectralData (A.adjoint ∘L A))
    (D' : PositiveSpectralData (A ∘L A.adjoint)) (n : ℕ) : D.eigenvalue n ≤ D'.eigenvalue n := by
  -- Separate `0 < D.eigenvalue n` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  by_cases hp : 0 < D.eigenvalue n
  · let s := spectralSelected D.summable (n+1)
    have hcard : s.card = n+1 := by
      cases h : spectralNext D.summable (spectralSelected D.summable n) with
      | none =>
        have hz : D.eigenvalue n = 0 := by simp only [PositiveSpectralData.eigenvalue,spectralSorted,h,Option.elim_none]
        exact (hp.ne' hz).elim
      | some i =>
        dsimp [s]
        rw [spectralSelected,h,Finset.card_insert_of_notMem (spectralNext_some D.summable h).1,
          spectralSelected_card_of_missing D.summable n (spectralNext_some D.summable h).1
            (spectralNext_some D.summable h).2.1]
    have hpos (i : s) : 0 < D.eig i := hp.trans_le (spectralSelected_ge_last D.summable D.nonneg n i.property)
    let v : s → F := fun i => (sqrt (D.eig i))⁻¹ • A (D.basis i)
    have hinner (i j : s) : inner ℝ (A (D.basis i)) (A (D.basis j)) =
        D.eig j * inner ℝ (D.basis i) (D.basis j) := by
      rw [← ContinuousLinearMap.adjoint_inner_right]
      change inner ℝ (D.basis i) ((A.adjoint ∘L A) (D.basis j)) = _
      rw [D.equation,real_inner_smul_right,mul_comm]
    have hv : Orthonormal ℝ v := by
      rw [orthonormal_iff_ite]
      intro i j
      change inner ℝ ((sqrt (D.eig i))⁻¹ • A (D.basis i))
        ((sqrt (D.eig j))⁻¹ • A (D.basis j)) = _
      rw [real_inner_smul_left,real_inner_smul_right,hinner]
      by_cases h : i=j
      · subst j
        rw [real_inner_self_eq_norm_sq,D.basis.orthonormal.norm_eq_one]
        simp only [one_pow,mul_one,ite_true]
        have hr := sqrt_pos.mpr (hpos i)
        have hs := sq_sqrt (hpos i).le
        field_simp
        nlinarith [hs]
      · have he : (i : D.Index) ≠ (j : D.Index) := fun he => h (Subtype.ext he)
        rw [D.basis.orthonormal.inner_eq_zero he]
        simp [h]
    have he (i : s) : (A ∘L A.adjoint) (v i) = D.eig i • v i := by
      have hi : A.adjoint (A (D.basis i)) = D.eig i • D.basis i := D.equation i
      change A (A.adjoint ((sqrt (D.eig i))⁻¹ • A (D.basis i))) = _
      rw [map_smul,map_smul,hi,map_smul]
      dsimp [v]
      rw [smul_comm]
    apply eigenvalue_ge_of_eigenframe D' hv he (fun i => spectralSelected_ge_last D.summable D.nonneg n i.property) n
    simpa using (show n < s.card by omega)
  · exact (le_of_not_gt hp).trans (D'.eigenvalue_nonneg n)

/--
Equality of sorted, zero-padded Gram spectra, in possibly different Hilbert spaces; this
includes nonzero multiplicities.

Exact identity `D.eigenvalue = D'.eigenvalue`.

Use: `chebyshev2.Continuum.atomic_matrix_eigenvalue_eq` uses this identity to establish
exact identity `(atomicSpectralData w y hw).eigenvalue = (atomicMatrixSpectralData w
y).eigenvalue`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — nonzero spectra of Gram operators.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem gram_eigenvalue_eq (A : E →L[ℝ] F) (D : PositiveSpectralData (A.adjoint ∘L A))
    (D' : PositiveSpectralData (A ∘L A.adjoint)) : D.eigenvalue = D'.eigenvalue := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  funext n
  apply le_antisymm (gram_eigenvalue_le A D D' n)
  have h := gram_eigenvalue_le A.adjoint
  rw [ContinuousLinearMap.adjoint_adjoint] at h
  exact h D' D n

end
end chebyshev2.Continuum
