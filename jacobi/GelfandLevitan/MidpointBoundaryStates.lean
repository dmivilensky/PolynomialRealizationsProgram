import jacobi.GelfandLevitan.TransformedHilbertGreen

/-!
Article: jacobi, Proposition C.2.
Every original spectral midpoint state is nonzero. Both actual
transformed bases are used: a zero state would be orthogonal to the
entire other parity basis, contradicting its own proved normalization.
Each original parity family therefore has one nontrivial common
separated midpoint boundary condition.
Use: midpoint_spectral_state_nonzero tests an actual zero midpoint state against the complete other transformed basis.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The opposite original spectral parity class.
Use: midpoint_spectral_state_nonzero tests an actual zero midpoint state against the complete other transformed basis.
Article: jacobi, Proposition C.2.
-/
def oppositeParity (p : Fin 2) : Fin 2 := ⟨1-(p:ℕ),by omega⟩

/-- The two original parity classes have disjoint actual reference indices.
Use: strict monotonicity of the original sigma enumeration permits division by the genuine spectral difference in the midpoint nonvanishing proof.
Article: jacobi, Proposition C.2.
Proof: equality would give equal residues modulo two, whereas the two original parity residues are complementary. -/
theorem oppositeParity_index_ne (p : Fin 2) (i j : ℕ) :
    parityIndex (oppositeParity p) i≠parityIndex p j := by
  change 2*i+(1-(p:ℕ))≠2*j+(p:ℕ)
  have hp := p.isLt
  omega

/-- Every actual transformed spectral midpoint state is nonzero.
Use: the genuine collinear states determine one nontrivial boundary condition for each original parity class in Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: if both actual characteristic values vanished, the original Green identity would make that wave orthogonal to every wave of the other actual parity basis. Its proved completeness forces the genuine Hilbert vector to be zero. Its own independently proved normalized basis entry has norm one, a contradiction. -/
theorem midpoint_spectral_state_nonzero (a : ℝ) (ha : -1<a) (p : Fin 2) (k : ℕ) :
    midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex p k):ℂ)≠0 ∨
      midpointSlope a ha (jacobi.Bessel.sigma a ha (parityIndex p k):ℂ)≠0 := by
  -- The two completeness uses refer to the actual original transformed functions, not hypothetical boundary eigenfunctions.
  by_contra h
  push Not at h
  have hz : transformedVector a ha (jacobi.Bessel.sigma a ha (parityIndex p k))=0 := by
    apply transformed_parity_total a ha (oppositeParity p)
    intro j
    have hG := midpoint_hilbert_green a ha
      (jacobi.Bessel.sigma a ha (parityIndex (oppositeParity p) j))
      (jacobi.Bessel.sigma a ha (parityIndex p k))
    simp only [h.1,h.2,mul_zero,sub_self] at hG
    have hσ : jacobi.Bessel.sigma a ha (parityIndex (oppositeParity p) j)≠
        jacobi.Bessel.sigma a ha (parityIndex p k) :=
      (jacobi.Bessel.sigma_strictMono ha).injective.ne (oppositeParity_index_ne p j k)
    have hE : (jacobi.Bessel.sigma a ha (parityIndex (oppositeParity p) j):ℂ)-
        (jacobi.Bessel.sigma a ha (parityIndex p k):ℂ)≠0 :=
      sub_ne_zero.mpr (Complex.ofReal_injective.ne hσ)
    exact Complex.ofReal_injective ((mul_eq_zero.mp hG).resolve_left hE)
  have hN := normalizedTransformedVector_parity_inner a ha p k k
  rw [normalizedTransformedVector,hz,smul_zero,inner_zero_left] at hN
  norm_num at hN

/-- Each actual original parity family has a common nontrivial midpoint boundary condition, expressed in the genuine complex characteristics.
Use: the negative-energy and characteristic-product comparison in the subsequent Proposition C.2 argument identifies these actual separated classes as Neumann and Dirichlet.
Article: jacobi, Proposition C.2.
Proof: use the actual first state of that same parity class as the nonzero boundary vector. Its determinant with every other original state vanishes by the proved genuine parity Green identity. -/
theorem midpoint_parity_boundary_class (a : ℝ) (ha : -1<a) (p : Fin 2) :
    ∃ A B:ℂ,(A≠0 ∨ B≠0) ∧ ∀ k,
      midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex p k):ℂ)*B-
        midpointSlope a ha (jacobi.Bessel.sigma a ha (parityIndex p k):ℂ)*A=0 :=
  ⟨midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex p 0):ℂ),
    midpointSlope a ha (jacobi.Bessel.sigma a ha (parityIndex p 0):ℂ),
      midpoint_spectral_state_nonzero a ha p 0,fun k => midpoint_parity_collinear a ha p k 0⟩

/-- Each actual original spectral parity family has a common nontrivial real separated midpoint condition.
Use: the subsequent negative-energy comparison identifies these actual real boundary classes as the Neumann and Dirichlet classes of general Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: take the real parts of the genuine first midpoint state. The actual characteristics are real at real energies, so these real coefficients retain both the proved nonzero state and every original determinant identity. -/
theorem midpoint_parity_real_boundary_class (a : ℝ) (ha : -1<a) (p : Fin 2) :
    ∃ A B:ℝ,(A≠0 ∨ B≠0) ∧ ∀ k,
      midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex p k):ℂ)*(B:ℂ)-
        midpointSlope a ha (jacobi.Bessel.sigma a ha (parityIndex p k):ℂ)*(A:ℂ)=0 := by
  -- Reality is used for the actual characteristic values, rather than supplied for arbitrary boundary coefficients.
  let E := jacobi.Bessel.sigma a ha (parityIndex p 0)
  have hA : ((midpointValue a ha (E:ℂ)).re:ℂ)=midpointValue a ha (E:ℂ) := by
    rw [midpointValue_real]
    rfl
  have hB : ((midpointSlope a ha (E:ℂ)).re:ℂ)=midpointSlope a ha (E:ℂ) := by
    rw [midpointSlope_real]
    rfl
  refine ⟨(midpointValue a ha (E:ℂ)).re,(midpointSlope a ha (E:ℂ)).re,?_,?_⟩
  · rcases midpoint_spectral_state_nonzero a ha p 0 with h|h
    · left
      intro hz
      rw [hz,Complex.ofReal_zero] at hA
      exact h hA.symm
    · right
      intro hz
      rw [hz,Complex.ofReal_zero] at hB
      exact h hB.symm
  · intro k
    rw [hA,hB]
    exact midpoint_parity_collinear a ha p k 0

end
end jacobi.GelfandLevitan
