import krylov.Strings.DiscreteMeasure
import krylov.Strings.DiscreteInverseBoundary

/-!
Article: `main_krylov`, `apC:lem:stieltjes(a,b)`.
The genuine physical boundary spectral probability is independent of the
chosen eigenbasis, ordering and eigenvector signs. Simplicity supplies a
true permutation of the nodes; the actual adjugate/cofactor identity fixes
the positive boundary weights at every same node. Thus the inverse string
realizes the prescribed real probability measure itself, rather than only
a matching list of spectral data in a particular basis.
-/

namespace krylov.Strings.DiscreteString
noncomputable section
open Matrix Set MeasureTheory Polynomial chebyshev1 jacobi.Finite
open scoped BigOperators ENNReal
variable {N : ℕ} (S : DiscreteString N)

/-- Any actual full physical eigenbasis with the prescribed nodes and
boundary weights gives exactly the same genuine real spectral probability. -/
theorem spectralMeasure_eq_of_basis (M : DiscreteMeasure (N+1))
    (B : SpectralBasis S.operator) (hvalues : B.eigenvalues=M.node)
    (hweights : ∀ k,B.weight 0 k=M.weight k) :
    S.spectralMeasure=krylov.Design.atomicProbability M M.node := by
  classical
  have hB : Function.Injective B.eigenvalues := by rw [hvalues]; exact M.distinct
  have hex (k : Fin (N+1)) : ∃ j,S.spectralBasis.eigenvalues j=B.eigenvalues k := by
    have hz : S.operator.charpoly.eval (B.eigenvalues k)=0 := by
      rw [B.charpoly_factor, eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      simp
    rw [S.spectralBasis.charpoly_factor, eval_prod] at hz
    obtain ⟨j,_,hj⟩ := Finset.prod_eq_zero_iff.mp hz
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hj
    exact ⟨j,hj.symm⟩
  let f : Fin (N+1)→Fin (N+1) := fun k ↦ (hex k).choose
  have hf (k : Fin (N+1)) : S.spectralBasis.eigenvalues (f k)=B.eigenvalues k :=
    (hex k).choose_spec
  have hfinj : Function.Injective f := by
    intro k l h
    apply hB
    rw [← hf k, ← hf l, h]
  let e : Fin (N+1)≃Fin (N+1) := Equiv.ofBijective f
    ⟨hfinj, Finite.surjective_of_injective hfinj⟩
  have he (k : Fin (N+1)) : S.spectralBasis.eigenvalues (e k)=B.eigenvalues k := hf k
  have hw (k : Fin (N+1)) : S.spectralBasis.weight 0 (e k)=B.weight 0 k := by
    have h0 := S.spectralBasis.adjugate_eigenvalue_diagonal S.spectralBasis_injective 0 (e k)
    have h1 := B.adjugate_eigenvalue_diagonal hB 0 k
    rw [he k] at h0
    exact mul_right_cancel₀ (B.charpoly_derivative_ne hB k) (h0.symm.trans h1)
  apply Subtype.ext
  change (∑ j, ENNReal.ofReal (S.spectralBasis.weight 0 j) •
      Measure.dirac (S.spectralBasis.eigenvalues j))=
    ∑ k, ENNReal.ofReal (M.weight k) • Measure.dirac (M.node k)
  calc
    _ = ∑ k, ENNReal.ofReal (S.spectralBasis.weight 0 (e k)) •
        Measure.dirac (S.spectralBasis.eigenvalues (e k)) := (e.sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hw k, he k, hweights k, hvalues]

end
end krylov.Strings.DiscreteString

namespace krylov.Strings.DiscreteInverse
noncomputable section
open MeasureTheory jacobi.Finite
variable {N : ℕ} (M : DiscreteMeasure (N+1))

/-- Complete finite inverse Stieltjes realization of the prescribed real
probability measure itself, with the true physical path operator. -/
theorem string_spectralMeasure (hnode : ∀ i,0≤M.node i) :
    (string M hnode).spectralMeasure=krylov.Design.atomicProbability M M.node :=
  (string M hnode).spectralMeasure_eq_of_basis M (basis M hnode) rfl (basis_weight M hnode)

end
end krylov.Strings.DiscreteInverse
