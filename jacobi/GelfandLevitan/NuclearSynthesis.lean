import jacobi.GelfandLevitan.TransformationInverse

/-!
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
A norm-summable perturbation of a genuine Hilbert basis is synthesized
by I plus an actual norm sum of rank-one operators. Both the correction
and its true Hilbert adjoint are compact. This general construction is
used with the independently proved original reference perturbations.
Use: synthesisCorrection sums these true operators to map the original complete reference basis to the target reference family.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual rank-one synthesis correction for one perturbed basis entry.
Use: synthesisCorrection sums these true operators to map the original complete reference basis to the target reference family.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def synthesisCorrectionTerm (b : HilbertBasis ℕ ℝ H) (g : ℕ → H) (k : ℕ) : H →L[ℝ] H :=
  InnerProductSpace.rankOne ℝ (g k-b k) (b k)

/-- The true synthesis correction constructed by summing the actual rank-one operators.
Use: synthesisOperator maps the reference basis to the actual target reference family in the two-bases argument.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def synthesisCorrection (b : HilbertBasis ℕ ℝ H) (g : ℕ → H) : H →L[ℝ] H :=
  ∑' k,synthesisCorrectionTerm b g k

/-- The identity plus the genuine compact synthesis correction.
Use: transports the actual complete half-reference basis to the target reference functions before applying the true GL transformation.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def synthesisOperator (b : HilbertBasis ℕ ℝ H) (g : ℕ → H) : H →L[ℝ] H :=
  1+synthesisCorrection b g

/-- A norm-summable actual basis perturbation gives a norm-summable rank-one synthesis series.
Use: proves the genuine synthesis limit and compactness, including its true adjoint.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Source: the community rank-one norm formula.
Proof: each original basis entry has norm one, so each actual correction norm is exactly the corresponding vector difference norm. -/
theorem synthesisCorrectionTerm_summable (b : HilbertBasis ℕ ℝ H) (g : ℕ → H)
    (hδ : Summable (fun k => ‖g k-b k‖)) : Summable (synthesisCorrectionTerm b g) := by
  apply hδ.of_norm_bounded
  intro k
  rw [synthesisCorrectionTerm,InnerProductSpace.norm_rankOne,b.orthonormal.norm_eq_one,mul_one]

/-- The actual synthesis operator sends every genuine reference basis entry to its prescribed perturbed vector.
Use: identifies the eventual unitary image with the original transformed spectral functions in Two orthonormal bases.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: evaluate the genuine norm-summable correction series at the original basis entry. Orthonormality makes every term except its own index zero, leaving exactly g_k-e_k^0. -/
theorem synthesisOperator_basis (b : HilbertBasis ℕ ℝ H) (g : ℕ → H)
    (hδ : Summable (fun k => ‖g k-b k‖)) (k : ℕ) : synthesisOperator b g (b k)=g k := by
  -- This is an actual operator series, with no extension of a merely formal basis assignment.
  have h := (ContinuousLinearMap.apply ℝ H (b k)).hasSum (synthesisCorrectionTerm_summable b g hδ).hasSum
  have he (j : ℕ) : synthesisCorrectionTerm b g j (b k)=if j=k then g k-b k else 0 := by
    rw [synthesisCorrectionTerm,InnerProductSpace.rankOne_apply,
      (orthonormal_iff_ite.mp b.orthonormal) j k]
    split_ifs with hj
    · subst j
      exact one_smul _ _
    · exact zero_smul _ _
  have hs : synthesisCorrection b g (b k)=g k-b k :=
    (h.congr_fun (fun j => (he j).symm)).unique (hasSum_ite_eq k (g k-b k))
  change b k+synthesisCorrection b g (b k)=g k
  rw [hs]
  abel_nf

/-- The actual synthesis correction is compact.
Use: the compact Fredholm argument applies to the genuine identity-plus-correction operator in the two-bases proof.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Source: norm limits of compact operators, mathlib, and the earlier article's rank-one compactness theorem.
Proof: every original finite prefix is a sum of genuine rank-one compact maps. The closed community submodule of compact operators contains their actual operator-norm limit. -/
theorem synthesisCorrection_compact (b : HilbertBasis ℕ ℝ H) (g : ℕ → H)
    (hδ : Summable (fun k => ‖g k-b k‖)) : IsCompactOperator (synthesisCorrection b g) := by
  -- Compactness belongs to the actual completed operator, not just its finite formal approximants.
  let S : Submodule ℝ (H →L[ℝ] H) := compactOperator (RingHom.id ℝ) H H
  have hS : IsClosed (S : Set (H →L[ℝ] H)) := isClosed_setOfPred_isCompactOperator
  have hlim := (synthesisCorrectionTerm_summable b g hδ).hasSum.tendsto_sum_nat
  exact hS.mem_of_tendsto hlim (Eventually.of_forall (fun N =>
    S.sum_mem (fun j _ => chebyshev2.Continuum.rankOne_isCompact _ _)))

/-- The true Hilbert adjoint of the actual synthesis correction is compact.
Use: genuine completeness excludes the compact adjoint's minus-one eigenvalue and proves synthesis invertibility by Fredholm.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Source: continuity of the Hilbert adjoint and norm-closedness of compact operators.
Proof: take the actual norm limit of the adjoints of the finite correction sums. The genuine rank-one adjoint swaps its two vectors, so each original adjoint prefix is compact; adjoint continuity and closedness give compactness of its actual limit. -/
theorem synthesisCorrection_adjoint_compact (b : HilbertBasis ℕ ℝ H) (g : ℕ → H)
    (hδ : Summable (fun k => ‖g k-b k‖)) : IsCompactOperator (synthesisCorrection b g).adjoint := by
  -- Adjoint compactness is proved here from the same actual finite-rank approximations.
  let S : Submodule ℝ (H →L[ℝ] H) := compactOperator (RingHom.id ℝ) H H
  have hS : IsClosed (S : Set (H →L[ℝ] H)) := isClosed_setOfPred_isCompactOperator
  have hlim := ContinuousLinearMap.adjoint.continuous.continuousAt.tendsto.comp
    (synthesisCorrectionTerm_summable b g hδ).hasSum.tendsto_sum_nat
  apply hS.mem_of_tendsto hlim
  exact Eventually.of_forall (fun N => by
    dsimp only [Function.comp_apply]
    rw [map_sum]
    apply S.sum_mem
    intro j _
    rw [synthesisCorrectionTerm,InnerProductSpace.adjoint_rankOne]
    exact chebyshev2.Continuum.rankOne_isCompact _ _)

end
end jacobi.GelfandLevitan
