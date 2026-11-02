import jacobi.GelfandLevitan.NuclearSynthesis

/-!
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
A complete norm-summable perturbation of an actual Hilbert basis has
an invertible synthesis operator. The proof uses the actual compact
adjoint correction and the community Fredholm alternative.
Use: excludes the compact adjoint correction's minus-one eigenvalue in synthesisOperator_isUnit.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Module
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The synthesis operator of a complete actual perturbed family has injective true Hilbert adjoint.
Use: excludes the compact adjoint correction's minus-one eigenvalue in synthesisOperator_isUnit.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: a genuine zero adjoint image pairs to zero with every original basis image g_k. The stated mathematical completeness of that actual family then forces the original vector to vanish. -/
theorem synthesisOperator_adjoint_injective (b : HilbertBasis ℕ ℝ H) (g : ℕ → H)
    (hδ : Summable (fun k => ‖g k-b k‖))
    (htotal : ∀ v:H,(∀ k,inner ℝ (g k) v=0) → v=0) :
    Function.Injective (synthesisOperator b g).adjoint := by
  apply (synthesisOperator b g).adjoint.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change (synthesisOperator b g).adjoint v=0 at hv
  apply htotal v
  intro k
  rw [← synthesisOperator_basis b g hδ k,← ContinuousLinearMap.adjoint_inner_right,hv,inner_zero_right]

/-- A complete norm-summable actual basis perturbation has a genuine bounded invertible synthesis operator.
Use: the original target reference families discharge hdelta and htotal, so the subsequent transformed frame is a unitary image of the true reference basis.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Source: compact Fredholm alternative, mathlib.
Proof: the actual compact adjoint correction cannot have eigenvalue minus one, since the true synthesis adjoint is injective. Fredholm gives its genuine inverse; taking Hilbert star gives invertibility of the original synthesis operator. -/
theorem synthesisOperator_isUnit (b : HilbertBasis ℕ ℝ H) (g : ℕ → H)
    (hδ : Summable (fun k => ‖g k-b k‖))
    (htotal : ∀ v:H,(∀ k,inner ℝ (g k) v=0) → v=0) : IsUnit (synthesisOperator b g) := by
  -- These are explicit general mathematical hypotheses; both are proved for the actual source family in TransformedBases.
  have hA : (synthesisOperator b g).adjoint=1+(synthesisCorrection b g).adjoint := by
    rw [synthesisOperator,map_add,ContinuousLinearMap.adjoint_one]
  have hne : ¬ Module.End.HasEigenvalue (synthesisCorrection b g).adjoint.toLinearMap (-1:ℝ) := by
    intro he
    obtain ⟨v,hv⟩ := he.exists_hasEigenvector
    have hz : (synthesisOperator b g).adjoint v=0 := by
      rw [hA]
      change v+(synthesisCorrection b g).adjoint v=0
      have he : (synthesisCorrection b g).adjoint v= -v := by
        have hh := hv.apply_eq_smul
        simp only [neg_one_smul] at hh
        convert! hh using 1
      rw [he,add_neg_cancel]
    exact hv.2 ((synthesisOperator_adjoint_injective b g hδ htotal) (hz.trans (map_zero _).symm))
  have hu : IsUnit (synthesisOperator b g).adjoint := by
    rcases (synthesisCorrection_adjoint_compact b g hδ).hasEigenvalue_or_mem_resolventSet
        (by norm_num : (-1:ℝ)≠0) with h|h
    · exact False.elim (hne h)
    · have hu : IsUnit ((-1:H →L[ℝ] H)-(synthesisCorrection b g).adjoint) := by
        simpa only [map_neg,map_one] using (spectrum.mem_resolventSet_iff.mp h)
      have he : (-1:H →L[ℝ] H)-(synthesisCorrection b g).adjoint= -(synthesisOperator b g).adjoint := by
        rw [hA]
        abel_nf
      rw [he] at hu
      simpa only [neg_neg] using hu.neg
  have h := hu.star
  simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint] using h

end
end jacobi.GelfandLevitan
