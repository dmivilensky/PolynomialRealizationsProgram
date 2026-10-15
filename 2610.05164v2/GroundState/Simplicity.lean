import «2610.05164v2».GroundState.Uniqueness

/-!
Article: 2610.05164v2, Theorem 3.1.
The literal leading eigenspace of the article's L2 kernel has dimension one.
Use: `«2610.05164v2».GroundState.kernel_ground_simple` feeds
`«2610.05164v2».GroundState.GroundWitness.simple` (simple).
-/
namespace «2610.05164v2».GroundState
noncomputable section
open «2610.05164v2».Continuum «2610.05164v2».Sobolev Set MeasureTheory Real Module.End
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
The literal leading eigenspace of the article's L2 kernel has dimension one. Multiplicity is
transferred by the previously proved Gram eigenspace equivalence.

Exact identity `Module.finrank ℝ (eigenspace (kernelOperator hm hn).toLinearMap
(kernelEigenvalue hm hn 0))=1`.

Use: `«2610.05164v2».GroundState.GroundWitness.simple` uses this identity to establish exact
identity `Module.finrank ℝ (Module.End.eigenspace (kernelOperator hm hn).toLinearMap
(kernelEigenvalue hm hn 0))=1`.

Article: 2610.05164v2, Theorem 3.1.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.exists_unique_ground`,
`«2610.05164v2».Sobolev.H1.rep_zero`, `«2610.05164v2».GroundState.top_density_attained` with
the arguments shown in the proof.
-/
theorem kernel_ground_simple {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hM : 0 < ∫ x, m x) :
    Module.finrank ℝ (eigenspace (kernelOperator hm hn).toLinearMap (kernelEigenvalue hm hn 0))=1 := by
  -- Use the identities/estimates `«2610.05164v2».GroundState.exists_unique_ground`,
  -- `«2610.05164v2».Sobolev.H1.rep_zero`, `«2610.05164v2».GroundState.top_density_attained`
  -- with the arguments shown in the proof.
  obtain ⟨u,_,hpos,_,he,_,hsimple,_⟩ := exists_unique_ground hm hn hM
  have hun : u ≠ 0 := by
    intro hz
    have hp := hpos 0
    rw [hz,H1.rep_zero] at hp
    exact (lt_irrefl (0:ℝ)) hp
  have hspace : eigenspace (densityOperator m).toLinearMap (kernelEigenvalue hm hn 0)=
      Submodule.span ℝ {u} := by
    apply le_antisymm
    · intro v hv
      obtain ⟨r,hr⟩ := hsimple v (mem_eigenspace_iff.mp hv)
      rw [hr]
      exact Submodule.smul_mem _ r (Submodule.subset_span (mem_singleton u))
    · apply Submodule.span_le.mpr
      intro v hv
      have hvu : v=u := mem_singleton_iff.mp hv
      rw [hvu]
      exact mem_eigenspace_iff.mpr he
  rw [← (densityKernelEigenspaceEquiv hm hn (ne_of_gt (top_density_attained hm hn hM).1)).finrank_eq,
    hspace]
  exact finrank_span_singleton hun

end
end «2610.05164v2».GroundState
