import krylov.OneGradient.KnownBaseCentreData
import krylov.Reference.EnergyPositive
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), genuine complete two-dimensional CG plane.
Use: derive the actual orthonormal complete frame and exact normalization
used by the history-only known-base centring algorithm.
Source: real full-atom CG orthonormality, genuine finite-dimensional span
and the actual penultimate canonical residual/last-step identity.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace BigOperators

/-- The actual known reference's two canonical CG unit steps form a
complete genuine physical orthonormal plane.
Use: the centring algorithm and hidden-adversary constructions use the
actual known full-atom reference geometry, not a supplied frame model.
Article: main_krylov, thm:local(c), original known-base frame.
Proof: genuine full-atom CG gives its true orthonormal family. The actual
finite dimension makes that genuine family a complete orthonormal basis;
its exact coordinate sum reconstructs every real physical vector. -/
theorem knownBaseCentre_reference_plane (base : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin 2)) (hc : referenceAtomCount base hb g=2) :
    ‖canonicalCGUnitStep base g 0‖=1 ∧ ‖canonicalCGUnitStep base g 1‖=1 ∧
      inner ℝ (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g 1)=0 ∧
      ∀ v : EuclideanSpace ℝ (Fin 2),
        (inner ℝ (canonicalCGUnitStep base g 0) v) • canonicalCGUnitStep base g 0+
          (inner ℝ (canonicalCGUnitStep base g 1) v) • canonicalCGUnitStep base g 1=v := by
  let q := fun i : Fin 2 => canonicalCGUnitStep base g i.val
  have ho : Orthonormal ℝ q := canonicalCG_frame_of_full_atoms base hb g hc
  have h0 : ‖q (0 : Fin 2)‖=1 := ho.norm_eq_one (0 : Fin 2)
  have h1 : ‖q (1 : Fin 2)‖=1 := ho.norm_eq_one (1 : Fin 2)
  have h01 : inner ℝ (q (0 : Fin 2)) (q (1 : Fin 2))=0 :=
    ho.inner_eq_zero (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
  have hdim : Fintype.card (Fin 2)=Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by simp
  have hsp : Submodule.span ℝ (Set.range q)=⊤ := ho.linearIndependent.span_eq_top_of_card_eq_finrank' hdim
  have hspan : ⊤≤Submodule.span ℝ (Set.range q) := hsp.ge
  let b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) := OrthonormalBasis.mk ho hspan
  have hbq (i : Fin 2) : b i=q i := congrFun (OrthonormalBasis.coe_mk ho hspan) i
  refine ⟨h0,h1,h01,?_⟩
  intro v
  have hv := b.sum_repr' v
  rw [Fin.sum_univ_two] at hv
  simpa only [hbq,q,Fin.val_zero,Fin.val_one] using hv

/-- The actual known last canonical CG step length is positive and equals
the original penultimate-reference energy-error normalization exactly.
Use: the centring policy reads its genuine observed increment column with
the source denominator, rather than a surrogate terminal length.
Article: main_krylov, thm:local(c), true V2 error normalization.
Proof: true full-atom nonstagnation makes the actual last canonical step
nonzero. The exact actual last-reference gradient identity and unit norm
identify its genuine norm with the original penultimate canonical error. -/
theorem knownBaseCentre_reference_scale (base : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin 2)) (hc : referenceAtomCount base hb g=2) :
    0<‖canonicalCGStep base g 1‖ ∧ ‖cgCanonicalError base g 1‖=‖canonicalCGStep base g 1‖ := by
  have hs := canonicalCGStep_ne_zero base hb g 1
    (fun i hi => cg_nonstagnation base hb g i (by rw [hc];omega))
  have ho := canonicalCG_frame_of_full_atoms base hb g hc
  have he := canonicalCG_last_gradient base hb g ho
  have hh := (knownBaseCentre_reference_plane base hb g hc).2.1
  refine ⟨norm_pos_iff.mpr hs,?_⟩
  change ‖cgOperator (metricRoot base)⁻¹ (CG.gradient (cgOperator base) g 1)‖=‖canonicalCGStep base g 1‖
  have he' : cgOperator (metricRoot base)⁻¹ (CG.gradient (cgOperator base) g 1)=
      -‖canonicalCGStep base g 1‖ • canonicalCGUnitStep base g 1 := he
  rw [he',norm_smul,Real.norm_eq_abs,abs_neg,abs_norm,hh,mul_one]

end
end krylov.OneGradient
