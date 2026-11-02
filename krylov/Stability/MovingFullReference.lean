import krylov.Stability.CGFrameRegularity
import krylov.Information.RankBaseCurve
import krylov.Correction.TerminalCGResponse
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine moving full-reference domain.
Use: derive full actual A0 reference activity and smooth source flags
from primitive C-one data, without a supplied moving frame or rank tube.
Source: true joint CG regularity, exact actual stopping criterion,
physical spectral-cardinality bound and genuine CG flag dictionary.
-/

namespace krylov.Stability
noncomputable section
open Matrix Filter Topology krylov.Reference krylov.Secant krylov.Correction
  krylov.Variation krylov.Information
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Full active CG reference information persists on a true primitive
C-one positive reference neighborhood.
Use: the original moving-reference source flags are genuinely complete.
Article: main_krylov, thm:local(a), actual moving full-atom domain.
Proof: true joint CG analyticity makes the last active gradient continuous
in the primitive operator. Its actual nonzero reference value persists.
Exact stopping gives the lower atom count; physical dimension gives the
upper count, so the actual moving count is exactly the dimension. -/
theorem moving_reference_full_atoms
    (B : X → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hB : ContDiffAt ℝ 1 B 0)
    (hpos : ∀ᶠ z in 𝓝 (0 : X),(B z).PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1)))
    (hc : referenceAtomCount (B 0) hpos.self_of_nhds g=n+1) :
    ∀ᶠ z in 𝓝 (0 : X),∃ hb : (B z).PosDef,referenceAtomCount (B z) hb g=n+1 := by
  let Q := fun z => cgOperator (B z)
  have hQ : ContDiffAt ℝ 1 Q 0 := matrixOperator_contDiffAt _ 0 hB
  have hj := (activeReferenceCG_analytic (B 0) hpos.self_of_nhds g n (by omega)).1
  have hG : ContDiffAt ℝ 1 (fun z => CG.gradient (Q z) g n) 0 :=
    hj.contDiffAt.comp (g := fun p => CG.gradient p.1 p.2 n)
      (f := fun z => (Q z,g)) 0 (hQ.prodMk contDiffAt_const)
  have hne : CG.gradient (Q 0) g n≠0 := cg_nonstagnation (B 0) hpos.self_of_nhds g n (by omega)
  filter_upwards [hpos,hG.continuousAt.eventually_ne hne] with z hb hz
  refine ⟨hb,?_⟩
  have hlo : n<referenceAtomCount (B z) hb g :=
    Nat.lt_of_not_ge (fun h => hz ((cg_stopping_iff (B z) hb g n).mpr h))
  have hhi := referenceAtomCount_le (B z) hb g
  omega

/-- Every actual moving full reference flag has a C-one transported
representative, equal to the genuine orthogonal source projection on a
derived reference neighborhood. Its transpose is the same real projection.
Use: coefficient freezing for the source's own A0 flags has all primitive
regularity and full-domain premises derived from the actual CG reference.
Article: main_krylov, thm:local(a), moving original flag regularity.
Proof: the real full CG matrix and inverse are C-one from primitive data.
The exact transported selector is therefore C-one. Derived full moving
activity gives the already proved actual orthogonal CG flag dictionary. -/
theorem moving_reference_flag_data
    (B : X → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hB : ContDiffAt ℝ 1 B 0)
    (hpos : ∀ᶠ z in 𝓝 (0 : X),(B z).PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1)))
    (hc : referenceAtomCount (B 0) hpos.self_of_nhds g=n+1) (l : ℕ) :
    let P := fun z => transportedFlag (canonicalCGUnitMatrix (B z) g) l
    ContDiffAt ℝ 1 P 0 ∧
      ∀ᶠ z in 𝓝 (0 : X),cgOperator (P z)=(oldFlag (B z) g l).starProjection ∧
        cgOperator (P z)ᵀ=(oldFlag (B z) g l).starProjection := by
  let P := fun z => transportedFlag (canonicalCGUnitMatrix (B z) g) l
  have hframe := canonicalCG_frame_contDiffAt B hB hpos g hc
  refine ⟨(hframe.1.mul contDiffAt_const).mul hframe.2,?_⟩
  filter_upwards [moving_reference_full_atoms B hB hpos g hc] with z hz
  obtain ⟨hb,hcount⟩ := hz
  refine ⟨canonicalCG_transportedFlag (B z) hb g hcount l,?_⟩
  have hsym : (P z)ᵀ=P z := by
    dsimp only [P,transportedFlag]
    rw [canonicalCGUnitMatrix_inverse (B z) hb g hcount]
    simp only [Matrix.transpose_mul,Matrix.transpose_transpose,(prefixProjection_isSymm (n+1) l).eq,Matrix.mul_assoc]
  rw [hsym]
  exact canonicalCG_transportedFlag (B z) hb g hcount l

end
end krylov.Stability
