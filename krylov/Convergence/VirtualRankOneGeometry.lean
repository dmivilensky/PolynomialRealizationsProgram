import krylov.Convergence.EvaluatedRankOneGeometry
import krylov.OneGradient.XRFCFlagRow
import krylov.OneGradient.TrialAmplitudes

/-!
Article: main_krylov, thm:V, prop:EL and thm:LB, real rank-one geometry.
Use: extract the oldest compatible midpoint contraction and the exact
oldest oblique-row amplification from the actual XRFC reference.
Source: true evaluated segments, genuine CG orthogonality and the already
proved literal boundary-row block of the actual projector.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Finset krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
  krylov.Tensor krylov.Correction krylov.Variation krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- True canonical missed-step coordinates in the actual virtual launch.
Article: thm:V and prop:EL. -/
theorem xrfcReferenceMiss_canonical
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : E) (i : ℕ) (hi : i<referenceAtomCount base hb g) :
    cgOperator (metricRoot base) (xrfcReferenceMiss trial (cgOperator base) g i)=
      (1-trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) g i)/
        CG.length (cgOperator base) g i) • canonicalCGStep base g i :=
  canonical_relative_trial_miss base hb g i hi _

/-- The first genuine compatible midpoint contraction has exactly the
source's half first-step value, independently of later trial errors.
Article: main_krylov, prop:EL, virtual rank-one coefficient. -/
theorem xrfc_midpoint_first_first
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n)
    (ht : ∀ i<n,0<trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i)) :
    inner ℝ (canonicalCGUnitStep base (cgOperator base u) 0)
      (cgOperator (metricRoot base) (xrfcReferenceMidpointDrift trial (cgOperator base) u 0))=
      Real.sqrt (cgEnergy base (cgOperator base u) 0)/2 := by
  let g := cgOperator base u
  let S := cgOperator (metricRoot base)
  let e := canonicalCGUnitStep base g 0
  have h0 : inner ℝ e (S (referenceStep (cgOperator base) g 0))=Real.sqrt (cgEnergy base g 0) := by
    have hh := canonical_step_unit_pair base hb g ⟨0,by rw [hc];exact hn⟩ ⟨0,by rw [hc];exact hn⟩
    simpa only [e,S,referenceStep,canonicalCGStep,cgStep,cgLine,cgOperator,ite_true,cgEnergy_sqrt base hb] using hh
  by_cases h1 : 1<n
  · have hstep1 : inner ℝ e (S (referenceStep (cgOperator base) g 1))=0 := by
      have hh := canonical_step_unit_pair base hb g ⟨0,by rw [hc];exact hn⟩ ⟨1,by rw [hc];exact h1⟩
      simpa only [e,S,referenceStep,canonicalCGStep,cgStep,cgLine,cgOperator,Fin.mk.injEq,zero_ne_one,ite_false] using hh
    have hmiss1 : inner ℝ e (S (xrfcReferenceMiss trial (cgOperator base) g 1))=0 := by
      rw [xrfcReferenceMiss_canonical trial base hb g 1 (by rw [hc];exact h1),inner_smul_right]
      change _*inner ℝ e (S (referenceStep (cgOperator base) g 1))=0
      rw [hstep1,mul_zero]
    rw [xrfcReferenceMidpointDrift_interior trial base hb u hc (fun i hi=>(ht i hi).ne') 0 h1]
    simp only [xrfcPreviousMiss,ite_true,zero_add,map_smul,map_add,map_sub,inner_smul_right,
      inner_add_right,inner_sub_right]
    change (1/2:ℝ)*(inner ℝ e (S (referenceStep (cgOperator base) g 0))+
      (inner ℝ e (S (referenceStep (cgOperator base) g 1))-
        inner ℝ e (S (xrfcReferenceMiss trial (cgOperator base) g 1))))=_
    rw [h0,hstep1,hmiss1]
    ring
  · have hn1 : n=1 := by omega
    have hh := xrfcReferenceMidpointDrift_terminal trial base hb u hc hn ht
    rw [show n-1=0 by omega] at hh
    simp only [xrfcPreviousMiss,ite_true,zero_add] at hh
    rw [hh,map_smul,inner_smul_right]
    change (1/2:ℝ)*inner ℝ e (S (referenceStep (cgOperator base) g 0))=_
    rw [h0]
    ring

/-- The transpose of the first real oblique flag maps its true first
unit direction exactly to the actual boundary row. Article: prop:EL. -/
theorem xrfc_first_projector_transpose_unit
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : E) (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) g i)≠0) :
    cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) 0)ᵀ (canonicalCGUnitStep base g 0)=
      xrfcFlagRow trial base g 0 := by
  rw [cgOperator_transpose,xrfc_projector_row_block trial base hb g hc ht 0 hn,exploredFlag_zero]
  simp only [Submodule.starProjection_bot,zero_add,InnerProductSpace.adjoint_rankOne,InnerProductSpace.rankOne_apply]
  rw [real_inner_self_eq_norm_sq,(canonicalCG_frame_of_full_atoms base hb g hc).norm_eq_one ⟨0,hn⟩,one_pow,one_smul]

/-- The actual first oblique transpose amplification is exactly the
printed spectral norm of the true projector. Article: prop:EL. -/
theorem xrfc_first_projector_transpose_norm
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : E) (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) g i)≠0) :
    ‖cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) 0)ᵀ (canonicalCGUnitStep base g 0)‖=
      ‖cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) 0)‖ := by
  rw [xrfc_first_projector_transpose_unit trial base hb g hc hn ht,xrfc_projector_norm trial base hb g hc ht 0 hn]

end
end krylov.Convergence
