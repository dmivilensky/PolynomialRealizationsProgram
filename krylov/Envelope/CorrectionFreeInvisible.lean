import krylov.Envelope.CorrectionFreeHiddenScenario
import krylov.Envelope.InvisibleRemainder

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), the actual universal correction-free invisible fibre.
Use: identify the genuine explored first variation of every actual correction-free smooth source method on the full printed invisible-scenario subspace.
Source: actual absorbed information forcing, true hidden-prefix exact execution, real finite-scenario first-variation linearity and the genuine fresh-defect action.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- On every genuine invisible scenario every actual correction-free smooth method has exactly the true fresh response minus the common tilt.
Use: On every genuine invisible scenario every actual correction-free smooth method has exactly the true fresh response minus the common tilt.
Article: main_krylov, apB:lem:mu(d), the actual universal correction-free invisible fibre.
Proof: Subtract the actual absorbed scenario. Its real remainder has exactly zero earlier CG probes and the genuine fresh final action; actual source differentiation and linearity add it to the forced absorbed response. -/
theorem correctionFree_invisible_scenario_variation (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (hfree : Methods.CorrectionFree M.policy)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hk : 0<k) (hcount : k+1≤referenceAtomCount base hb g) (Θ : CanonicalScenario n (k+1))
    (hE : ∀ i,(Θ.1 i).IsSymm)
    (hInv : InvisibleIncrements base g (matrixSequenceExtension ((k+1)-1) Θ.1) (k+1)) :
    scenarioVariation M.policy base g (k+1) Θ=
      Real.sqrt (cgEnergy base g k) •
        freshDefect base g (matrixSequenceExtension ((k+1)-1) Θ.1) (k+1)-
      commonTilt base g (canonicalFCPath base (matrixSequenceExtension ((k+1)-1) Θ.1)) (k+1) := by
  -- Split the genuine source scenario into its actual absorbed information fibre and the real hidden remainder.
  let E := matrixSequenceExtension ((k+1)-1) Θ.1
  let Ξ := Θ-absorbedScenario base g Θ
  have hExt : matrixSequenceExtension ((k+1)-1) Ξ.1=
      fun l => E l-absorbedIncrements base g E l := by
    change matrixSequenceExtension ((k+1)-1) (Θ.1-(absorbedScenario base g Θ).1)=_
    rw [matrixSequenceExtension_sub,absorbedScenario_extension]
  have hprefix (j : ℕ) (hj : j<k) :
      cgOperator (∑ l∈Finset.range j,matrixSequenceExtension ((k+1)-1) Ξ.1 l)
        (canonicalCGUnitStep base g j)=0 := by
    rw [hExt]
    exact invisible_remainder_prefix_action base hb g E (k+1) hcount hInv j (by omega)
  -- The whole newest remainder action is exactly the genuine chronological fresh defect.
  have hLast : cgOperator (∑ l∈Finset.range k,matrixSequenceExtension ((k+1)-1) Ξ.1 l)
      (canonicalCGUnitStep base g k)=freshDefect base g E (k+1) := by
    rw [hExt]
    simpa only [Nat.add_sub_cancel] using remainder_last_action_freshDefect base hb g E (k+1) (by omega) hcount
  have horth : inner ℝ (canonicalCGUnitStep base g k)
      (cgOperator (∑ l∈Finset.range k,matrixSequenceExtension ((k+1)-1) Ξ.1 l) (canonicalCGUnitStep base g k))=0 := by
    rw [hLast]
    have hz := freshDefect_last_coordinate_zero base hb g hcount (show 0<k+1 by omega) E
    change inner ℝ (canonicalCGStep base g k) (freshDefect base g E (k+1))=0 at hz
    change inner ℝ (‖canonicalCGStep base g k‖⁻¹ • canonicalCGStep base g k) (freshDefect base g E (k+1))=0
    rw [real_inner_smul_left,hz,mul_zero]
  -- Differentiate the actual exact hidden-prefix execution, then add the forced true absorbed response by linearity.
  have hv := correctionFree_hidden_scenario_projection M hfree base hb g k hcount Ξ hprefix horth
  rw [hLast,Submodule.starProjection_eq_self_iff.mpr
    (exploredFlag_mono base g (show k+1-1≤k+1 by omega) (freshDefect_mem base g E (k+1)))] at hv
  have ha := forced_absorbed_scenarioVariation M base hb g (k+1) (by omega) hcount Θ hE
  change scenarioVariation M.policy base g (k+1) (Θ-absorbedScenario base g Θ)=_ at hv
  rw [map_sub,ha,sub_neg_eq_add] at hv
  exact eq_sub_of_add_eq hv
end
end krylov.Envelope
