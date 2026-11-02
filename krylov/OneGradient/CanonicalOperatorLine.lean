import krylov.OneGradient.XRFCSharp
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, actual arbitrary-operator canonical line dictionary.
Use: normalize the genuine physical direction-basis replay response into the
original printed unit-CG-step amplitudes without a matrix-image relaxation.
Source: actual positive root/inverse cancellation, genuine missed-line CG
energy normalization and the existing original trial coefficient definition.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Envelope
open scoped BigOperators
variable {n : ℕ}

/-- A genuine arbitrary physical operator acting on an actual missed CG line
has precisely its canonical normalized unit-step action.
Use: normalize actual operator derivatives, including the true final output increment.
Article: main_krylov, thm:I.
Proof: insert the actual root/inverse identity, use the genuine canonical
missed-line formula and transport its real scalar through the original operator. -/
theorem canonical_operator_missed_line
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k<referenceAtomCount base hb g)
    (rho : ℝ) (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    let R := cgOperator (metricRoot base)⁻¹
    R (C (rho • CG.direction (cgOperator base) g k))=
      (rho/CG.length (cgOperator base) g k*Real.sqrt (cgEnergy base g k)) •
        (R*C*R) (canonicalCGUnitStep base g k) := by
  let R := cgOperator (metricRoot base)⁻¹
  let root := cgOperator (metricRoot base)
  have hcancel (v : EuclideanSpace ℝ (Fin n)) : R (root v)=v := by
    simp only [R,root,cgOperator,← mul_apply_eq_comp,← map_mul,
      Matrix.nonsing_inv_mul _ (metricRoot_det_unit base hb),map_one,one_apply_eq_self]
  have hline := canonical_missed_line base hb g k hk rho
  calc
    R (C (rho • CG.direction (cgOperator base) g k))=
        (R*C*R) (root (rho • CG.direction (cgOperator base) g k)) := by
      change R (C _)=R (C (R (root _)))
      rw [hcancel]
    _ = _ := by rw [hline,map_smul]

/-- The genuine physical signed replay-response sum normalizes exactly into
the original direction-basis XRFC amplitude response.
Use: keep the real measured reference trials, actual energies and arbitrary
physical increment operators in the source formula.
Article: main_krylov, thm:I, sum a_l E_l shat_l.
Proof: normalize each actual missed CG line by the true positive root
identity, then collect exactly the existing native signed later-trial factor
and genuine relative missed-line/square-root-energy coefficient. -/
theorem canonical_direction_response_sum
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (C : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    let R := cgOperator (metricRoot base)⁻¹
    let tau := fun j => trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g j)
    let rho := fun j => CG.length (cgOperator base) g j-tau j
    R (∑ l∈Finset.range n,trialTailFactor tau rho n l • (rho l • C l (CG.direction (cgOperator base) g l)))=
      xrfcDirectionResponse trial base g (fun l => R*C l*R) := by
  dsimp only
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [map_smul,← map_smul (C l),canonical_operator_missed_line base hb g l
    (by rw [hc];exact Finset.mem_range.mp hl),smul_smul]
  congr 1
  dsimp only [xrfcTrialCoefficient]
  ring

end
end krylov.OneGradient
