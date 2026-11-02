import krylov.Envelope.XRFCReferenceOperatorSums
import krylov.Envelope.CanonicalTrialSums
import krylov.Envelope.XRFCInjectionFormula
import krylov.Envelope.XRFCOutputJet
import krylov.Envelope.CanonicalAbsorption
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1 and eq:virtual-trial-delta, actual printed canonical trial formulas.
Use: connect genuine differentiated XRFC output and virtual injection sums on the original canonical source path to the printed actual trial amplitudes and chronological canonical increments.
Source: actual native virtual coefficients, true physical operator summation by parts and genuine missed-direction root normalization.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped BigOperators
variable {n : ℕ}

/-- Every genuine finite physical canonical increment sum equals its original root-congruence operator on the actual summed canonical matrices.
Use: Every genuine finite physical canonical increment sum equals its original root-congruence operator on the actual summed canonical matrices.
Article: main_krylov, thm:E1 and eq:virtual-trial-delta, actual printed canonical trial formulas.
Proof: Distribute the real root multiplication and actual matrix-to-operator linear identification through the true finite sum. -/
theorem physical_increment_linear_sum (base : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (s : Finset ℕ) :
    (∑ l∈s,(cgOperator (metricRoot base*E l*metricRoot base)).toLinearMap)=
      (cgOperator (metricRoot base*(∑ l∈s,E l)*metricRoot base)).toLinearMap := by
  simp only [cgOperator,Matrix.mul_sum,Matrix.sum_mul,map_sum]
  ext v
  simp

/-- The actual semantic XRFC output-defect first variation on the original canonical source path is exactly the printed trial-amplitude canonical increment sum.
Use: The actual semantic XRFC output-defect first variation on the original canonical source path is exactly the printed trial-amplitude canonical increment sum.
Article: main_krylov, thm:E1 and eq:virtual-trial-delta, actual printed canonical trial formulas.
Proof: Differentiate the genuine constructed primitive path, use actual native-weighted output summation by parts and normalize the true missed CG directions. -/
theorem xrfc_canonical_output_formula (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) (hcount : N≤referenceAtomCount base hb g)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (xrfcOutputJet trial (canonicalFCPath base E) (fun t => canonicalFCPath base E t N) (cgOperator base) g N)=
      ∑ l∈Finset.range N,xrfcTrialCoefficient trial base g N l • cgOperator (E l) (canonicalCGUnitStep base g l) := by
  -- Identify the original primitive physical path derivatives before inserting actual computed reference weights.
  let Q := cgOperator base
  let m := xrfcMethod fullMemory trial (E := EuclideanSpace ℝ (Fin n))
  let tau := fun j => trial (oneGradientRun m (fun _ => Q) g j)
  let rho := fun j => CG.length Q g j-tau j
  let D := fun l => (cgOperator (metricRoot base*E l*metricRoot base)).toLinearMap
  have hp := cgOperator_positive base hb
  have hpre (i : ℕ) (hi : i<N) : CG.gradient Q g i≠0 := cg_nonstagnation base hb g i (hi.trans_le hcount)
  have hout := xrfc_reference_output_increment_sum trial Q hp.1 hp.2 g N hpre ht D
  dsimp only at hout
  have he : xrfcOutputJet trial (canonicalFCPath base E) (fun t => canonicalFCPath base E t N) Q g N=
      ∑ i : Fin N,oneGradientVirtualCoefficients m (fun _ => Q) g N i •
        (∑ l∈Finset.Ico i.val N,D l) (oneGradientStep m (fun _ => Q) g i.val) := by
    unfold xrfcOutputJet
    apply Finset.sum_congr rfl
    intro i _
    rw [(canonicalFCPath_calculus base E N).2.deriv,(canonicalFCPath_calculus base E i.val).2.deriv]
    rw [cumulativeDrift_sub base E i.isLt.le]
    dsimp only [D]
    rw [physical_increment_linear_sum]
    rfl
  rw [he,hout]
  exact canonical_weighted_missed_sum base hb g N hcount (trialTailFactor tau rho N) rho E

/-- The actual differentiated effective injection minus the original CG cumulative injection has exactly the printed canonical virtual-trial-delta formula.
Use: The actual differentiated effective injection minus the original CG cumulative injection has exactly the printed canonical virtual-trial-delta formula.
Article: main_krylov, thm:E1 and eq:virtual-trial-delta, actual printed canonical trial formulas.
Proof: Identify genuine primitive injection derivatives, substitute true computed reference weights, apply actual operator summation by parts and retain the original square-root measured CG energy. -/
theorem xrfc_canonical_trial_delta (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) (hcount : N≤referenceAtomCount base hb g)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g k)) :
    let m := xrfcMethod fullMemory trial
    let tau := fun j => trial (oneGradientRun m (fun _ => cgOperator base) g j)
    let rho := fun j => CG.length (cgOperator base) g j-tau j
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (xrfcInjectionJet trial (canonicalFCPath base E) (cgOperator base) g N-
        ∑ i∈Finset.range N,cumulativeDrift base E i (referenceStep (cgOperator base) g i))=
    ∑ l∈Finset.range (N-1),((rho l/CG.length (cgOperator base) g l)*Real.sqrt (cgEnergy base g l)*
      (1-trialTailFactor tau rho N l)) • cgOperator (E l) (canonicalCGUnitStep base g l) := by
  dsimp only
  let Q := cgOperator base
  let m := xrfcMethod fullMemory trial (E := EuclideanSpace ℝ (Fin n))
  let tau := fun j => trial (oneGradientRun m (fun _ => Q) g j)
  let rho := fun j => CG.length Q g j-tau j
  let D := fun l => (cgOperator (metricRoot base*E l*metricRoot base)).toLinearMap
  have hp := cgOperator_positive base hb
  have hpre (i : ℕ) (hi : i<N) : CG.gradient Q g i≠0 := cg_nonstagnation base hb g i (hi.trans_le hcount)
  -- Differentiate the real executed virtual injection sum using primitive trial charts and genuine reference model domains.
  have hj := xrfc_injection_jet_formula trial (canonicalFCPath base E) g Q hp.1 hp.2
    (canonicalFCPath_zero base E) N (fun i => (canonicalFCPath_calculus base E i).1.contDiffAt) hpre ht
    (by rw [canonicalFCPath_zero];exact hT)
  have hpref (i : ℕ) : (∑ l∈Finset.range i,D l)=(cumulativeDrift base E i).toLinearMap :=
    physical_increment_linear_sum base E (Finset.range i)
  have hinj := xrfc_reference_injection_increment_sum trial Q hp.1 hp.2 g N hpre ht D
  dsimp only at hinj
  simp only [hpref,ContinuousLinearMap.coe_coe] at hinj
  rw [hj]
  simp_rw [(canonicalFCPath_calculus base E _).2.deriv]
  rw [hinj]
  -- Normalize the actual missed CG directions and collect the genuine printed chronological trial factors.
  have he := canonical_weighted_missed_sum base hb g (N-1) ((Nat.sub_le N 1).trans hcount)
    (fun l => 1-trialTailFactor tau rho N l) rho E
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    (∑ l∈Finset.range (N-1),(1-trialTailFactor tau rho N l) •
      cgOperator (metricRoot base*E l*metricRoot base) (rho l • CG.direction (cgOperator base) g l))=_
  rw [he]
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  ring
end
end krylov.Envelope
