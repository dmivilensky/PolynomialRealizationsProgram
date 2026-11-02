import krylov.Envelope.CanonicalMissedDirection
import krylov.Envelope.TrialReferenceSums
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, actual canonical trial amplitudes.
Use: normalize original physical missed-direction increment sums by the genuine inverse metric root and identify the printed actual trial-error and square-root-energy coefficients.
Source: proved real root congruence action, positive true CG line lengths and genuine normalized canonical step energy.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped BigOperators
variable {n : ℕ}

/-- The actual inverse-root image of every genuine finite weighted physical missed-direction increment sum equals its printed canonical energy-normalized action sum.
Use: The actual inverse-root image of every genuine finite weighted physical missed-direction increment sum equals its printed canonical energy-normalized action sum.
Article: main_krylov, thm:E1, actual canonical trial amplitudes.
Proof: Apply the genuine missed-direction root identity term by term and collect the actual real scalar factors. -/
theorem canonical_weighted_missed_sum (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (r : ℕ) (hr : r≤referenceAtomCount base hb g)
    (c rho : ℕ → ℝ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (∑ l∈Finset.range r,c l • cgOperator (metricRoot base*E l*metricRoot base)
        (rho l • CG.direction (cgOperator base) g l))=
    ∑ l∈Finset.range r,(c l*(rho l/CG.length (cgOperator base) g l)*Real.sqrt (cgEnergy base g l)) •
      cgOperator (E l) (canonicalCGUnitStep base g l) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [map_smul,canonical_missed_direction_action base hb g l ((Finset.mem_range.mp hl).trans_le hr)]
  simp only [smul_smul,mul_assoc]

/-- The actual chronological output trial amplitude built from genuine measured CG lines, true reference trials and original canonical step energies.
Use: The actual chronological output trial amplitude built from genuine measured CG lines, true reference trials and original canonical step energies.
Article: main_krylov, thm:E1, actual canonical trial amplitudes.
Proof: Multiply the genuine later-correction product, actual relative missed line and square-root measured energy. -/
def xrfcTrialCoefficient (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N l : ℕ) : ℝ :=
  let tau := fun j => trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g j)
  let rho := fun j => CG.length (cgOperator base) g j-tau j
  trialTailFactor tau rho N l*(rho l/CG.length (cgOperator base) g l)*Real.sqrt (cgEnergy base g l)

/-- The genuine measured output trial amplitude equals exactly the original printed signed product times relative trial error and square-root energy.
Use: The genuine measured output trial amplitude equals exactly the original printed signed product times relative trial error and square-root energy.
Article: main_krylov, thm:E1, actual canonical trial amplitudes.
Proof: Use the true nonzero measured CG line to rewrite its relative missed component, then collect the original chronological factors. -/
theorem xrfcTrialCoefficient_printed (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N l : ℕ) (hl : l<referenceAtomCount base hb g) :
    let tau := fun j => trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g j)
    xrfcTrialCoefficient trial base g N l=
      (-1:ℝ)^(N-1-l)*(1-tau l/CG.length (cgOperator base) g l)*
        (∏ j∈Finset.Ico (l+1) N,(CG.length (cgOperator base) g j-tau j)/tau j)*Real.sqrt (cgEnergy base g l) := by
  -- Rewrite the genuine relative missed component only after its true positive CG line domain has been proved.
  have hp := cgOperator_positive base hb
  have ha : CG.length (cgOperator base) g l≠0 :=
    (CG.invariant_line_pos _ hp.2 g l (CG.invariant _ hp.1 hp.2 g l
      (fun i hi => cg_nonstagnation base hb g i (hi.trans hl))) (cg_nonstagnation base hb g l hl)).2.1.ne'
  dsimp only [xrfcTrialCoefficient,trialTailFactor]
  rw [sub_div,div_self ha]
  ring
end
end krylov.Envelope
