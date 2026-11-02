import krylov.Envelope.FreshDefect
import krylov.Variation.FCResponse

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), actual fresh-defect residual coordinates.
Use: identify genuine chronological physical segment-defect pairings with
the real source fresh-defect vector and true last-step energy factor.
Source: existing genuine metric drift pairing and actual old-flag finite
CG coordinate sums with true canonical step normalization.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every genuine old reference-step/fresh-segment pairing is exactly the true canonical step coordinate of square-root last energy times the actual fresh defect.
Use: Every genuine old reference-step/fresh-segment pairing is exactly the true canonical step coordinate of square-root last energy times the actual fresh defect.
Article: main_krylov, apB:lem:mu(d), actual fresh-defect residual coordinates.
Proof: Use the real cumulative increment difference and existing genuine metric pairing. Normalize the actual last CG step and identify its true old-flag suffix coordinates. -/
theorem freshDefect_physical_coordinates (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hN : k+1≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (i : ℕ) (hi : i<k) :
    inner ℝ (referenceStep (cgOperator base) g i)
      ((cumulativeDrift base E k-cumulativeDrift base E i) (referenceStep (cgOperator base) g k))=
    inner ℝ (canonicalCGStep base g i)
      (Real.sqrt (cgEnergy base g k) • freshDefect base g E (k+1)) := by
  -- Reuse the genuine cumulative drift and metric pairing identities before the actual last-step normalization.
  rw [cumulativeDrift_sub base E hi.le,metric_drift_pairing]
  have hs : Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (referenceStep (cgOperator base) g k)=
      Real.sqrt (cgEnergy base g k) • canonicalCGUnitStep base g k := by
    rw [cgEnergy_sqrt base hb]
    exact (NormedSpace.norm_smul_normalize _).symm
  rw [hs,map_smul,real_inner_smul_right,real_inner_smul_right,
    freshDefect_step_coordinate base hb g hN E i (by omega)]
  congr 1
  change inner ℝ (canonicalCGStep base g i)
    (cgOperator (∑ l∈Ico i k,E l) (canonicalCGUnitStep base g k))=_
  simp only [cgOperator,map_sum,_root_.sum_apply,inner_sum,Nat.add_sub_cancel]
end
end krylov.Envelope
