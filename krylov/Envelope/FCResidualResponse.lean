import krylov.Envelope.FCResidualVariation
import krylov.Envelope.PrefixResponseCoordinates
import krylov.Envelope.TiltSplitting
import krylov.Variation.FCResponse

set_option autoImplicit false
/-!
Article: main_krylov, apB:eq:nu and cor:lm, actual finite-prefix FC residual response.
Use: identify the true observed residual-variation vector of the genuine
full-memory FC executor with the printed old-flag response on its actual
finite remaining-step tails, before and at exhaustion.
Source: actual FC residual-staircase differentiation, genuine canonical
affine paths and the true finite-prefix CG response coordinate identities.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- The genuine observed residual variation of actual full-memory FC on the true source canonical increment path is exactly its finite-prefix triangular old-flag response.
Use: The genuine observed residual variation of actual full-memory FC on the true source canonical increment path is exactly its finite-prefix triangular old-flag response.
Article: main_krylov, apB:eq:nu and cor:lm, actual finite-prefix FC residual response.
Proof: Differentiate the actual executed FC residual staircase on the genuine symmetric affine canonical path. True cumulative-drift differences and real metric pairing identify every actual reference-step coordinate. The genuine finite-prefix projector and actual nonzero CG step normalizers then identify the true residual vector, without an ambient full-basis premise. -/
theorem canonicalFC_residualVariation (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : N≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l, (E l).IsSymm) :
    residualVariation base g (fcMethod fullMemory) (canonicalFCPath base E) (canonicalFCPath base E) N=
      partialCycleResponse base g N E := by
  -- Use the actual canonical affine segment path and the genuine finite-prefix old-flag response.
  let A := canonicalFCPath base E
  let F := partialCycleResponse base g N E
  have hfix : (exploredFlag base g N).starProjection F=F :=
    (exploredFlag base g N).starProjection_eq_self_iff.mpr (partialCycleResponse_mem base g N E)
  have hpre (i : ℕ) (hi : i<N) : CG.gradient (cgOperator base) g i≠0 := cg_nonstagnation base hb g i (hi.trans_le hN)
  have hactual (t : ℝ) (i : ℕ) : probedStep (fcMethod fullMemory) (A t) (A t) g i=fcStep fullMemory (A t) g i := by
    change fcStep fullMemory (A t) g i+0=_
    exact add_zero _
  -- The exact real FC residual staircase supplies each true coordinate before exhaustion; no terminal-gradient cancellation is imposed.
  have hres (i : ℕ) (hi : i<N) :
      deriv (fun t => inner ℝ (probedStep (fcMethod fullMemory) (A t) (A t) g i)
        (probedGradient (fcMethod fullMemory) (A t) (A t) g N)) 0=inner ℝ (canonicalCGStep base g i) F := by
    have heq : (fun t => inner ℝ (probedStep (fcMethod fullMemory) (A t) (A t) g i)
        (probedGradient (fcMethod fullMemory) (A t) (A t) g N))=
        fun t => inner ℝ (fcStep fullMemory (A t) g i) (fcGradient fullMemory (A t) g N) := by
      funext t
      rw [hactual]
      rfl
    rw [heq]
    have hd := fullFC_residual_firstVariation A (cumulativeDrift base E) g
      (fun j => (canonicalFCPath_calculus base E j).1) (fun j => (canonicalFCPath_calculus base E j).2)
      (canonicalFCPath_symmetric base hb E hE) (cgOperator base) (canonicalFCPath_zero base E)
      (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 N hpre hi
    rw [hd,partialCycleResponse_coordinates base hb g hN E hi]
    apply sum_congr rfl
    intro j hj
    rw [cumulativeDrift_sub base E (by have := mem_Ico.mp hj;omega)]
    exact metric_drift_pairing base _ _ _
  -- Compare the real finite vectors through their genuine explored-flag orthogonal coordinates.
  change residualVariation base g (fcMethod fullMemory) A A N=F
  rw [← hfix,exploredFlag_projection base hb g hN,residualVariation]
  apply sum_congr rfl
  intro i _
  have hr : ‖canonicalCGStep base g i.val‖≠0 := norm_ne_zero_iff.mpr
    (canonicalCGStep_ne_zero base hb g i.val (fun j hj => hpre j (hj.trans_lt i.isLt)))
  have hunit : canonicalCGStep base g i.val=‖canonicalCGStep base g i.val‖ • canonicalCGUnitStep base g i.val :=
    (NormedSpace.norm_smul_normalize _).symm
  have hh := hres i.val i.isLt
  change deriv (fun t => inner ℝ (probedStep (fcMethod fullMemory) (A t) (A t) g i.val)
      (probedGradient (fcMethod fullMemory) (A t) (A t) g N)) 0=inner ℝ (canonicalCGStep base g i.val) F at hh
  rw [hunit,real_inner_smul_left] at hh
  rw [hh]
  congr 1
  exact mul_div_cancel_left₀ _ hr
end
end krylov.Envelope
