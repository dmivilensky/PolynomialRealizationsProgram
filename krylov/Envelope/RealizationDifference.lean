import krylov.Envelope.FCResidualResponse
import krylov.Envelope.RFCResidualVariation
import krylov.Methods.FCSmoothClass
import krylov.Methods.RFCSmoothClass

set_option autoImplicit false
/-!
Article: main_krylov, cor:lm(b), apB:eq:nu and thm:select, actual FC/RFC transverse comparison.
Use: identify the true full-memory RFC explored component with minus the
genuine common tilt and the actual FC/RFC difference with the printed
finite-prefix old-flag response, with primitive smooth membership derived from their real coefficients.
Source: complete raw-method tilt splitting, genuine executed FC residual
response and proved actual positive-correction RFC residual derivatives.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Variation
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Actual full-memory RFC has exactly minus the true common frozen tilt as its real explored gradient variation.
Use: Actual full-memory RFC has exactly minus the true common frozen tilt as its real explored gradient variation.
Article: main_krylov, cor:lm(b), apB:eq:nu and thm:select, actual FC/RFC transverse comparison.
Proof: Derive actual primitive RFC smooth membership from its genuine coefficients and apply the proved actual raw-method residual/tilt decomposition to the genuine globally CG-consistent span-restricted RFC executor. Its real recorded-residual variation is exactly zero by the true projected-residual order theorem. -/
theorem fullRFC_tilt (count : ℕ) (hc : 0<count)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (A B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ i, AnalyticAt ℝ (fun t => A t i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun t => B t i) 0)
    (hA0 : A 0=fun _ => cgOperator base) (hB0 : B 0=fun _ => cgOperator base)
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) :
    (exploredFlag base g N).starProjection
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
        (deriv (fun t => probedGradient (rfcMethod fullMemory count) (A t) (B t) g N) 0))=
      -commonTilt base g A N := by
  have hm := rfcMethod_consistent fullMemory (fun _ hk => hk) count (E := EuclideanSpace ℝ (Fin n))
  -- Primitive smooth membership is derived for the actual RFC policy, rather than supplied as a comparison hypothesis.
  have hsmooth := rfcMethod_smoothCycleAt fullMemory count (cgOperator base) (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 g (fun _ _ hk => hk) N
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hcount)) 2
  have ht := actual_tilt_splitting fullMemory (rfcMethod fullMemory count) hm
    (rfcMethod_spanRestricted fullMemory count) A B g base hb hA0 hB0 N
    (fun i _ => (hA i).contDiffAt) (fun i _ => (hB i).contDiffAt) hcount hsmooth
  rw [fullRFC_residualVariation_zero count hc base hb g A B hA hB hA0 hB0 N hN hcount,zero_sub] at ht
  exact ht

/-- The true explored gradient variations of actual full-memory FC and RFC differ by exactly the actual finite-prefix old-flag canonical increment response.
Use: The true explored gradient variations of actual full-memory FC and RFC differ by exactly the actual finite-prefix old-flag canonical increment response.
Article: main_krylov, cor:lm(b), apB:eq:nu and thm:select, actual FC/RFC transverse comparison.
Proof: Use the genuine actual tilt decomposition for FC and the true minus-tilt identity for RFC. Both executors have the same actual source path and common frozen tilt, which cancels; the real FC residual vector is the proved genuine finite-prefix response. -/
theorem fullFC_sub_fullRFC_transverse (count : ℕ) (hc : 0<count)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l, (E l).IsSymm)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB : ∀ i, AnalyticAt ℝ (fun t => B t i) 0) (hB0 : B 0=fun _ => cgOperator base)
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) :
    let A := canonicalFCPath base E
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    let P := exploredFlag base g N
    P.starProjection (R (deriv (fun t => probedGradient (fcMethod fullMemory) (A t) (A t) g N) 0))-
      P.starProjection (R (deriv (fun t => probedGradient (rfcMethod fullMemory count) (A t) (B t) g N) 0))=
        partialCycleResponse base g N E := by
  -- Both genuine executors see the same true canonical source path, so their actual common frozen tilt cancels.
  let A := canonicalFCPath base E
  have hm := fcMethod_consistent fullMemory (fun _ hk => hk) (E := EuclideanSpace ℝ (Fin n))
  have hsFC := fcMethod_smoothCycleAt fullMemory (cgOperator base) (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 g (fun _ _ hk => hk) N
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hcount)) 2
  have hFC := actual_tilt_splitting fullMemory (fcMethod fullMemory) hm
    (fcMethod_spanRestricted fullMemory) A A g base hb (canonicalFCPath_zero base E) (canonicalFCPath_zero base E) N
    (fun i _ => (canonicalFCPath_calculus base E i).1.contDiffAt)
    (fun i _ => (canonicalFCPath_calculus base E i).1.contDiffAt) hcount hsFC
  have hRFC := fullRFC_tilt count hc base hb g A B (fun i => (canonicalFCPath_calculus base E i).1) hB
    (canonicalFCPath_zero base E) hB0 N hN hcount
  change _-_=_
  rw [hFC,hRFC,canonicalFC_residualVariation base hb g hcount E hE]
  abel
end
end krylov.Envelope
