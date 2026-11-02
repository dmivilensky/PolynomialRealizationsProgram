import krylov.Correction.RepeatedBound

/-!
Article: main_krylov, thm:C2(b), the original repeated RFC method.
Use: specialize the independently queried terminal expansion to the actual
public repeated RFC executor with its existing observed gate and history.
Source: the proved genuine terminal execution identity and canonical product;
the real accepted neighborhood is derived from the original primitive data.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Reference krylov.Variation krylov.Envelope
  krylov.Methods krylov.Secant krylov.Stability krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The original actual repeated-RFC method has the full signed canonical terminal product and higher-order remainder.
Use: the expansion concerns the real returned gradient, with its real gate and all previous iterations executed.
Article: main_krylov, thm:C2(b), actual RFC_k_c fixed-model iterative refinement.
Proof: construct the genuine analytic probe and correction operators from
the primitive increments. The independently queried terminal expansion uses
the same last correction operator each time. The proved actual gate-execution
identity therefore identifies its output with the original RFC output locally.
-/
theorem full_repeated_rfc_canonical_order {k : ℕ} (count : ℕ) (hc : 0<count)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (E F : X → ℕ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hE : ∀ i, AnalyticAt ℝ (fun z => E z i) 0)
    (hF : ∀ i, AnalyticAt ℝ (fun z => F z i) 0)
    (hE0 : ∀ i, E 0 i=0) (hF0 : ∀ i, F 0 i=0)
    (hEsym : ∀ z i, (E z i).IsSymm) :
    let A := fun z => canonicalFCPath base (E z) 1
    let B := fun z i => canonicalCorrectionOperator base (E z) (F z i) i
    (fun z => cgOperator (metricRoot base)⁻¹
        (probedGradient (rfcMethod fullMemory count) (A z) (B z) g (k+1))-
      ((-1 : ℝ)^count*‖canonicalCGStep base g k‖) •
        (chebyshev1.orderedProduct (fun _ => staircaseOperator base g (E z) (F z k) (k+1)) count)
          (freshDefect base g (E z) (k+1))) =O[𝓝 (0 : X)] (fun z => ‖z‖^(count+2)) := by
  -- The actual primitive data give the genuine accepted repeated-query neighborhood.
  let A := fun z => canonicalFCPath base (E z) 1
  let B := fun z i => canonicalCorrectionOperator base (E z) (F z i) i
  have hA (i : ℕ) : AnalyticAt ℝ (fun z => A z i) 0 :=
    canonicalFCPath_analyticAt (fun _ => base) E 0 analyticAt_const
      (Eventually.of_forall fun _ => hb) hE i
  have hB (i : ℕ) : AnalyticAt ℝ (fun z => B z i) 0 := by
    have hm : AnalyticAt ℝ (fun z => metricRoot base*F z i*metricRoot base) 0 :=
      (analyticAt_const.mul (hF i)).mul analyticAt_const
    exact (hA i).add ((matrixOperator_contDiffAt _ 0 hm.contDiffAt).analyticAt)
  have hA0 : A 0=(fun _ => cgOperator base) := canonicalFCPath_at_zero base (E 0) hE0
  have hB0 : B 0=(fun _ => cgOperator base) := by
    funext i
    simp only [B,canonicalCorrectionOperator,hF0,Matrix.mul_zero,Matrix.zero_mul,cgOperator,map_zero,add_zero]
    exact congrFun hA0 i
  have hpos := cgOperator_positive base hb
  have hpre (i : ℕ) (hi : i≤k) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (by omega)
  have he := repeatedTerminalResult_constant_eventually count A B (fun _ => g)
    hA hB analyticAt_const (cgOperator base) hA0 hB0 hpos.1 hpos.2 k hk hpre
  have hn := full_repeated_canonical_order count hc base hb g hN hk E F (fun _ z => F z k)
    hE hF (fun _ _ => hF k) hE0 hF0 (fun _ _ => hF0 k) hEsym
  apply hn.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [he] with z hz
  rw [hz]

end
end krylov.Correction
