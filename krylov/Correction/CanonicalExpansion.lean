import krylov.Correction.CanonicalCoefficient
import krylov.Stability.CanonicalRegularity

/-!
Article: main_krylov, thm:C, the genuine canonical second-order RFC expansion.
Use: close the source geometric formula for the actual full-memory RFC
executor on analytic physical perturbations with arbitrary intermediate corrections.
Source: the derived actual physical cubic expansion and the exact reference
coefficient identification; all true gate and inverse domains were discharged
from genuine nonstagnating quadratic execution in the preceding modules.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Reference krylov.Variation krylov.Envelope
  krylov.Methods krylov.Secant krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The real full RFC cycle has exactly the source staircase/fresh-defect expansion with a genuine cubic remainder.
Use: apply the source second-order coefficient and sharp norm bound to the
actual algorithm, rather than to an assumed model trajectory.
Article: main_krylov, thm:C, A^(−1/2)g_n=−‖ŝ_last‖𝓛f̂+O(ω³).
Proof: the primitive canonical increment and correction families give the
actual analytic physical query operators. Their genuine common quadratic
reference discharges every prefix domain in the proved physical expansion.
The exact actual reference coefficient equals the geometric staircase/fresh
defect, and the fixed genuine inverse root preserves the cubic remainder. -/
theorem full_canonical_second_order {k : ℕ}
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
      (probedGradient (rfcMethod fullMemory 1) (A z) (B z) g (k+1))+
      ‖canonicalCGStep base g k‖ • staircaseOperator base g (E z) (F z k) (k+1)
        (freshDefect base g (E z) (k+1))) =O[𝓝 (0 : X)] (fun z => ‖z‖^3) := by
  -- Primitive canonical operators supply the actual analytic query family and its genuine reference values.
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
  have hn := full_physical_second_order A B (fun _ => g) hA hB analyticAt_const
    (fun z i => canonicalFCPath_symmetric base hb (E z) (hEsym z) 1 i)
    (cgOperator base) hA0 hB0 hpos.1 hpos.2 hk hpre
  let U := referenceModelBasis base g k
  let H := pairModel U (probedImageBasis (rfcMethod fullMemory 1)
    (fun _ => cgOperator base) (fun _ => cgOperator base) g k)
  let R := fullBasisMatrix U
  let L := fun z => Matrix.of fun i j : Fin (k+1) => inner ℝ (U i)
    ((B z k-A z (k-(min i j).val)) (U j))
  have hn' : (fun z => probedGradient (rfcMethod fullMemory 1) (A z) (B z) g (k+1)+
      Matrix.toEuclideanCLM (𝕜 := ℝ) (Rᵀ⁻¹*(L z*H⁻¹))
        (frozenIncoming (cgOperator base) g (A z) k)) =O[𝓝 (0 : X)] (fun z => ‖z‖^3) := by
    simpa only [hA0,hB0,U,H,R,L,referenceModelBasis] using hn
  -- The fixed true inverse root transports the genuine cubic remainder; its leading coefficient cancels exactly.
  have ho := operator_action_order (fun _ : X => cgOperator (metricRoot base)⁻¹) _
    (fun _ => 1) (fun z => ‖z‖^3) (continuousAt_const.tendsto.isBigO_one ℝ) hn'
  have ho' : (fun z => cgOperator (metricRoot base)⁻¹
      (probedGradient (rfcMethod fullMemory 1) (A z) (B z) g (k+1)+
        Matrix.toEuclideanCLM (𝕜 := ℝ) (Rᵀ⁻¹*(L z*H⁻¹))
          (frozenIncoming (cgOperator base) g (A z) k))) =O[𝓝 (0 : X)] (fun z => ‖z‖^3) := by
    simpa only [one_mul] using ho
  apply ho'.congr_left
  intro z
  rw [map_add]
  exact congrArg (_+·) (native_coefficient_canonical base hb g hN (E z) (F z k))

end
end krylov.Correction
