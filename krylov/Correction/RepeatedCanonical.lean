import krylov.Correction.RepeatedCoefficient
import krylov.Stability.CanonicalRegularity

/-!
Article: main_krylov, thm:C2(b), the actual canonical repeated-RFC expansion.
Use: derive the source signed staircase product for independently varying
terminal correction queries from the original analytic curvature increments.
Source: the actual higher-order prefix and terminal execution estimates,
with exact cancellation in the genuine common CG reference frame.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Variation krylov.Envelope
  krylov.Methods krylov.Secant krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The genuine repeated-RFC terminal execution has the signed ordered canonical product and the source higher-order remainder.
Use: independent terminal correction segments are allowed, while all earlier corrections belong to the actual repeated RFC prefix.
Article: main_krylov, thm:C2(b), A^(−1/2)g_n=(−1)^k_c‖e_last‖_A𝓛_k_c⋯𝓛_1f̂+O(ω^(k_c+2)).
Proof: the original canonical increments define analytic physical query
operators with the genuine common quadratic base. The proved actual
repeated execution and reconstruction give its native physical product.
Every correction count has the same true CG reference columns and Gram.
Apply the fixed inverse root and identify the coefficient by exact ordered
reference cancellation, retaining every independent terminal operator.
-/
theorem full_repeated_canonical_order {k : ℕ} (count : ℕ) (hc : 0<count)
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (E F : X → ℕ → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (T : ℕ → X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hE : ∀ i, AnalyticAt ℝ (fun z => E z i) 0)
    (hF : ∀ i, AnalyticAt ℝ (fun z => F z i) 0)
    (hT : ∀ j<count, AnalyticAt ℝ (T j) 0)
    (hE0 : ∀ i, E 0 i=0) (hF0 : ∀ i, F 0 i=0)
    (hT0 : ∀ j<count, T j 0=0) (hEsym : ∀ z i, (E z i).IsSymm) :
    let A := fun z => canonicalFCPath base (E z) 1
    let B := fun z i => canonicalCorrectionOperator base (E z) (F z i) i
    let C := fun j z => canonicalCorrectionOperator base (E z) (T j z) k
    (fun z => cgOperator (metricRoot base)⁻¹
        (repeatedTerminalResult count (A z) (B z) g k (fun j => C j z)).gradient-
      ((-1 : ℝ)^count*‖canonicalCGStep base g k‖) •
        (chebyshev1.orderedProduct (fun j => staircaseOperator base g (E z) (T j z) (k+1)) count)
          (freshDefect base g (E z) (k+1))) =O[𝓝 (0 : X)] (fun z => ‖z‖^(count+2)) := by
  -- Construct the actual primitive physical queries and their true reference domains.
  let A := fun z => canonicalFCPath base (E z) 1
  let B := fun z i => canonicalCorrectionOperator base (E z) (F z i) i
  let C := fun j z => canonicalCorrectionOperator base (E z) (T j z) k
  have hA (i : ℕ) : AnalyticAt ℝ (fun z => A z i) 0 :=
    canonicalFCPath_analyticAt (fun _ => base) E 0 analyticAt_const
      (Eventually.of_forall fun _ => hb) hE i
  have hB (i : ℕ) : AnalyticAt ℝ (fun z => B z i) 0 := by
    have hm : AnalyticAt ℝ (fun z => metricRoot base*F z i*metricRoot base) 0 :=
      (analyticAt_const.mul (hF i)).mul analyticAt_const
    exact (hA i).add ((matrixOperator_contDiffAt _ 0 hm.contDiffAt).analyticAt)
  have hC (j : ℕ) (hj : j<count) : AnalyticAt ℝ (C j) 0 := by
    have hm : AnalyticAt ℝ (fun z => metricRoot base*T j z*metricRoot base) 0 :=
      (analyticAt_const.mul (hT j hj)).mul analyticAt_const
    exact (hA k).add ((matrixOperator_contDiffAt _ 0 hm.contDiffAt).analyticAt)
  have hA0 : A 0=(fun _ => cgOperator base) := canonicalFCPath_at_zero base (E 0) hE0
  have hB0 : B 0=(fun _ => cgOperator base) := by
    funext i
    simp only [B,canonicalCorrectionOperator,hF0,Matrix.mul_zero,Matrix.zero_mul,cgOperator,map_zero,add_zero]
    exact congrFun hA0 i
  have hC0 (j : ℕ) (hj : j<count) : C j 0=cgOperator base := by
    simp only [C,canonicalCorrectionOperator,hT0 j hj,Matrix.mul_zero,Matrix.zero_mul,cgOperator,map_zero,add_zero]
    exact congrFun hA0 k
  have hpos := cgOperator_positive base hb
  have hpre (i : ℕ) (hi : i≤k) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (by omega)
  have hn := full_repeated_physical_order count hc A B (fun _ => g) C hA hB analyticAt_const hC
    (fun z i => canonicalFCPath_symmetric base hb (E z) (hEsym z) 1 i)
    (cgOperator base) hA0 hB0 hC0 hpos.1 hpos.2 hk hpre
  let U := referenceModelBasis base g k
  let R := fullBasisMatrix U
  let H := pairModel U (fun i => cgOperator base (U i))
  let L := fun j z => Matrix.of fun a b : Fin (k+1) => inner ℝ (U a)
    ((C j z-A z (k-(min a b).val)) (U b))
  let v := fun z => correctionRun (fun j z => cgOperator (L j z*H⁻¹))
    (fun z => frozenIncoming (cgOperator base) g (A z) k) count z
  have hn' : (fun z => (repeatedTerminalResult count (A z) (B z) g k (fun j => C j z)).gradient-
      cgOperator Rᵀ⁻¹ (v z)) =O[𝓝 (0 : X)] (fun z => ‖z‖^(count+2)) := by
    apply hn.congr_left
    intro z
    simp only [hA0,hB0,quadratic_imageBasis,referenceModelBasis_count count base hb]
    rfl
  -- Transport the actual remainder and cancel all intermediate reference coordinates exactly.
  have ho := operator_action_order (fun _ : X => cgOperator (metricRoot base)⁻¹) _
    (fun _ => 1) (fun z => ‖z‖^(count+2)) (continuousAt_const.tendsto.isBigO_one ℝ) hn'
  have ho' : (fun z => cgOperator (metricRoot base)⁻¹
      ((repeatedTerminalResult count (A z) (B z) g k (fun j => C j z)).gradient-
        cgOperator Rᵀ⁻¹ (v z))) =O[𝓝 (0 : X)] (fun z => ‖z‖^(count+2)) := by
    simpa only [one_mul] using ho
  apply ho'.congr_left
  intro z
  rw [map_sub]
  congr 1
  change cgOperator (metricRoot base)⁻¹ (cgOperator Rᵀ⁻¹
    (correctionRun (fun j z => cgOperator (L j z*H⁻¹))
      (fun z => frozenIncoming (cgOperator base) g (A z) k) count z))=_
  rw [correctionRun_freeze]
  simpa only [quadratic_imageBasis,referenceModelBasis_count 1 base hb,U,R,H,L,A,C] using
    native_repeated_coefficient_canonical base hb g hN (E z) (fun j => T j z) count

end
end krylov.Correction
