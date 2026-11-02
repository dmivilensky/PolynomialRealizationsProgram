import krylov.Correction.NativeExpansion
import krylov.Correction.RepeatedFactors

/-!
Article: main_krylov, thm:C2(b), actual repeated terminal corrections.
Use: connect the fixed-model product calculus to the true RFC prefix, with
independently queried terminal correction operators and derived error orders.
Source: fixed-model iterative refinement (Moler67, Higham02), here proved
for the actual measured model and actual updated query gradients.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Execute the terminal fixed-model queries after the genuine repeated-RFC prefix.
Use: each correction has its own physical operator and uses its preceding observed gradient.
Article: main_krylov, thm:C2(b), independently varying last correction segments. -/
def repeatedTerminalResult (count : ℕ) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ)
    (C : ℕ → E →L[ℝ] E) : CorrectionResult E :=
  let m := rfcMethod fullMemory count (E := E)
  let U := probedStepBasis m A B g k
  let H := pairModel U (probedImageBasis m A B g k)
  modelQueries U H C count (fullPostSearch count A B g k)

/-- Constant terminal query operators recover the actual returned repeated-RFC gradient locally.
Use: the more general execution agrees with the original method on its derived gate domain.
Article: main_krylov, thm:C2(b), actual RFC execution identity.
Proof: the actual observed gate accepts near the genuine quadratic prefix;
the repeated query executor is exactly the existing repeated model tree. -/
theorem repeatedTerminalResult_constant_eventually (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hk : 0<k) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    ∀ᶠ z in 𝓝 (0 : X),
      (repeatedTerminalResult count (A z) (B z) (g z) k (fun _ => B z k)).gradient=
        probedGradient (rfcMethod fullMemory count) (A z) (B z) (g z) (k+1) := by
  filter_upwards [full_phase_execution_eventually count A B g hA hB hg Q hA0 hB0 hQ hpos k hk hpre]
    with z hz
  rw [probedGradient_succ,hz]
  exact (modelQueries_constant _ _ _ _ _).2.1

/-- The actual repeated terminal corrections have their full native leading product and higher-order remainder.
Use: all factor and incoming-vector error premises follow from the genuine prefix, including its higher-order residual.
Article: main_krylov, thm:C2(b), native ordered product with O(ω^(k_c+2)) remainder.
Proof: genuine prefix regularity and pair-discrepancy estimates give each
independently queried model-error factor. Its frozen linear part vanishes at
the common quadratic base. The actual prefix supplies the incoming fresh
vector to quadratic order. Apply the proved query-execution product theorem.
-/
theorem full_repeated_projected_order (count : ℕ) (hc : 0<count)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (C : ℕ → X → E →L[ℝ] E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (hC : ∀ j<count, AnalyticAt ℝ (C j) 0)
    (hAsym : ∀ z i, (A z i).toLinearMap.IsSymmetric)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hC0 : ∀ j<count, C j 0=Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hk : 0<k) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    let m := rfcMethod fullMemory count (E := E)
    let U := fun z => probedStepBasis m (A z) (B z) (g z) k
    let H := fun z => pairModel (U z) (probedImageBasis m (A z) (B z) (g z) k)
    let L := fun j z => Matrix.of fun a b =>
      inner ℝ (U 0 a) ((C j z-A z (k-(min a b).val)) (U 0 b))
    (fun z => projectedResidual (U z)
        (repeatedTerminalResult count (A z) (B z) (g z) k (fun j => C j z)).gradient-
      correctionRun (fun j z => Matrix.toEuclideanCLM (𝕜 := ℝ) (L j z*(H 0)⁻¹))
        (fun z => frozenIncoming Q (g 0) (A z) k) count z) =O[𝓝 (0 : X)]
          (fun z => ‖z‖^(count+2)) := by
  -- Actual observed columns and images discharge every model-error premise.
  let m := rfcMethod fullMemory count (E := E)
  let U := fun z => probedStepBasis m (A z) (B z) (g z) k
  let Z := fun z => probedImageBasis m (A z) (B z) (g z) k
  let H := fun z => pairModel (U z) (Z z)
  let L := fun j z => Matrix.of fun a b =>
    inner ℝ (U 0 a) ((C j z-A z (k-(min a b).val)) (U 0 b))
  have hd := full_cycle_data_regular count A B g hA hB hg Q hA0 hB0 hQ hpos k hpre
  have hN (j : ℕ) (hj : j<count) :
      (fun z => correctionCompression (U z) (C j z)-H z-L j z) =O[𝓝 (0 : X)]
        (fun z => ‖z‖^2) := by
    apply observed_model_error_order U Z (fun z (i : Fin (k+1)) => A z (k-i.val)) (C j)
      hd.2.1 (fun i => hA (k-i.val)) (hC j hj)
    · exact fun z i => hAsym z (k-i.val)
    · intro i
      rw [hC0 j hj,hA0]
    · exact full_image_discrepancy_order count A B g hA hB hg Q hA0 hB0 hQ hpos k hpre
  have hL (j : ℕ) (hj : j<count) : L j =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
    have ha : AnalyticAt ℝ (L j) 0 := analytic_spectral_matrix _ 0 fun a b =>
      analytic_inner analyticAt_const
        (analytic_operator_apply ((hC j hj).sub (hA (k-(min a b).val))) analyticAt_const)
    have hz : L j 0=0 := by
      ext a b
      simp only [L,hC0 j hj,hA0,sub_self,_root_.zero_apply,inner_zero_right,Matrix.of_apply,Matrix.zero_apply]
    simpa only [hz,sub_zero] using analytic_reference_order _ ha
  exact modelQueries_product_order U H C _ _ L count hd.2.2.2
    (full_model_unit_eventually count A B g hA hB hg Q hA0 hB0 hQ hpos k hpre).1 hN hL
    (full_incoming_vector_order A B g hA hB hg hAsym Q hA0 hB0 hQ hpos k hk hpre count hc)
    (frozenIncoming_order A hA Q hA0 (g 0) k)

end
end krylov.Correction
