import krylov.Functions.NativeRFCJets
import krylov.Functions.GenuineHessianSymmetry

/-!
Article: main_krylov, lem:cycle-transfer, actual ordinary RFC selfadjoint inputs.
Use: prove that every real native search/correction segment operator is
symmetric from the original scalar objective, without adding symmetry to its
primitive derivative assumptions. Source: Schwarz's theorem and integration.
-/
namespace krylov.Functions
noncomputable section
open Set Metric MeasureTheory krylov.Methods krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A true segment average of symmetric Hessians is symmetric.
Article: main_krylov, lem:cycle-transfer, actual operator symmetry. -/
theorem averagedDerivative_symmetric (H : E → E →L[ℝ] E) (a s : E)
    (hc : ContinuousOn (fun t : ℝ=>H (a+t • s)) (Icc 0 1))
    (hs : ∀ t∈Icc (0:ℝ) 1, (H (a+t • s)).toLinearMap.IsSymmetric) :
    (averagedDerivative H a s).toLinearMap.IsSymmetric := by
  have hi := hc.intervalIntegrable_of_Icc (μ:=volume) (by norm_num : (0:ℝ)≤1)
  intro u v
  let L : (E →L[ℝ] E) →L[ℝ] ℝ := (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E u)
  let R : (E →L[ℝ] E) →L[ℝ] ℝ := (innerSL ℝ u).comp (ContinuousLinearMap.apply ℝ E v)
  change inner ℝ (averagedDerivative H a s u) v=inner ℝ u (averagedDerivative H a s v)
  calc
    _ = L (averagedDerivative H a s) := real_inner_comm _ _
    _ = ∫ t in (0:ℝ)..1, L (H (a+t • s)) := (L.intervalIntegral_comp_comm hi).symm
    _ = ∫ t in (0:ℝ)..1, R (H (a+t • s)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
      change inner ℝ v (H (a+t • s) u)=inner ℝ u (H (a+t • s) v)
      exact (real_inner_comm _ _).trans (hs t ht' u v)
    _ = R (averagedDerivative H a s) := R.intervalIntegral_comp_comm hi
    _ = _ := rfl

/-- Every real native ordinary RFC query operator is selfadjoint throughout
its derived shrinking neighborhood. Article: main_krylov, thm:Htransfer.
The sole scale condition encloses the already derived genuine queries; no
operator symmetry assumption is imposed. -/
theorem NativeRFCPrefixBounds.operator_symmetric
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (r : ℝ) (u : E) (ε M D C : ℝ) (N : ℕ)
    (hp : NativeRFCPrefixBounds T f G H Q r u ε M D C N)
    (hscale : ‖T.toContinuousLinearMap‖*(M*ε)<r)
    {L : ℝ≥0} (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖≤r → HasFDerivAt G (H z) z) :
    ∀ k<N,
      (rfcFunctionSearchOperator T f G H fullMemory r (ε • u) k).toLinearMap.IsSymmetric ∧
      (rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u) k).toLinearMap.IsSymmetric := by
  intro k hk
  let A := rfcFunctionRun T f G fullMemory r (ε • u) k
  let X := rfcFunctionPoint T f G fullMemory r (ε • u) k
  let Y := rfcFunctionLinePoint T f fullMemory r (ε • u) A
  let U := rfcFunctionCorrectionStep T f G fullMemory r (ε • u) A
  let Z := rfcFunctionPoint T f G fullMemory r (ε • u) (k+1)
  have hx : ‖X‖≤M*ε := (hp.1 k hk.le).1
  have hy : ‖Y‖≤M*ε := (hp.2 k hk).2.2.1
  have hz : ‖Z‖≤M*ε := (hp.1 (k+1) (by omega)).1
  have hZU : Z=Y+U := rfcFunctionPoint_succ_line T f G fullMemory r (ε • u) k
  have hbase (a b : E) (ha : ‖a‖≤M*ε) (hb : ‖b‖≤M*ε) :
      (averagedDerivative H a (b-a)).toLinearMap.IsSymmetric := by
    have hnorm t (ht : t∈Icc (0:ℝ) 1) : ‖T (a+t • (b-a))‖<r :=
      ((T.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (segment_norm_le_endpoints a b _ ha hb t ht) (norm_nonneg _))).trans_lt hscale
    have hseg t (ht : t∈Icc (0:ℝ) 1) : a+t • (b-a)∈T ⁻¹' closedBall (0:E) r := by
      simpa only [mem_preimage,mem_closedBall,dist_zero_right] using (hnorm t ht).le
    have hc := (coordinateDerivative_lipschitz_pullback T H hH).continuousOn.comp
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hseg
    exact averagedDerivative_symmetric H a (b-a) hc
      (fun t ht=>genuine_hessian_symmetric T f G H hF hG _ (hnorm t ht))
  refine ⟨hbase X Y hx hy,?_⟩
  have hb := hbase Y Z hy hz
  rw [hZU,add_sub_cancel_left] at hb
  exact hb

end
end krylov.Functions
