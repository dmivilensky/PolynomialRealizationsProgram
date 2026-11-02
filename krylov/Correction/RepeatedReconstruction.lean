import krylov.Correction.RepeatedExpansion
import krylov.Correction.FullReconstruction

/-!
Article: main_krylov, thm:C2(b), the actual full physical repeated residual.
Use: reconstruct the signed ordered native product as a genuine returned
physical gradient, with the stated higher-order error rather than a projection.
Source: full reference CG independence and analytic inverse reconstruction;
the terminal product is derived from the actual observed query execution.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Actual repeated terminal queries have the full physical leading product with remainder O(ω^(k_c+2)).
Use: no moving projection or unproved reconstruction domain remains in the actual returned-gradient expansion.
Article: main_krylov, thm:C2(b), physical repeated fixed-model refinement.
Proof: the actual CG reference gives an independent full family for every
correction count. Each leading model factor has first order and the fresh
incoming vector has first order, hence their product has order k_c+1.
The general inverse-transpose reconstruction therefore preserves the proved
projected remainder at order k_c+2.
-/
theorem full_repeated_physical_order {k : ℕ} (count : ℕ) (hc : 0<count)
    (A B : X → ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g : X → EuclideanSpace ℝ (Fin (k+1)))
    (C : ℕ → X → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (hC : ∀ j<count, AnalyticAt ℝ (C j) 0)
    (hAsym : ∀ z i, (A z i).toLinearMap.IsSymmetric)
    (Q : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hC0 : ∀ j<count, C j 0=Q)
    (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : EuclideanSpace ℝ (Fin (k+1)), v≠0 → 0 < inner ℝ v (Q v))
    (hk : 0<k) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    let m := rfcMethod fullMemory count
    let U := fun z => probedStepBasis m (A z) (B z) (g z) k
    let H := fun z => pairModel (U z) (probedImageBasis m (A z) (B z) (g z) k)
    let L := fun j z => Matrix.of fun a b =>
      inner ℝ (U 0 a) ((C j z-A z (k-(min a b).val)) (U 0 b))
    let R₀ := fullBasisMatrix (U 0)
    (fun z => (repeatedTerminalResult count (A z) (B z) (g z) k (fun j => C j z)).gradient-
      Matrix.toEuclideanCLM (𝕜 := ℝ) R₀ᵀ⁻¹
        (correctionRun (fun j z => Matrix.toEuclideanCLM (𝕜 := ℝ) (L j z*(H 0)⁻¹))
          (fun z => frozenIncoming Q (g 0) (A z) k) count z)) =O[𝓝 (0 : X)]
            (fun z => ‖z‖^(count+2)) := by
  -- The actual full reference family supplies the inverse reconstruction domain.
  let m := rfcMethod fullMemory count (E := EuclideanSpace ℝ (Fin (k+1)))
  let U := fun z => probedStepBasis m (A z) (B z) (g z) k
  let H := fun z => pairModel (U z) (probedImageBasis m (A z) (B z) (g z) k)
  let L := fun j z => Matrix.of fun a b =>
    inner ℝ (U 0 a) ((C j z-A z (k-(min a b).val)) (U 0 b))
  let R := fun z => fullBasisMatrix (U z)
  let M := fun j z => Matrix.toEuclideanCLM (𝕜 := ℝ) (L j z*(H 0)⁻¹)
  let r := fun z => frozenIncoming Q (g 0) (A z) k
  let v := fun z => correctionRun M r count z
  have hd := full_cycle_data_regular count A B g hA hB hg Q hA0 hB0 hQ hpos k hpre
  have hR (i j : Fin (k+1)) : AnalyticAt ℝ (fun z => R z i j) 0 :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k+1) => ℝ) i).analyticAt _).comp (hd.2.1 j)
  have hU : LinearIndependent ℝ (U 0) := by
    dsimp only [U]
    rw [hA0,hB0]
    exact probedStepBasis_independent m (rfcMethod_consistent fullMemory (fun _ ha => ha) count)
      Q hQ hpos (g 0) k hpre
  have hu : IsUnit (R 0).det := fullBasisMatrix_unit _ hU
  -- Every further correction gains one order from its derived linear factor.
  have hM (j : ℕ) (hj : j<count) : M j =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
    have ha : AnalyticAt ℝ (L j) 0 := analytic_spectral_matrix _ 0 fun a b =>
      analytic_inner analyticAt_const
        (analytic_operator_apply ((hC j hj).sub (hA (k-(min a b).val))) analyticAt_const)
    have hz : L j 0=0 := by
      ext a b
      simp only [L,hC0 j hj,hA0,sub_self,_root_.zero_apply,inner_zero_right,Matrix.of_apply,Matrix.zero_apply]
    have hL : L j =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
      simpa only [hz,sub_zero] using analytic_reference_order _ ha
    exact krylov.Secant.matrix_bigO_toEuclideanCLM _ _ (matrix_mul_const_bigO _ _ _ hL)
  have hv : v =O[𝓝 (0 : X)] (fun z => ‖z‖^(count+1)) := by
    simpa only [pow_one,Nat.add_comm] using correctionRun_order M r (fun z => ‖z‖) 1 count hM
      (by simpa only [pow_one] using frozenIncoming_order A hA Q hA0 (g 0) k)
  have hp := full_repeated_projected_order count hc A B g C hA hB hg hC hAsym
    Q hA0 hB0 hC0 hQ hpos k hk hpre
  have hp' : (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (R z)ᵀ
      (repeatedTerminalResult count (A z) (B z) (g z) k (fun j => C j z)).gradient+-v z)
        =O[𝓝 (0 : X)] (fun z => ‖z‖^((count+1)+1)) := by
    change (fun z => projectedResidual (U z)
      (repeatedTerminalResult count (A z) (B z) (g z) k (fun j => C j z)).gradient-v z)
        =O[𝓝 (0 : X)] (fun z => ‖z‖^(count+2)) at hp
    simpa only [projectedResidual_fullBasisMatrix,sub_eq_add_neg,Nat.add_assoc,Nat.reduceAdd] using hp
  have hf := full_projection_reconstruction_order_at R _ (fun z => -v z) (count+1) hR hu hv.neg_left hp'
  change (fun z => (repeatedTerminalResult count (A z) (B z) (g z) k (fun j => C j z)).gradient-
    Matrix.toEuclideanCLM (𝕜 := ℝ) (R 0)ᵀ⁻¹ (v z)) =O[𝓝 (0 : X)] (fun z => ‖z‖^(count+2))
  simpa only [map_neg,sub_eq_add_neg,Nat.add_assoc,Nat.reduceAdd] using hf

end
end krylov.Correction
