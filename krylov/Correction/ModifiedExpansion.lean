import krylov.Correction.TerminalModel

/-!
Article: main_krylov, apD:lem-model, actual modified terminal expansion.
Use: derive the cubic remainder for a real model replacement, with every
prefix, incoming-residual and inverse premise discharged from actual RFC.
Source: the genuine native expansion ingredients and the arbitrary-reference
matrix correction theorem; no desired output expansion is a hypothesis.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Replacing the genuine last RFC model subtracts precisely that change from its native second-order factor.
Use: the real modified coefficient solve has a derived cubic projected remainder.
Article: main_krylov, apD:lem-model, modified model error 𝓛−Δ̂.
Proof: the actual model-error and incoming-vector expansions are already
proved for the unchanged real prefix. Adding the analytic vanishing model
change preserves the reference inverse, and subtracts it from both true and
frozen errors. Apply the reference solve theorem and the exact modified query identity. -/
theorem full_modified_projected_second_order {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (hAsym : ∀ z i, (A z i).toLinearMap.IsSymmetric)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hk : 0<k) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0)
    (D : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hD : AnalyticAt ℝ D 0) (hD0 : D 0=0) :
    let m := rfcMethod fullMemory 1 (E := E)
    let U := fun z => probedStepBasis m (A z) (B z) (g z) k
    let H := fun z => pairModel (U z) (probedImageBasis m (A z) (B z) (g z) k)
    let L := fun z => Matrix.of fun i j =>
      inner ℝ (U 0 i) ((B z k-A z (k-(min i j).val)) (U 0 j))
    (fun z => projectedResidual (U z) (modifiedTerminalGradient (A z) (B z) (g z) k (D z))+
      Matrix.toEuclideanCLM (𝕜 := ℝ) ((L z-D z)*(H 0)⁻¹)
        (frozenIncoming Q (g 0) (A z) k)) =O[𝓝 (0 : X)] (fun z => ‖z‖^3) := by
  -- Both leading factors come from actual prefix data, before changing only the final model.
  let m := rfcMethod fullMemory 1 (E := E)
  let U := fun z => probedStepBasis m (A z) (B z) (g z) k
  let H := fun z => pairModel (U z) (probedImageBasis m (A z) (B z) (g z) k)
  let L := fun z => Matrix.of fun i j => inner ℝ (U 0 i)
    ((B z k-A z (k-(min i j).val)) (U 0 j))
  let N := fun z => correctionCompression (U z) (B z k)-(H z+D z)
  let gp := fun z => projectedResidual (U z) (fullPostSearch 1 (A z) (B z) (g z) k)
  let r := fun z => frozenIncoming Q (g 0) (A z) k
  have hH := (full_cycle_data_regular 1 A B g hA hB hg Q hA0 hB0 hQ hpos k hpre).2.2.2
  have hu := (full_model_unit_eventually 1 A B g hA hB hg Q hA0 hB0 hQ hpos k hpre).1
  have hN : (fun z => N z-(L z-D z)) =O[𝓝 (0 : X)] (fun z => ‖z‖^2) := by
    apply (full_model_error_order 1 A B g hA hB hg hAsym Q hA0 hB0 hQ hpos k hpre).congr_left
    intro z
    dsimp only [N,L,H,U]
    abel
  have hLa : AnalyticAt ℝ L 0 := analytic_spectral_matrix L 0 fun i j =>
    analytic_inner analyticAt_const
      (analytic_operator_apply ((hB k).sub (hA (k-(min i j).val))) analyticAt_const)
  have hL0 : L 0=0 := by
    ext i j
    simp only [L,hA0,hB0,sub_self,_root_.zero_apply,inner_zero_right,Matrix.of_apply,Matrix.zero_apply]
  have hLD : (fun z => L z-D z) =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
    simpa only [hL0,hD0,sub_self,sub_zero] using
      analytic_reference_order (fun z => L z-D z) (hLa.sub hD)
  have hmod0 : H 0+D 0=H 0 := by rw [hD0,add_zero]
  have hs := reference_matrix_correction_order (fun z => H z+D z) N (fun z => L z-D z) gp r
    (hH.add hD) (by simpa only [hmod0] using hu) hN hLD
    (full_incoming_vector_order A B g hA hB hg hAsym Q hA0 hB0 hQ hpos k hk hpre)
    (frozenIncoming_order A hA Q hA0 (g 0) k)
  simp only [hmod0] at hs
  apply hs.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [modified_model_unit_eventually A B g hA hB hg Q hA0 hB0 hQ hpos k hpre D hD hD0]
    with z hz
  rw [modifiedTerminalGradient_projected _ _ _ _ hz]

/-- The genuine full modified terminal gradient has the physical second-order factor L−Δ_H with cubic remainder.
Use: a concrete last-model variant can use the source's correction formula
after its common true RFC prefix, with no extra full-basis assumptions.
Article: main_krylov, apD:lem-model, full physical modified-model expansion.
Proof: true CG consistency proves independence of the actual full reference
window. The changed leading factor is quadratic, so the proved full-basis
reconstruction freezes its inverse transpose at cubic cost. -/
theorem full_modified_physical_second_order {k : ℕ}
    (A B : X → ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g : X → EuclideanSpace ℝ (Fin (k+1)))
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (hAsym : ∀ z i, (A z i).toLinearMap.IsSymmetric)
    (Q : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : EuclideanSpace ℝ (Fin (k+1)), v≠0 → 0 < inner ℝ v (Q v))
    (hk : 0<k) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0)
    (D : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hD : AnalyticAt ℝ D 0) (hD0 : D 0=0) :
    let m := rfcMethod fullMemory 1
    let U := fun z => probedStepBasis m (A z) (B z) (g z) k
    let H := fun z => pairModel (U z) (probedImageBasis m (A z) (B z) (g z) k)
    let L := fun z => Matrix.of fun i j =>
      inner ℝ (U 0 i) ((B z k-A z (k-(min i j).val)) (U 0 j))
    let R₀ := fullBasisMatrix (U 0)
    (fun z => modifiedTerminalGradient (A z) (B z) (g z) k (D z)+
      Matrix.toEuclideanCLM (𝕜 := ℝ) (R₀ᵀ⁻¹*((L z-D z)*(H 0)⁻¹))
        (frozenIncoming Q (g 0) (A z) k)) =O[𝓝 (0 : X)] (fun z => ‖z‖^3) := by
  -- Reconstruction uses the actual unchanged prefix basis, whose full reference rank is derived.
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (k+1)))
  let U := fun z => probedStepBasis m (A z) (B z) (g z) k
  let H := fun z => pairModel (U z) (probedImageBasis m (A z) (B z) (g z) k)
  let L := fun z => Matrix.of fun i j => inner ℝ (U 0 i)
    ((B z k-A z (k-(min i j).val)) (U 0 j))
  let R := fun z => fullBasisMatrix (U z)
  let c := fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) ((L z-D z)*(H 0)⁻¹)
    (frozenIncoming Q (g 0) (A z) k)
  have hd := full_cycle_data_regular 1 A B g hA hB hg Q hA0 hB0 hQ hpos k hpre
  have hR (i j : Fin (k+1)) : AnalyticAt ℝ (fun z => R z i j) 0 :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k+1) => ℝ) i).analyticAt _).comp (hd.2.1 j)
  have hU : LinearIndependent ℝ (U 0) := by
    dsimp only [U]
    rw [hA0,hB0]
    exact probedStepBasis_independent m (rfcMethod_consistent fullMemory (fun _ ha => ha) 1)
      Q hQ hpos (g 0) k hpre
  have hLa : AnalyticAt ℝ L 0 := analytic_spectral_matrix L 0 fun i j =>
    analytic_inner analyticAt_const
      (analytic_operator_apply ((hB k).sub (hA (k-(min i j).val))) analyticAt_const)
  have hL0 : L 0=0 := by
    ext i j
    simp only [L,hA0,hB0,sub_self,_root_.zero_apply,inner_zero_right,Matrix.of_apply,Matrix.zero_apply]
  have hLD : (fun z => L z-D z) =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
    simpa only [hL0,hD0,sub_self,sub_zero] using
      analytic_reference_order (fun z => L z-D z) (hLa.sub hD)
  have hc : c =O[𝓝 (0 : X)] (fun z => ‖z‖^2) := by
    have hM := krylov.Secant.matrix_bigO_toEuclideanCLM _ _
      (matrix_mul_const_bigO (fun z => L z-D z) (H 0)⁻¹ _ hLD)
    simpa only [← pow_two] using operator_action_order _ _ _ _ hM
      (frozenIncoming_order A hA Q hA0 (g 0) k)
  have hproj := full_modified_projected_second_order A B g hA hB hg hAsym Q hA0 hB0 hQ hpos k hk hpre D hD hD0
  simp only [projectedResidual_fullBasisMatrix] at hproj
  have hf := full_projection_reconstruction_order R _ c hR (fullBasisMatrix_unit _ hU) hc hproj
  simpa only [R,c,map_mul,mul_apply_eq_comp] using hf

end
end krylov.Correction
