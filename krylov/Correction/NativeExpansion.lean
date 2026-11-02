import krylov.Correction.ActualSolve
import krylov.Correction.ReferenceSolve

/-!
Article: main_krylov, thm:C, the genuine executed second-order RFC coefficient expansion.
Use: combine the derived incoming and model-error coefficients with the actual
accepted inverse solve, obtaining a cubic remainder in native physical data coordinates.
Source: actual RFC execution, proved fresh-residual and measured-model error
expansions, and the existing matrix correction calculus at a genuine reference model.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The frozen incoming coefficient is genuinely analytic in the actual probe operators.
Use: its first-order size will be derived at the common quadratic base.
Article: main_krylov, thm:C, regularity of the leading fresh coefficient.
Proof: each actual operator-difference action is analytic; pair with the fixed
genuine reference steps and assemble the finite Euclidean coefficient vector. -/
theorem frozenIncoming_analytic (A : X → ℕ → E →L[ℝ] E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0) (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    AnalyticAt ℝ (fun z => frozenIncoming Q g (A z) k) 0 := by
  -- Assemble real analytic scalar coordinates through the genuine Euclidean coordinate equivalence.
  have ha : AnalyticAt ℝ (fun z => WithLp.ofLp (frozenIncoming Q g (A z) k)) 0 := by
    apply AnalyticAt.pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact analyticAt_const
    · change AnalyticAt ℝ (fun z => inner ℝ (referenceStep Q g (k-1-j.val))
        ((A z k-A z (k-1-j.val)) (referenceStep Q g k))) 0
      exact analytic_inner analyticAt_const
        (analytic_operator_apply ((hA k).sub (hA (k-1-j.val))) analyticAt_const)
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (k+1) => ℝ)).symm.toContinuousLinearMap.analyticAt _).comp ha

/-- The actual frozen incoming coefficient has first order at the genuine common quadratic base.
Use: discharge the leading-residual size premise of the final matrix expansion.
Article: main_krylov, thm:C, r₁=O(ω).
Proof: the analytic coefficient vanishes exactly when every real probe operator
is the common quadratic operator; differentiability supplies its first-order size. -/
theorem frozenIncoming_order (A : X → ℕ → E →L[ℝ] E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0) (Q : E →L[ℝ] E)
    (hA0 : A 0=fun _ => Q) (g : E) (k : ℕ) :
    (fun z => frozenIncoming Q g (A z) k) =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
  have hz : frozenIncoming Q g (A 0) k=0 := by
    ext j
    change (Fin.cons (0 : ℝ) (fun i : Fin k => inner ℝ (referenceStep Q g (k-1-i.val))
      ((A 0 k-A 0 (k-1-i.val)) (referenceStep Q g k))) : Fin (k+1) → ℝ) j=0
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · simp only [hA0,sub_self,_root_.zero_apply,inner_zero_right,Fin.cons_succ]
  simpa only [hz,sub_zero] using analytic_reference_order _ (frozenIncoming_analytic A hA Q g k)

/-- The actual returned full-memory RFC projected gradient has its complete native second-order expansion and cubic remainder.
Use: the coefficient contains the true measured model and reference CG steps;
all analytic domains, incoming orders, pair discrepancies and actual gate execution are derived.
Article: main_krylov, thm:C, native-coordinate second-order residual.
Proof: the real incoming vector equals its frozen fresh coefficient up to
quadratic order, and the real model error equals its frozen operator coefficient
up to quadratic order. Both coefficients vanish at the genuine quadratic base.
Apply the reference-model correction theorem, then identify its left side with
the actual returned gradient through the proved executed correction identity. -/
theorem full_projected_second_order
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (hAsym : ∀ z i, (A z i).toLinearMap.IsSymmetric)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hk : 0<k) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    let m := rfcMethod fullMemory 1 (E := E)
    let U := fun z => probedStepBasis m (A z) (B z) (g z) k
    let H := fun z => pairModel (U z) (probedImageBasis m (A z) (B z) (g z) k)
    let L := fun z => Matrix.of fun i j =>
      inner ℝ (U 0 i) ((B z k-A z (k-(min i j).val)) (U 0 j))
    (fun z => projectedResidual (U z) (probedGradient m (A z) (B z) (g z) (k+1))+
      Matrix.toEuclideanCLM (𝕜 := ℝ) (L z*(H 0)⁻¹) (frozenIncoming Q (g 0) (A z) k)) =O[𝓝 (0 : X)]
        (fun z => ‖z‖^3) := by
  -- Assemble the genuinely derived two leading factors before using the actual returned-output identity.
  let m := rfcMethod fullMemory 1 (E := E)
  let U := fun z => probedStepBasis m (A z) (B z) (g z) k
  let H := fun z => pairModel (U z) (probedImageBasis m (A z) (B z) (g z) k)
  let N := fun z => correctionCompression (U z) (B z k)-H z
  let L := fun z => Matrix.of fun i j => inner ℝ (U 0 i)
    ((B z k-A z (k-(min i j).val)) (U 0 j))
  let rho := fun z => projectedResidual (U z) (fullPostSearch 1 (A z) (B z) (g z) k)
  let r := fun z => frozenIncoming Q (g 0) (A z) k
  have hd := full_cycle_data_regular 1 A B g hA hB hg Q hA0 hB0 hQ hpos k hpre
  have hLanalytic : AnalyticAt ℝ L 0 := analytic_spectral_matrix L 0 fun i j =>
    analytic_inner analyticAt_const
      (analytic_operator_apply ((hB k).sub (hA (k-(min i j).val))) analyticAt_const)
  have hL₀ : L 0=0 := by
    ext i j
    simp only [L,hA0,hB0,sub_self,_root_.zero_apply,inner_zero_right,Matrix.of_apply,Matrix.zero_apply]
  have hL : L =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
    simpa only [hL₀,sub_zero] using analytic_reference_order L hLanalytic
  have he := reference_matrix_correction_order H N L rho r hd.2.2.2
    (full_model_unit_eventually 1 A B g hA hB hg Q hA0 hB0 hQ hpos k hpre).1
    (full_model_error_order 1 A B g hA hB hg hAsym Q hA0 hB0 hQ hpos k hpre) hL
    (full_incoming_vector_order A B g hA hB hg hAsym Q hA0 hB0 hQ hpos k hk hpre)
    (frozenIncoming_order A hA Q hA0 (g 0) k)
  apply he.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [full_projected_correction_eventually A B g hA hB hg Q hA0 hB0 hQ hpos k hk hpre]
    with z hz
  rw [hz]

end
end krylov.Correction
