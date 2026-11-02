import krylov.Cancellation.DCOneGradientFreshProjection
import krylov.Cancellation.WindowResidualEquality
import krylov.Cancellation.PhysicalFreshDefect
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(a), exact physical fresh-defect attainment.
Use: close the full finite-variation source assertion with the original
native DC-slide execution, original symmetric matrix budget and exact
inverse-energy-Gram residual norm.
Source: proved genuine native fresh coordinates, true metric transfer,
physical Householder attainer and the matching sharp projection upper bound.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- With quadratic past and only the newest physical increment, the actual
DC-slide one-gradient window residual equals exactly the true fresh defect
in the article's original inverse-energy-Gram norm.
Use: a finite-variation identity on the genuine retained window, not just
equality of first derivatives or a formal response model.
Article: main_krylov, apH:dcs2(a), original metric attainment identity.
Proof: true quadratic positivity and window independence derive the actual
tilted-solve inverse domain. Native one-gradient execution gives the exact
fresh physical pairing coordinates; their proved true metric dictionary
gives equality of the original window norms. -/
theorem dc_one_gradient_newest_metric
    (memory : ℕ → ℕ) (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hs : LinearIndependent ℝ (windowSteps (selectedWindow memory
      (oneGradientRun (dcSlideOneGradient memory estimate) (fun _ => cgOperator base) g k))))
    (ha : estimate (oneGradientRun (dcSlideOneGradient memory estimate) (fun _ => cgOperator base) g k)≠0)
    (F : Matrix (Fin n) (Fin n) ℝ) :
    let m := dcSlideOneGradient memory estimate
    let W := selectedWindow memory (oneGradientRun m (fun _ => cgOperator base) g k)
    windowMetricResidual base (windowSteps W)
      (oneGradientGradient m (freshOperatorPath (fun _ => cgOperator base) k (cgOperator F)) g (k+1))=
        windowMetricResidual base (windowSteps W) (cgOperator F (oneGradientStep m (fun _ => cgOperator base) g k)) := by
  exact window_metric_residual_congr base hb _ hs _ _
    (dc_one_gradient_newest_coordinates memory estimate _ (cgOperator_positive base hb).1
      (cgOperator_positive base hb).2 g k hs ha (cgOperator F))

/-- One-gradient DC-slide attains exactly the universal irreducible fresh
window radius on the original real symmetric physical matrix budget ball.
Use: the upper bound and a real attaining matrix hold at finite variation,
on the actual independent nonempty retained window, including a zero new
step or zero budget. Combined with the arbitrary-policy opposite-scenario
theorem this closes the full printed fresh-defect assertion.
Article: main_krylov, apH:dcs2(a), exact attained native fresh minimax radius.
Proof: native exact fresh-coordinate cancellation transfers to the genuine
inverse-energy-Gram norm. Every physical symmetric increment obeys the
sharp relative-operator projection bound. The real physical Householder
matrix maps the actual canonical step to the full budget radius in the
actual window and gives equality for the original executed gradient. -/
theorem dc_one_gradient_fresh_sharp
    (memory : ℕ → ℕ) (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hp : 0<(selectedWindow memory (oneGradientRun (dcSlideOneGradient memory estimate)
      (fun _ => cgOperator base) g k)).length)
    (hs : LinearIndependent ℝ (windowSteps (selectedWindow memory
      (oneGradientRun (dcSlideOneGradient memory estimate) (fun _ => cgOperator base) g k))))
    (ha : estimate (oneGradientRun (dcSlideOneGradient memory estimate) (fun _ => cgOperator base) g k)≠0)
    (omega : ℝ) (homega : 0≤omega) :
    let m := dcSlideOneGradient memory estimate
    let W := selectedWindow memory (oneGradientRun m (fun _ => cgOperator base) g k)
    let step := oneGradientStep m (fun _ => cgOperator base) g k
    IsGreatest {z : ℝ | ∃ F : Matrix (Fin n) (Fin n) ℝ,F.IsSymm ∧ ‖relativeOperator base F‖≤omega ∧
      z=windowMetricResidual base (windowSteps W)
        (oneGradientGradient m (freshOperatorPath (fun _ => cgOperator base) k (cgOperator F)) g (k+1))}
      (omega*‖cgOperator (metricRoot base) step‖) := by
  let m := dcSlideOneGradient memory estimate
  let W := selectedWindow memory (oneGradientRun m (fun _ => cgOperator base) g k)
  let step := oneGradientStep m (fun _ => cgOperator base) g k
  obtain ⟨F,hFs,hF,hvalue,_⟩ := physical_fresh_projection_witness base hb (windowSteps W) hs hp
    step 0 omega homega
  constructor
  · refine ⟨F,hFs,hF,?_⟩
    rw [dc_one_gradient_newest_metric memory estimate base hb g k hs ha F]
    exact hvalue.symm
  · rintro z ⟨F,_,hF,rfl⟩
    rw [dc_one_gradient_newest_metric memory estimate base hb g k hs ha F]
    exact window_metric_fresh_le base hb (windowSteps W) step F omega hF

end
end krylov.Cancellation
