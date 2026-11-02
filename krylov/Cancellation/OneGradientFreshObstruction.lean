import krylov.LinearAlgebra.FreshDefectGeometry
import krylov.Methods.OneGradientCoordinates
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(a), genuine one-gradient fresh obstruction.
Use: construct opposite real oracle scenarios and prove that their actual
executed histories and actual chosen step agree before the fresh query.
Source: the original nonanticipating one-gradient executor and the proved
sharp symmetric reflection witness; no method smoothness is assumed.
-/

namespace krylov.Cancellation
noncomputable section
open krylov.Methods krylov.LinearAlgebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Change only the operator used by the actual indicated new query.
Use: the incoming observed transcript contains no observation of this change.
Article: main_krylov, apH:dcs2(a), the two fresh scenarios. -/
def freshOperatorPath (A : ℕ → E →L[ℝ] E) (k : ℕ) (F : E →L[ℝ] E) : ℕ → E →L[ℝ] E :=
  fun i => if i=k then A i+F else A i

/-- Equal actual oracle prefixes give exactly equal full one-gradient histories.
Use: derive indistinguishability from the real executor for arbitrary policies.
Article: main_krylov, apH:dcs2(a), common data before the new query.
Proof: induction on actual queries; both executions choose the same next step
from the same complete observed history and receive the same operator image. -/
theorem oneGradientRun_congr_prefix (m : OneGradientMethod E)
    (A B : ℕ → E →L[ℝ] E) (g : E) (N : ℕ) (hAB : ∀ i<N,A i=B i) :
    ∀ j≤N,oneGradientRun m A g j=oneGradientRun m B g j := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [oneGradientRun,oneGradientRun,ih (by omega),hAB j (by omega)]

/-- The real fresh perturbation leaves every incoming observed history unchanged.
Use: all actual prior window vectors, policy coefficients and the next chosen
step are identical in the two fresh scenarios.
Article: main_krylov, apH:dcs2(a), exact prefix indistinguishability.
Proof: every earlier actual query has the original operator. -/
theorem one_gradient_fresh_prefix (m : OneGradientMethod E)
    (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (F : E →L[ℝ] E) :
    ∀ j≤k,oneGradientRun m (freshOperatorPath A k F) g j=oneGradientRun m A g j :=
  oneGradientRun_congr_prefix m _ A g k (fun i hi => by
    change (if i=k then A i+F else A i)=A i
    split_ifs with h
    · omega
    · rfl)

/-- The actual new gradient changes by precisely the fresh operator acting on
the actual common step, for every data-only one-gradient policy.
Use: the opposite gradients are actual executed observations, not a prescribed
response or a linearized model.
Article: main_krylov, apH:dcs2(a), g plus/minus equals common gradient plus/minus Fs.
Proof: the genuine incoming histories agree, hence so do their chosen steps;
expand the one real new oracle update. -/
theorem one_gradient_fresh_gradient (m : OneGradientMethod E)
    (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (F : E →L[ℝ] E) :
    oneGradientGradient m (freshOperatorPath A k F) g (k+1)=
      oneGradientGradient m A g (k+1)+F (oneGradientStep m A g k) := by
  have hh := one_gradient_fresh_prefix m A g k F k le_rfl
  rw [oneGradientGradient_succ,oneGradientGradient_succ]
  change (oneGradientRun m (freshOperatorPath A k F) g k).gradient+
    freshOperatorPath A k F k (m.step (oneGradientRun m (freshOperatorPath A k F) g k))=_
  rw [hh]
  simp only [freshOperatorPath,ite_true,_root_.add_apply,oneGradientGradient,oneGradientStep]
  abel

/-- Every genuine one-gradient method has an actual pair of indistinguishable
fresh symmetric scenarios attaining the whole projected fresh lower radius.
Use: applies to every nonempty actual old window and every finite variation,
without CG consistency, a smooth method or an assumed output expansion.
Article: main_krylov, apH:dcs2(a), irreducibility of the fresh defect.
Proof: the proved symmetric reflection witness gives the full projected image
of the actual common step. Both genuine executed gradients have that opposite
fresh image about the same incoming value, so the two-scenario lower bound applies. -/
theorem one_gradient_fresh_obstruction [CompleteSpace E]
    (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (hK : K≠⊥)
    (omega : ℝ) (homega : 0≤omega) :
    ∃ F : E →L[ℝ] E,IsSelfAdjoint F ∧ ‖F‖≤omega ∧
      (∀ j≤k,oneGradientRun m (freshOperatorPath A k F) g j=
        oneGradientRun m (freshOperatorPath A k (-F)) g j) ∧
      ‖K.starProjection (F (oneGradientStep m A g k))‖=omega*‖oneGradientStep m A g k‖ ∧
      omega*‖oneGradientStep m A g k‖≤
        max ‖K.starProjection (oneGradientGradient m (freshOperatorPath A k F) g (k+1))‖
          ‖K.starProjection (oneGradientGradient m (freshOperatorPath A k (-F)) g (k+1))‖ := by
  obtain ⟨F,hFs,hF,himage,hlower⟩ := projected_fresh_two_scenarios K hK
    (oneGradientStep m A g k) (oneGradientGradient m A g (k+1)) omega homega
  refine ⟨F,hFs,hF,fun j hj => (one_gradient_fresh_prefix m A g k F j hj).trans
    (one_gradient_fresh_prefix m A g k (-F) j hj).symm,himage,?_⟩
  rw [one_gradient_fresh_gradient,one_gradient_fresh_gradient]
  simpa only [_root_.neg_apply,sub_eq_add_neg] using hlower

end
end krylov.Cancellation
