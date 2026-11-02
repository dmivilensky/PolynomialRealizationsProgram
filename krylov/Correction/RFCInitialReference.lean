import krylov.Methods.RFCReference
import krylov.Stability.UniformLineSearch

/-!
Article: main_krylov, thm:UCq, exact small-dimensional reference prefix.
Use: Derive the genuine first RFC history and second CG direction from the
original unchanged base probe, then retain relative small-line search control.
Source: the actual empty-window RFC executor, proved quadratic consistency
and the existing true unit-curvature and reciprocal perturbation inequalities.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If the genuine first probe is the reference operator, the actual first complete ordinary-RFC history equals its real static reference history.
Use: Start the three-dimensional exception with exact observed data, independently of the first correction operator.
Article: main_krylov, thm:UCq.
Proof: The actual first retained window is empty, so the genuine RFC correction tree is done. The real first records therefore depend only on their common initial search probe.
-/
theorem ordinary_initial_history (A B : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (g : E) (hA : A 0=Q) :
    methodRun (rfcMethod fullMemory 1) A B g 1=
      methodRun (rfcMethod fullMemory 1) (fun _ => Q) (fun _ => Q) g 1 := by
  simp [methodRun,methodAdvance,hA,rfcMethod,retainedMethod,rfcCorrection,selectedWindow,History.pairs,
    fullMemory,runCorrections]

/-- The genuine first ordinary-RFC recorded step and observed secant are exactly their true quadratic CG reference pair whenever its first probe is unchanged.
Use: Derive actual exact old data in the low-dimensional uniform exception.
Article: main_krylov, thm:UCq.
Proof: Exact first-history equality preserves the real observed step/secant pair. Apply the existing true quadratic RFC pair dictionary.
-/
theorem ordinary_initial_pair (A B : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (hA : A 0=Q) :
    probedStep (rfcMethod fullMemory 1) A B g 0=referenceStep Q g 0 ∧
      probedSecant (rfcMethod fullMemory 1) A B g 0=Q (referenceStep Q g 0) := by
  have hh := ordinary_initial_history A B Q g hA
  have hp := congrArg History.pairs hh
  rw [methodRun_pairs_executed,methodRun_pairs_executed] at hp
  have he := Prod.mk.inj (List.cons.inj hp).1
  have hr := rfc_reference_pair fullMemory 1 Q hQ hpos g (fun _ _ hj => hj) 0
  exact ⟨he.1.trans hr.1,he.2.trans hr.2⟩

/-- The actual second ordinary-RFC search direction is exactly the true second CG direction when the original first probe equals the base.
Use: Avoid an unweighted direction perturbation estimate at a tiny intermediate CG step.
Article: main_krylov, thm:UCq.
Proof: The true complete first history is exactly static quadratic data. Reuse genuine quadratic RFC direction consistency on that same observed history.
-/
theorem ordinary_second_direction (A B : ℕ → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (hA : A 0=Q) :
    (rfcMethod fullMemory 1).direction (methodRun (rfcMethod fullMemory 1) A B g 1)=
      CG.direction Q g 1 := by
  rw [ordinary_initial_history A B Q g hA]
  exact rfc_reference_direction fullMemory 1 Q hQ hpos g (fun _ _ hj => hj) 1

/-- A genuine fixed-unit-direction search is exactly its true identity-reference displacement times the actual reciprocal curvature.
Use: Retain the reference step length in low-dimensional perturbation estimates.
Article: main_krylov, thm:UCq.
Proof: The original unit-direction rank-one formula differs from its identity reference only in that real scalar denominator.
-/
theorem unitLineUpdate_reference_ratio (B : E →L[ℝ] E) (g u : E) (hu : ‖u‖=1) :
    unitLineUpdate B g u=(inner ℝ u (B u))⁻¹ • unitLineUpdate (ContinuousLinearMap.id ℝ E) g u := by
  rw [unitLineUpdate_id g u hu]
  simp only [unitLineUpdate,smul_neg]

/-- The true fixed-unit-direction line error is at most twice the operator budget times its actual reference line norm.
Use: Keep uniform control when the genuine intermediate CG reference step is arbitrarily small.
Article: main_krylov, thm:UCq.
Proof: The real unit curvature lies above one half. Apply its proved reciprocal error bound to the exact true reference displacement ratio, retaining its norm as a factor.
-/
theorem unitLineUpdate_reference_relative (B : E →L[ℝ] E) (g u : E) (hu : ‖u‖=1)
    {ε : ℝ} (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤ε) (hε : ε≤1/2) :
    ‖unitLineUpdate B g u-unitLineUpdate (ContinuousLinearMap.id ℝ E) g u‖≤
      2*ε*‖unitLineUpdate (ContinuousLinearMap.id ℝ E) g u‖ := by
  have hcurv := unit_curvature_error B u hu hB
  have hhalf : (1/2 : ℝ) ≤ inner ℝ u (B u) := by linarith [(abs_le.mp hcurv).1]
  have hratio := (curvature_reciprocal_bound _ hhalf hcurv).2
  rw [unitLineUpdate_reference_ratio B g u hu]
  have he : (inner ℝ u (B u))⁻¹ • unitLineUpdate (ContinuousLinearMap.id ℝ E) g u-
      unitLineUpdate (ContinuousLinearMap.id ℝ E) g u=
      ((inner ℝ u (B u))⁻¹-1) • unitLineUpdate (ContinuousLinearMap.id ℝ E) g u := by module
  rw [he,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hratio (norm_nonneg _)

/-- The actual searched displacement has the same relative reference-line bound for every genuine nonzero raw direction.
Use: Apply the small-line mechanism to the original physical RFC search.
Article: main_krylov, thm:UCq.
Proof: Exact direction rescaling identifies both actual searched displacements with the same genuine normalized direction; apply the proved relative unit-direction estimate.
-/
theorem lineStep_reference_relative (B : E →L[ℝ] E) (g d : E) (hd : d≠0)
    {ε : ℝ} (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤ε) (hε : ε≤1/2) :
    ‖lineLength g d (B d) • d-lineLength g d d • d‖≤2*ε*‖lineLength g d d • d‖ := by
  have href : lineLength g d d • d=lineLength g d ((ContinuousLinearMap.id ℝ E) d) • d := rfl
  rw [href,lineStep_eq_unitLineUpdate B g d hd,
    lineStep_eq_unitLineUpdate (ContinuousLinearMap.id ℝ E) g d hd]
  exact unitLineUpdate_reference_relative B g _ (NormedSpace.norm_normalize hd) hB hε

/-- A true nonzero reference line remains nonzero under a half-identity operator perturbation along the same actual unit direction.
Use: Derive the positive true intermediate line norm without a quantitative step-size lower bound.
Article: main_krylov, thm:UCq.
Proof: The genuine curvature is positive, so its true reciprocal is nonzero in the exact reference displacement ratio.
-/
theorem unitLineUpdate_reference_nonzero (B : E →L[ℝ] E) (g u : E) (hu : ‖u‖=1)
    {ε : ℝ} (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤ε) (hε : ε≤1/2)
    (href : unitLineUpdate (ContinuousLinearMap.id ℝ E) g u≠0) : unitLineUpdate B g u≠0 := by
  have hcurv := unit_curvature_error B u hu hB
  have hpos : 0 < inner ℝ u (B u) := by linarith [(abs_le.mp hcurv).1]
  rw [unitLineUpdate_reference_ratio B g u hu]
  exact smul_ne_zero (inv_ne_zero hpos.ne') href

/-- Every genuine raw-direction search with a nonzero true identity-reference line remains nonzero under a half-identity operator perturbation.
Use: Supply the actual positive line premise in the small-dimensional prefix induction.
Article: main_krylov, thm:UCq.
Proof: Genuine direction normalization preserves both actual lines, and the proved real positive-curvature reference ratio preserves nonzeroness.
-/
theorem lineStep_reference_nonzero (B : E →L[ℝ] E) (g d : E) (hd : d≠0)
    {ε : ℝ} (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤ε) (hε : ε≤1/2)
    (href : lineLength g d d • d≠0) : lineLength g d (B d) • d≠0 := by
  have href' : unitLineUpdate (ContinuousLinearMap.id ℝ E) g (NormedSpace.normalize d)≠0 := by
    rw [← lineStep_eq_unitLineUpdate (ContinuousLinearMap.id ℝ E) g d hd]
    exact href
  rw [lineStep_eq_unitLineUpdate B g d hd]
  exact unitLineUpdate_reference_nonzero B g _ (NormedSpace.norm_normalize hd) hB hε href'

end
end krylov.Correction
