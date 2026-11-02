import krylov.Convergence.OrderSearchOnlyDomains

/-!
Article: main_krylov, thm:D, actual scalar search-only protocol embedding.
Use: identify every actual nonlinear record with the original raw policy
on its genuine Hessian averages. Positive line domains are derived on the
compact finite source tube; the unknown Hessian is not a policy input.
Source: actual chord stationarity/FTC and true recorded line parameters.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Exact scalar observations execute the real original correction-free
operator protocol on genuine Hessian averages, once its actual positive
search domain is established. Positivity is discharged uniformly below.
Article: main_krylov, thm:D, DC. -/
theorem scalarSearchOnlyRun_eq_methodRun
    (m : ProbedMethod E) (hm : CorrectionFree m)
    (T : E ≃L[ℝ] E) (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0)
    (hH₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z,‖T z‖≤r →HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖T z‖≤r →HasFDerivAt G (H z) z)
    (x₀ : E) (hx₀ : ‖T x₀‖<r/4) (N : ℕ)
    (hα : ∀ i<N,
      let A:=scalarSearchOnlyOperator m T f G H r x₀
      let J:=methodRun m A A (G x₀) i
      0<lineLength J.gradient (m.direction J) (A i (m.direction J))) :
    ∀ i≤N,scalarFunctionRun m T f G r x₀ i=
      methodRun m (scalarSearchOnlyOperator m T f G H r x₀)
        (scalarSearchOnlyOperator m T f G H r x₀) (G x₀) i := by
  let A:=scalarSearchOnlyOperator m T f G H r x₀
  have hloc:=scalarSearchOnlyPoint_localization m hm T hT f G H hr hG₀ hH₀ hLr hH hF hG x₀ (by linarith)
  have hsteps:=scalarSearchOnlyPoint_chord_steps m hm T hT f G H hr hH₀ hLr hH hF hG x₀
    (by linarith [norm_nonneg (T x₀)])
  have hsqrt : Real.sqrt (3:ℝ)≤2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg (3:ℝ)]
  have hlocal i : ‖T (scalarFunctionPoint m T f G r x₀ i)‖<r/2 := by
    have hh:=(hloc i).1.trans (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg (T x₀)))
    linarith
  intro i hi
  induction i with
  | zero=>rfl
  | succ i ih=>
    have hiN : i<N := by omega
    have he:=ih (by omega)
    let J:=scalarFunctionRun m T f G r x₀ i
    let x:=scalarFunctionPoint m T f G r x₀ i
    let y:=scalarFunctionPoint m T f G r x₀ (i+1)
    let d:=m.direction J
    have hg : J.gradient=G x := scalarSearchOnlyRun_gradient m hm T f G r x₀ i
    have hp : 0<lineLength J.gradient d (A i d) := by
      change 0<lineLength (scalarFunctionRun m T f G r x₀ i).gradient
        (m.direction (scalarFunctionRun m T f G r x₀ i))
        (A i (m.direction (scalarFunctionRun m T f G r x₀ i)))
      rw [he]
      exact hα i hiN
    have hd : d≠0 := by
      intro hz
      simp only [hz,map_zero,lineLength,inner_zero_left,neg_zero,zero_div] at hp
      exact (lt_irrefl 0) hp
    have hb:=metric_chord_operator_search T hT f G H hr hG₀ hH₀ hLr hH hF hG x d y (hlocal i) (hsteps i)
    change y-x=lineLength (G x) d (A i d) • d ∧G y=searchedGradient (G x) d (A i d) at hb
    rw [←hg] at hb
    have hy : metricLocalExactPoint T f (x₀+J.displacement) d r=y :=
      (scalarSearchOnlyPoint_succ m hm T f G r x₀ i).symm
    have hrec:=scalarFunctionRecord_quadratic m T f G r x₀ J (A i)
      (lineLength J.gradient d (A i d)) hp.ne' hd rfl
      (by rw [hy];exact hb.1) (by rw [hy];exact hb.2)
      (by have hc : m.correction J (A i d)=.done := hm _ _;rw [hc];trivial)
    change (⟨J.initial,scalarFunctionRecord m T f G r x₀ J::J.records⟩ : History E)=_
    rw [hrec]
    dsimp only [J]
    rw [he]
    rfl

end
end krylov.Convergence
