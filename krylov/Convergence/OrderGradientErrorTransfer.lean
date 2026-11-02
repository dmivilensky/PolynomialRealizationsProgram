import krylov.Functions.MetricFCSourceBounds

/-!
Article: main_krylov, thm:D, true-gradient to true-error normalization.
Use: preserve the sharp quadratic or cubic leading constant when replacing
the actual dual gradient by the actual metric error. Uniform native
quadratic localization makes the genuine Taylor discrepancy O(e^4).
Source: real gradient Taylor estimate and exact positive-root coordinates.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Reference krylov.Functions krylov.Nonlinear krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Uniform genuine quadratic localization transfers either a quadratic
or cubic actual-gradient asymptotic bound to the identical leading actual
metric-error bound. This is a generic Taylor lemma; native policy bounds
are discharged in its function-level applications. Article: thm:D. -/
theorem actual_metric_error_of_gradient_asymptotic
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (G : E → E) (H : E → E →L[ℝ] E) {r : ℝ} (hr : 0<r)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base) {L : ℝ≥0}
    (hH : LipschitzOnWith L (coordinateDerivative (metricCoordinates base hb) H) (closedBall 0 r))
    (hG : ∀ z,‖metricCoordinates base hb z‖≤r → HasFDerivAt G (H z) z)
    (point : ℝ → X → E) (admission : X → Prop) (p : ℕ) (hp : p=2 ∨p=3) (C : ℝ)
    (hpoint : ∃ ep M : ℝ,0<ep ∧0<M ∧∀ ε : ℝ,0<ε → ε<ep →∀ u,admission u →
      ‖metricCoordinates base hb (point ε u)‖≤M*ε^2)
    (hgradient : ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε → ε<ep →∀ u,admission u →
      ‖cgOperator (metricRoot base)⁻¹ (G (point ε u))‖≤(C+η)*ε^p) :
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε → ε<ep →∀ u,admission u →
      ‖metricCoordinates base hb (point ε u)‖≤(C+η)*ε^p := by
  let T:=metricCoordinates base hb
  let R:=cgOperator (metricRoot base)⁻¹
  let P : ℝ:=((‖T.toContinuousLinearMap‖₊^3*L : ℝ≥0):ℝ)
  obtain ⟨ep,M,hep,hM,hsize⟩:=hpoint
  let J:=‖R‖*P/2*(‖R‖*M)^2
  have hP : 0≤P := NNReal.coe_nonneg _
  have hJ : 0≤J := by dsimp only [J];positivity
  intro η hη
  obtain ⟨eg,heg,hgrad⟩:=hgradient (η/2) (half_pos hη)
  refine ⟨min ep (min eg (min 1 (min (r/(M+1)) (η/(2*(J+1)))))),by positivity,?_⟩
  intro ε hε he u hu
  have he1 : ε≤1 := he.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heR : ε<r/(M+1) := he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have heJ : ε<η/(2*(J+1)) := he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have hx:=hsize ε hε (he.trans_le (min_le_left _ _)) u hu
  have hg:=hgrad ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu
  have he2 : ε^2≤ε := by nlinarith only [hε,he1]
  have hdomain : ‖T (point ε u)‖≤r := by
    have hh:=(lt_div_iff₀ (by positivity : 0<M+1)).mp heR
    exact hx.trans (by nlinarith only [hh,hε,mul_le_mul_of_nonneg_left he2 hM.le])
  have hphys : ‖point ε u‖≤‖R‖*M*ε^2 := by
    have hh:=T.symm.toContinuousLinearMap.le_opNorm (T (point ε u))
    change ‖T.symm (T (point ε u))‖≤‖R‖*‖T (point ε u)‖ at hh
    rw [T.symm_apply_apply] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hx (norm_nonneg R)).trans_eq (by ring))
  have hTaylor:=metric_gradient_quadratic_error T G H (cgOperator base) hr.le hG₀ hH₀ hH hG (point ε u) hdomain
  have hrem : ‖R (G (point ε u)-cgOperator base (point ε u))‖≤J*ε^4 := by
    apply (R.le_opNorm _).trans
    apply (mul_le_mul_of_nonneg_left hTaylor (norm_nonneg R)).trans
    have hh:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hphys 2)
      (mul_nonneg (norm_nonneg R) (div_nonneg hP (by norm_num : (0:ℝ)≤2)))
    calc
      _ = (‖R‖*(P/2))*‖point ε u‖^2 := by ring
      _ ≤ (‖R‖*(P/2))*(‖R‖*M*ε^2)^2 := hh
      _ = _ := by dsimp only [J];ring
  have hp4 : ε^4≤ε*ε^p := by
    rcases hp with rfl|rfl
    · nlinarith only [mul_le_mul_of_nonneg_right he1 (pow_nonneg hε.le 3)]
    · exact le_of_eq (by ring)
  have hJe : J*ε≤η/2 := by
    have hh:=(lt_div_iff₀ (by positivity : 0<2*(J+1))).mp heJ
    nlinarith only [hh,hε]
  have hrem' : ‖R (G (point ε u)-cgOperator base (point ε u))‖≤η/2*ε^p :=
    hrem.trans ((mul_le_mul_of_nonneg_left hp4 hJ).trans
      (by nlinarith only [mul_le_mul_of_nonneg_right hJe (pow_nonneg hε.le p)]))
  calc
    _ = ‖R (G (point ε u))-R (G (point ε u)-cgOperator base (point ε u))‖ := by
      rw [map_sub,sub_sub_cancel]
      exact (congrArg norm (canonical_reference_action base hb (point ε u))).symm
    _ ≤ ‖R (G (point ε u))‖+‖R (G (point ε u)-cgOperator base (point ε u))‖ := norm_sub_le _ _
    _ ≤ (C+η/2)*ε^p+η/2*ε^p := add_le_add hg hrem'
    _ = _ := by ring

end
end krylov.Convergence
