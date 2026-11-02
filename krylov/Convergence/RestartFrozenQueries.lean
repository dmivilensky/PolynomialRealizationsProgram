import krylov.Convergence.SS1LocalBounds
import krylov.Functions.MetricFCSourceBounds

/-!
Article: main_krylov, thm:D, arbitrary many frozen final corrections.
Use: execute genuine gradient queries against one fixed measured full
model and prove every extra query raises the small-source degree by one.
All intermediate queries are enclosed by the proof; no contraction or
output order is a premise. The native FC source module supplies the real
model-error and inverse bounds used by this generic correction lemma.
Source: the exact multipoint inverse-model equation and radial Taylor FTC.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Reference krylov.Functions krylov.Nonlinear
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Repeated true gradient queries with a single frozen full model.
Article: main_krylov, thm:D, k final corrections. -/
def frozenModelPoints (M : Matrix (Fin n) (Fin n) ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0=>x₀
  | j+1=>frozenModelPoints M G x₀ j-cgOperator M⁻¹ (G (frozenModelPoints M G x₀ j))

/-- The actual inverse-model query has the exact base-relative bound.
Article: main_krylov, apG:err and thm:D. -/
theorem frozen_query_error_bound (M base : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsUnit M.det) (x g : EuclideanSpace ℝ (Fin n)) :
    ‖x-cgOperator M⁻¹ g‖≤‖M⁻¹‖*(‖M-base‖*‖x‖+‖g-cgOperator base x‖) := by
  have hcancel : cgOperator M⁻¹ (cgOperator M x)=x := by
    change (Matrix.toEuclideanCLM (𝕜:=ℝ) M⁻¹) ((Matrix.toEuclideanCLM (𝕜:=ℝ) M) x)=x
    rw [←mul_apply_eq_comp,←map_mul,nonsing_inv_mul _ hM,map_one]
    rfl
  have he : x-cgOperator M⁻¹ g=
      cgOperator M⁻¹ (cgOperator (M-base) x-(g-cgOperator base x)) := by
    have hm : cgOperator (M-base) x=cgOperator M x-cgOperator base x := by
      simp only [cgOperator,map_sub,_root_.sub_apply]
    rw [hm]
    rw [show cgOperator M x-cgOperator base x-(g-cgOperator base x)=cgOperator M x-g by abel]
    rw [map_sub,hcancel]
  rw [he]
  have ho := (cgOperator M⁻¹).le_opNorm (cgOperator (M-base) x-(g-cgOperator base x))
  have hi := (norm_sub_le (cgOperator (M-base) x) (g-cgOperator base x)).trans
    (add_le_add ((cgOperator (M-base)).le_opNorm x) le_rfl)
  simp only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] at ho hi
  exact ho.trans (mul_le_mul_of_nonneg_left hi (norm_nonneg _))

set_option maxHeartbeats 800000 in
/-- Every actual frozen final correction raises the source degree by
one, uniformly for all measured models with the specified actual input
bounds. The derivative hypotheses are primitive local function data.
Article: main_krylov, thm:D, O(e_c^(k+2)). -/
theorem frozenModelPoints_source_degree
    (base : Matrix (Fin n) (Fin n) ℝ)
    (T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    {L : ℝ≥0} (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hG : ∀ z,‖T z‖≤r → HasFDerivAt G (H z) z)
    (B D J : ℝ) (hB : 0<B) (hD : 0≤D) (hJ : 0<J) :
    ∃ ep C : ℝ,0<ep ∧0<C ∧∀ ε : ℝ,0<ε → ε<ep →
      ∀ M : Matrix (Fin n) (Fin n) ℝ, IsUnit M.det → ‖M-base‖≤D*ε → ‖M⁻¹‖≤J →
      ∀ x₀ : EuclideanSpace ℝ (Fin n),‖x₀‖≤B*ε^2 →∀ j : ℕ,
      ‖frozenModelPoints M G x₀ j‖≤B*C^j*ε^(j+2) ∧
        ‖T (frozenModelPoints M G x₀ j)‖<r := by
  let P : ℝ := ((‖T.toContinuousLinearMap‖₊^3*L : ℝ≥0) : ℝ)
  let C := J*(D+P/2*B)+1
  have hP : 0≤P := NNReal.coe_nonneg _
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨min 1 (min (1/(C+1)) (r/(‖T.toContinuousLinearMap‖*B+1))),C,
    by positivity,hC,?_⟩
  intro ε hε he M hM hmodel hinv x₀ hx₀
  have he1 : ε≤1 := he.le.trans (min_le_left _ _)
  have hcontraction : C*ε≤1 := by
    have hh := (lt_div_iff₀ (by positivity : 0<C+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith only [hh,hε]
  have hradius : ‖T.toContinuousLinearMap‖*(B*ε^2)<r := by
    have hh := (lt_div_iff₀ (by positivity : 0<‖T.toContinuousLinearMap‖*B+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    have hs : ε^2≤ε := by nlinarith only [mul_le_mul_of_nonneg_left he1 hε.le]
    have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg (norm_nonneg (T.toContinuousLinearMap)) hB.le)
    nlinarith only [hh,hm,hε]
  have hbound : ∀ j,‖frozenModelPoints M G x₀ j‖≤B*ε^2*(C*ε)^j := by
    intro j
    induction j with
    | zero=>simpa only [frozenModelPoints,pow_zero,mul_one] using hx₀
    | succ j ih=>
      let x := frozenModelPoints M G x₀ j
      have hpower : (C*ε)^j≤1 := pow_le_one₀ (mul_nonneg hC.le hε.le) hcontraction
      have hx : ‖x‖≤B*ε^2 := ih.trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower (mul_nonneg hB.le (sq_nonneg ε)))
      have hlocal : ‖T x‖≤r := ((T.toContinuousLinearMap.le_opNorm x).trans
        (mul_le_mul_of_nonneg_left hx (norm_nonneg _))).trans hradius.le
      have hgrad : ‖G x-cgOperator base x‖≤P/2*(B*ε)*‖x‖ := by
        have hg := metric_gradient_quadratic_error T G H (cgOperator base) hr.le hG₀ hH₀ hH hG x hlocal
        have hx' : ‖x‖≤B*ε := hx.trans (by
          nlinarith only [mul_le_mul_of_nonneg_left he1 (mul_nonneg hB.le hε.le)])
        exact hg.trans (by
          have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx' (norm_nonneg x))
            (show 0≤P/2 by positivity)
          nlinarith only [hm])
      have hquery := frozen_query_error_bound M base hM x (G x)
      have hinner : ‖M-base‖*‖x‖+‖G x-cgOperator base x‖≤(D+P/2*B)*ε*‖x‖ := by
        have hm := mul_le_mul_of_nonneg_right hmodel (norm_nonneg x)
        nlinarith only [hm,hgrad]
      have hq : ‖x-cgOperator M⁻¹ (G x)‖≤C*ε*‖x‖ := by
        apply hquery.trans
        have hh := mul_le_mul hinv hinner
          (add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)) hJ.le
        exact hh.trans (by dsimp only [C]; nlinarith only [mul_nonneg hε.le (norm_nonneg x)])
      change ‖x-cgOperator M⁻¹ (G x)‖≤_
      exact hq.trans ((mul_le_mul_of_nonneg_left ih (mul_nonneg hC.le hε.le)).trans_eq
        (by rw [pow_succ]; ring))
  intro j
  constructor
  · exact (hbound j).trans_eq (by rw [mul_pow,pow_add]; ring)
  · have hp : (C*ε)^j≤1 := pow_le_one₀ (mul_nonneg hC.le hε.le) hcontraction
    have hx : ‖frozenModelPoints M G x₀ j‖≤B*ε^2 := (hbound j).trans (by
      nlinarith only [mul_le_mul_of_nonneg_left hp (mul_nonneg hB.le (sq_nonneg ε))])
    exact ((T.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hx (norm_nonneg _))).trans_lt hradius

end
end krylov.Convergence
