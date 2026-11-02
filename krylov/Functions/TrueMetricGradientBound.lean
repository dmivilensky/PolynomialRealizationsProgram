import krylov.Functions.HilbertPlaneMetricRealization
import krylov.Nonlinear.GradientQuadratic

/-!
Article: main_krylov, prop:Fcycle(iii), unrestricted actual-output error.
Use: convert the genuine gradient information lower bound to true-Hessian
metric error. No small-output assumption is imposed on a method: a numerical
case split derives the needed smallness from failure of the desired bound.
Source: genuine gradient FTC, actual positive-root energy and norm comparison.
-/
namespace krylov.Functions
noncomputable section
open Set Matrix krylov.Reference krylov.Secant krylov.Nonlinear
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
/-- Small true Hessian drift gives sharp linear and uniform inverse metric
bounds on every actual displacement. Article: main_krylov, prop:Fcycle(iii). -/
theorem trueMetric_linear_bounds (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    {τ : ℝ} (hτ : 0≤τ) (hτ₂ : τ≤1/2)
    (hd : ‖cgOperator base-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤τ)
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖cgOperator base v‖≤(1+τ)*‖metricCoordinates base hb v‖ ∧
      ‖v‖^2≤2*‖metricCoordinates base hb v‖^2 := by
  let Q := cgOperator base
  let S := metricCoordinates base hb
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Q-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))
  have hA : ‖A‖≤τ := hd
  have he (w : EuclideanSpace ℝ (Fin n)) : |inner ℝ w (Q w)-‖w‖^2|≤τ*‖w‖^2 := by
    have haw : ‖A w‖≤τ*‖w‖ :=
      (A.le_opNorm w).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg w))
    have hc : |inner ℝ w (A w)|≤‖w‖*‖A w‖ := abs_real_inner_le_norm w (A w)
    have hh := hc.trans (mul_le_mul_of_nonneg_left haw (norm_nonneg w))
    have heq : inner ℝ w (A w)=inner ℝ w (Q w)-‖w‖^2 := by
      dsimp only [A]
      rw [_root_.sub_apply,ContinuousLinearMap.id_apply,inner_sub_right,real_inner_self_eq_norm_sq]
    rw [heq] at hh
    exact hh.trans_eq (by ring)
  have hS (w : EuclideanSpace ℝ (Fin n)) : ‖S w‖≤(1+τ)*‖w‖ := by
    have hq := (abs_le.mp (he w)).2
    rw [←trueMetric_norm_sq base hb w] at hq
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤(1+τ)*‖w‖)).mp
    nlinarith only [hq,mul_nonneg hτ (sq_nonneg ‖w‖),mul_nonneg (sq_nonneg τ) (sq_nonneg ‖w‖)]
  have hSQ : S (S v)=Q v := by
    change cgOperator (metricRoot base) (cgOperator (metricRoot base) v)=Q v
    simp only [cgOperator,←mul_apply_eq_comp,←map_mul,metricRoot_square base hb,Q]
  refine ⟨by rw [←hSQ]; exact hS (S v),?_⟩
  have hl := (abs_le.mp (he v)).1
  rw [←trueMetric_norm_sq base hb v] at hl
  nlinarith only [hl,mul_le_mul_of_nonneg_right hτ₂ (sq_nonneg ‖v‖)]

/-- The actual gradient near a real stationary point obeys a global quadratic
bound in its own true-Hessian metric. For cubic objectives the actual Hessian
is globally Lipschitz, so the statement covers every unrestricted output.
Article: main_krylov, prop:Fcycle(iii). -/
theorem trueMetric_gradient_bound
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hG : ∀ x, HasFDerivAt G (H x) x) {L : ℝ≥0} (hH : LipschitzWith L H)
    (z : EuclideanSpace ℝ (Fin n)) (hz : G z=0)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (hbase : H z=cgOperator base)
    {τ : ℝ} (hτ : 0≤τ) (hτ₂ : τ≤1/2)
    (hd : ‖H z-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤τ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖G x‖≤(1+τ)*‖metricCoordinates base hb (x-z)‖+
      (L : ℝ)*‖metricCoordinates base hb (x-z)‖^2 := by
  have hshift : LipschitzOnWith L (fun v=>H (z+v)) univ := by
    have hh := hH.comp (isometry_add_left z).lipschitzWith
    convert! hh.lipschitzOnWith using 1
    simp only [mul_one]
  have hdshift v (_ : v∈(univ : Set (EuclideanSpace ℝ (Fin n)))) :
      HasFDerivAt (fun w=>G (z+w)) (H (z+v)) v := by
    convert! (hG (z+v)).comp v ((hasFDerivAt_id v).const_add z) using 1
  have ht := gradient_model_quadratic_error (fun v=>G (z+v)) (fun v=>H (z+v)) (H z)
    univ convex_univ (mem_univ _) (by rw [add_zero]) hshift hdshift (x-z) (mem_univ _)
  rw [add_sub_cancel,add_zero,hz,sub_zero,hbase] at ht
  have hm := trueMetric_linear_bounds base hb hτ hτ₂ (by rwa [hbase] at hd) (x-z)
  have hn := norm_le_norm_sub_add (G x) (cgOperator base (x-z))
  exact hn.trans ((add_le_add ht hm.1).trans (by
    have hh := mul_le_mul_of_nonneg_left hm.2 (by positivity : 0≤(L : ℝ)/2)
    nlinarith only [hh]))

/-- A true cubic gradient lower bound implies the same sharp cubic error
coefficient for every common output. Large outputs are covered directly;
smallness in the other case is derived, never assumed of the method.
Article: main_krylov, prop:Fcycle(iii). -/
theorem two_source_metric_error_lower {K E C B p e₀ e₁ g₀ g₁ : ℝ}
    (hK : 0≤K) (hE : 0≤E) (hC : 0≤C) (hB : 0≤B) (hp : 0≤p) (hp₁ : p≤1)
    (he₀ : 0≤e₀) (he₁ : 0≤e₁)
    (hlower : K*p^3-E*p^4≤max g₀ g₁)
    (hg₀ : g₀≤(1+C*p)*e₀+B*e₀^2) (hg₁ : g₁≤(1+C*p)*e₁+B*e₁^2) :
    K*p^3-(E+C*K+B*K^2)*p^4≤max e₀ e₁ := by
  let m := max e₀ e₁
  have hm : 0≤m := he₀.trans (le_max_left _ _)
  by_cases hsmall : m≤K*p^3
  · have h0 : e₀≤m := le_max_left _ _
    have h1 : e₁≤m := le_max_right _ _
    have hm2 : m^2≤K^2*p^6 := (pow_le_pow_left₀ hm hsmall 2).trans_eq (by ring)
    have hp6 : p^6≤p^4 := by
      have h2 : p^2≤1 := pow_le_one₀ hp hp₁
      nlinarith only [mul_le_mul_of_nonneg_right h2 (pow_nonneg hp 4)]
    have hbase : max g₀ g₁≤(1+C*p)*m+B*m^2 := max_le
      (hg₀.trans (add_le_add (mul_le_mul_of_nonneg_left h0 (by positivity))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he₀ h0 2) hB)))
      (hg₁.trans (add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he₁ h1 2) hB)))
    have hh := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hC hp)
    have hq := mul_le_mul_of_nonneg_left (hm2.trans (mul_le_mul_of_nonneg_left hp6 (sq_nonneg K))) hB
    dsimp only [m] at *
    nlinarith only [hlower,hbase,hh,hq]
  · exact (sub_le_self _ (by positivity : 0≤(E+C*K+B*K^2)*p^4)).trans (lt_of_not_ge hsmall).le

end
end krylov.Functions
