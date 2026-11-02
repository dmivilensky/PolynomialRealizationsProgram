import krylov.Functions.PlanarMetricShrink

/-!
Article: main_krylov, prop:Fcycle(iii), actual indistinguishable SC sources.
Use: apply one common linear shrink to both members of an extremal data
fibre, preserving exact observations while realizing the full printed
true-minimizer metric ball. Source: the actual smooth implicit critical
branch, exact affine Hessian, and the proved true-metric shrink margins.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Tensor.BinaryCubic krylov.Nonlinear krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- The full actual Hessian drift, including the prescribed quadratic
perturbation. Article: main_krylov, prop:Fcycle(iii). -/
theorem planeCubicHessian_scaled_norm_sub_id (p r a : ℝ) (hp : 0≤p) (ha : 0≤a)
    {t : krylov.Tensor.BinaryCubic} (ht : t.InBall) (x : Plane) :
    ‖planeCubicHessian p r (scaleBinaryCubic a t) x-ContinuousLinearMap.id ℝ Plane‖≤
      a*p*‖planeTerminalOperator r t‖+a*‖x-planeOfPair (p,r*p)‖ := by
  rw [planeCubicHessian_terminal_identity,planeTerminalOperator_scale,binary_canonicalVariation_scale]
  have he (A B : Plane →L[ℝ] Plane) :
      ContinuousLinearMap.id ℝ Plane+A+B-ContinuousLinearMap.id ℝ Plane=A+B := by abel
  rw [he]
  calc
    _ ≤ ‖p • (a • planeTerminalOperator r t)‖+
        ‖a • canonicalVariation t.tensor (x-planeOfPair (p,r*p))‖ := norm_add_le _ _
    _ = a*p*‖planeTerminalOperator r t‖+a*‖canonicalVariation t.tensor (x-planeOfPair (p,r*p))‖ := by
      rw [norm_smul,norm_smul,norm_smul,Real.norm_of_nonneg hp,Real.norm_of_nonneg ha]
      ring
    _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (binary_canonicalVariation_norm ht _) ha)

/-- A certificate about the genuine scalar objective and its actual
critical point. Every condition is proved by the realization theorem;
the positive matrix is the actual Hessian at that true minimum.
Article: main_krylov, prop:Fcycle(iii). -/
def PlanarTrueMetricRealization (p r a α : ℝ) (t : krylov.Tensor.BinaryCubic) (x : Plane) : Prop :=
  gradient (planeCubicObjective p r (scaleBinaryCubic α t)) x=0 ∧
  let b := physicalOperatorMatrix (planeCubicHessian p r (scaleBinaryCubic α t) x)
  ∃ hb : b.PosDef,
    cgOperator b=fderiv ℝ (gradient (planeCubicObjective p r (scaleBinaryCubic α t))) x ∧
    (∀ v : Plane, |(scaleBinaryCubic α t).tensor.form v v v|≤
      2*a*‖metricCoordinates b hb v‖^3) ∧
    IsStandardSelfConcordantOn (planeCubicObjective p r (scaleBinaryCubic α t))
      (planarTrueMetricBall (metricCoordinates b hb) x (canonicalCubicRadius a)) ∧
    IsMinOn (planeCubicObjective p r (scaleBinaryCubic α t))
      (planarTrueMetricBall (metricCoordinates b hb) x (canonicalCubicRadius a)) x

/-- Two arbitrary admissible fibre tensors admit the SAME linear shrink.
Both actual critical points are genuine minimizers on the complete printed
true-metric balls, with the exact 2a canonical tensor budget. The common
scale preserves every original equality of observed values and gradients.
Article: main_krylov, prop:Fcycle(iii), true-minimizer SC lower sources. -/
theorem planeCubic_pair_true_metric_realization (r a : ℝ) (ha : 0<a) (ha₁ : a<1)
    {t u : krylov.Tensor.BinaryCubic} (ht : t.InBall) (hu : u.InBall) :
    ∃ ε₀ C M : ℝ, 0<ε₀ ∧ 0<C ∧ 0<M ∧ ∀ p : ℝ, 0<p → p<ε₀ →
      let α := 2*a*(1-C*p)^3
      0<α ∧ α≤2*a ∧ ∃ x y : Plane,
        ‖x-planeOfPair (p,r*p)‖≤M*p^2 ∧
        ‖y-planeOfPair (p,r*p)‖≤M*p^2 ∧
        ‖planeCubicHessian p r (scaleBinaryCubic α t) x-ContinuousLinearMap.id ℝ Plane‖≤C*p ∧
        ‖planeCubicHessian p r (scaleBinaryCubic α u) y-ContinuousLinearMap.id ℝ Plane‖≤C*p ∧
        PlanarTrueMetricRealization p r a α t x ∧
        PlanarTrueMetricRealization p r a α u y := by
  obtain ⟨et,Bt,het,hBt,hxt⟩ := planeCubic_scaled_critical_localization r t (2*a) (by positivity)
  obtain ⟨eu,Bu,heu,hBu,hxu⟩ := planeCubic_scaled_critical_localization r u (2*a) (by positivity)
  let M := Bt+Bu
  let C := 2*a*(‖planeTerminalOperator r t‖+‖planeTerminalOperator r u‖+M)+1
  have hM : 0<M := by dsimp only [M]; positivity
  have hC : 0<C := by dsimp only [C]; positivity
  have hCt : 2*a*(‖planeTerminalOperator r t‖+M)≤C := by
    dsimp only [C]
    nlinarith only [mul_nonneg ha.le (norm_nonneg (planeTerminalOperator r u))]
  have hCu : 2*a*(‖planeTerminalOperator r u‖+M)≤C := by
    dsimp only [C]
    nlinarith only [mul_nonneg ha.le (norm_nonneg (planeTerminalOperator r t))]
  refine ⟨min et (min eu (min 1 (C+1)⁻¹)),C,M,by positivity,hC,hM,?_⟩
  intro p hp hep
  have hpet : p<et := lt_of_lt_of_le hep (min_le_left _ _)
  have hpeu : p<eu := lt_of_lt_of_le hep ((min_le_right _ _).trans (min_le_left _ _))
  have hpone : p<1 := lt_of_lt_of_le hep ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hpinv : p<(C+1)⁻¹ := lt_of_lt_of_le hep ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hq : 0<1-C*p := by
    have hpinv' : p<1/(C+1) := by rw [one_div]; exact hpinv
    have hh := (lt_div_iff₀ (by positivity : 0<C+1)).mp hpinv'
    nlinarith only [hh,hp]
  let q := 1-C*p
  let α := 2*a*q^3
  have hq₁ : q≤1 := by dsimp only [q]; nlinarith only [mul_nonneg hC.le hp.le]
  have hα : 0<α := by dsimp only [α]; positivity
  have hαU : α≤2*a := by
    have hh : q^3≤1 := pow_le_one₀ hq.le hq₁
    exact (mul_le_mul_of_nonneg_left hh (by positivity : 0≤2*a)).trans_eq (mul_one _)
  obtain ⟨x,hcritx,hx⟩ := hxt p hp hpet α hα hαU
  obtain ⟨y,hcrity,hy⟩ := hxu p hp hpeu α hα hαU
  have hx₂ : ‖x-planeOfPair (p,r*p)‖≤M*p^2 := hx.trans (by dsimp only [M]; nlinarith only [mul_nonneg hBu.le (sq_nonneg p)])
  have hy₂ : ‖y-planeOfPair (p,r*p)‖≤M*p^2 := hy.trans (by dsimp only [M]; nlinarith only [mul_nonneg hBt.le (sq_nonneg p)])
  have hpp : p^2≤p := by nlinarith only [hp,hpone]
  have hxx : ‖x-planeOfPair (p,r*p)‖≤M*p := hx₂.trans (mul_le_mul_of_nonneg_left hpp hM.le)
  have hyy : ‖y-planeOfPair (p,r*p)‖≤M*p := hy₂.trans (mul_le_mul_of_nonneg_left hpp hM.le)
  have hdrift (s : krylov.Tensor.BinaryCubic) (hs : s.InBall) (z : Plane)
      (hz : ‖z-planeOfPair (p,r*p)‖≤M*p)
      (hCs : 2*a*(‖planeTerminalOperator r s‖+M)≤C) :
      ‖planeCubicHessian p r (scaleBinaryCubic α s) z-ContinuousLinearMap.id ℝ Plane‖≤C*p := by
    calc
      _ ≤ α*p*‖planeTerminalOperator r s‖+α*‖z-planeOfPair (p,r*p)‖ :=
        planeCubicHessian_scaled_norm_sub_id p r α hp.le hα.le hs z
      _ ≤ α*p*‖planeTerminalOperator r s‖+α*(M*p) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hz hα.le)
      _ = α*(‖planeTerminalOperator r s‖+M)*p := by ring
      _ ≤ (2*a)*(‖planeTerminalOperator r s‖+M)*p :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hαU (by positivity)) hp.le
      _ ≤ C*p := mul_le_mul_of_nonneg_right hCs hp.le
  refine ⟨hα,hαU,x,y,hx₂,hy₂,hdrift t ht x hxx hCt,hdrift u hu y hyy hCu,?_,?_⟩
  · exact ⟨hcritx,planeCubic_shrunk_true_metric p r a M C hp.le ha ha₁ hM.le ht hCt hq x hxx hcritx⟩
  · exact ⟨hcrity,planeCubic_shrunk_true_metric p r a M C hp.le ha ha₁ hM.le hu hCu hq y hyy hcrity⟩

end
end krylov.Functions
