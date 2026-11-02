import krylov.Functions.PlanarCriticalPoint

/-!
Article: main_krylov, prop:Fcycle(iii), exact tensor-budget shrinking.
Use: scale the genuine indistinguishable cubic family while retaining its
true critical point, exact observed data fibre and finite-scale information
coefficient. Source: exact polynomial homogeneity of the original scalar
objectives and the proved genuine critical-point branch.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Tensor.BinaryCubic
open scoped InnerProductSpace

/-- Uniform scaling of the four actual tensor coefficients.
Article: main_krylov, prop:Fcycle(iii), true tensor-budget shrink. -/
def scaleBinaryCubic (a : ℝ) (t : krylov.Tensor.BinaryCubic) : krylov.Tensor.BinaryCubic :=
  ⟨a*t.t0,a*t.t1,a*t.t2,a*t.t3⟩

/-- Exact value scaling of the full genuine scalar cubic, including its
prescribed quadratic perturbation and linear reference part.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planeCubicObjective_tensor_scale (p r a : ℝ) (ha : a≠0)
    (t : krylov.Tensor.BinaryCubic) (x : Plane) :
    planeCubicObjective p r (scaleBinaryCubic a t) x=
      a⁻¹^2*planeCubicObjective (a*p) r t (a • x) := by
  unfold planeCubicObjective planarCubicObjective planarReferenceQuadratic planarValueFamily
    pairOfPlane scaleBinaryCubic
  simp only [ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',PiLp.smul_apply,smul_eq_mul]
  field_simp

/-- Exact Riesz-gradient scaling of the actual full scalar cubic family.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planeCubicGradient_tensor_scale (p r a : ℝ) (ha : a≠0)
    (t : krylov.Tensor.BinaryCubic) (x : Plane) :
    gradient (planeCubicObjective p r (scaleBinaryCubic a t)) x=
      a⁻¹ • gradient (planeCubicObjective (a*p) r t) (a • x) := by
  rw [planeCubicGradient_actual,planeCubicGradient_actual]
  ext i
  fin_cases i <;>
    simp [planeCubicGradient,planarCubicGradient,planarValueCoordinateDerivative,
      planeOfPair,pairOfPlane,scaleBinaryCubic] <;> field_simp

/-- Every bounded positive tensor rescaling has a genuine critical point
quadratically close to the common observed last point, uniformly in that
rescaling. The function and criticality are both actual scalar objects.
Article: main_krylov, prop:Fcycle(iii), true-minimizer shrink foundation. -/
theorem planeCubic_scaled_critical_localization (r : ℝ) (t : krylov.Tensor.BinaryCubic)
    (U : ℝ) (hU : 0<U) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ p : ℝ, 0<p → p<ε₀ →
      ∀ a : ℝ, 0<a → a≤U → ∃ x : Plane,
      gradient (planeCubicObjective p r (scaleBinaryCubic a t)) x=0 ∧
      ‖x-planeOfPair (p,r*p)‖≤C*p^2 := by
  obtain ⟨ψ,_,_,ep,B,hep,hB,hcritical⟩ := planarCubic_exists_localized_critical_branch r t
  refine ⟨ep/(U+1),2*B*U,by positivity,by positivity,?_⟩
  intro p hp he a ha haU
  have hsmall : a*p<ep := by
    have hh := (lt_div_iff₀ (by positivity : 0<U+1)).mp he
    nlinarith only [hh,mul_le_mul_of_nonneg_right haU hp.le,hp]
  have hc := hcritical (a*p) (mul_pos ha hp) hsmall
  let z := planeOfPair (ψ (a*p))
  let x := a⁻¹ • z
  have hgrad : gradient (planeCubicObjective (a*p) r t) z=0 := by
    rw [planeCubicGradient_actual]
    change planeOfPair (planarCubicGradient (a*p) r t (pairOfPlane (planeOfPair (ψ (a*p)))))=0
    rw [pairOfPlane_planeOfPair,planarCubicGradient_actual,hc.1]
    simp [planeOfPair,planarDifferentialCoordinates]
  refine ⟨x,?_,?_⟩
  · rw [planeCubicGradient_tensor_scale p r a ha.ne',show a • x=z by dsimp only [x]; simp only [smul_smul,mul_inv_cancel₀ ha.ne',one_smul],hgrad,smul_zero]
  · have heq : x-planeOfPair (p,r*p)=a⁻¹ • planeOfPair (ψ (a*p)-(a*p,r*(a*p))) := by
      rw [planeOfPair_sub,smul_sub]
      dsimp only [x,z]
      congr 1
      ext i
      fin_cases i <;> simp [planeOfPair] <;> field_simp
    rw [heq,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
    have hh := (planeOfPair_norm_le _).trans (mul_le_mul_of_nonneg_left hc.2 (by norm_num : (0:ℝ)≤2))
    calc
      _ ≤ a⁻¹*(2*(B*(a*p)^2)) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr ha.le)
      _ = 2*B*a*p^2 := by field_simp
      _ ≤ 2*B*U*p^2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haU (by positivity)) (sq_nonneg _)

end
end krylov.Functions
