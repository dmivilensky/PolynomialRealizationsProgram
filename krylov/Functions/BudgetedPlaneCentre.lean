import krylov.Functions.ReferencePlaneCentreUpper

/-!
Article: main_krylov, thm:Fplanar, known tensor-budget centre.
Use: normalize genuinely observed coefficients by the known diagonal
budget before centring the genuine unit fibre. No unknown tensor enters
the policy. Source: actual scalar cubic gradient homogeneity.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic
open scoped InnerProductSpace

/-- Uniform scaling of the actually observed three scalar coefficients.
Article: main_krylov, thm:Fplanar. -/
def scalePlaneObservation (B : ℝ) (O : Observation) : Observation :=
  ⟨B*O.t0,B*O.P,B*O.t3⟩

/-- The known budget normalizes all true observed coefficients exactly.
Article: main_krylov, thm:Fplanar. -/
theorem scalePlaneObservation_inverse (B r : ℝ) (hB : B≠0) (t : krylov.Tensor.BinaryCubic) :
    scalePlaneObservation B⁻¹ (observe r (scaleBinaryCubic B t))=observe r t := by
  unfold scalePlaneObservation observe scaleBinaryCubic
  congr 1 <;> field_simp [hB]

/-- An explicit data-only centre output for any known positive tensor
budget. The source's unknown coefficients are never supplied to it.
Article: main_krylov, thm:Fplanar. -/
def budgetedPlaneCentreOutput (B r p : ℝ) (O : Observation) : Plane :=
  B⁻¹ • planeCentreOutput r (B*p) (scalePlaneObservation B⁻¹ O)

/-- The actual endpoint-only budgeted centre attains the sharp coefficient
with its exact quadratic budget dependence and a fourth-order remainder.
Article: main_krylov, thm:Fplanar. -/
theorem budgetedPlaneCentreOutput_gradient_upper (B r : ℝ) (hB : 0<B) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → B*p≤1 →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      ‖gradient (planeCubicObjective p r (scaleBinaryCubic B t))
        (budgetedPlaneCentreOutput B r p (observe r (scaleBinaryCubic B t)))‖≤
        B^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*p^3+C*p^4 := by
  obtain ⟨C,hC,hupper⟩ := planeCentreOutput_gradient_upper r
  refine ⟨B^3*C,mul_pos (pow_pos hB _) hC,?_⟩
  intro p hp hp₁ t ht
  rw [budgetedPlaneCentreOutput,scalePlaneObservation_inverse B r hB.ne',
    planeCubicGradient_tensor_scale p r B hB.ne',smul_smul,mul_inv_cancel₀ hB.ne',one_smul,
    norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hB.le)]
  have hu := mul_le_mul_of_nonneg_left (hupper (B*p) (mul_pos hB hp) hp₁ t ht) (inv_nonneg.mpr hB.le)
  convert hu using 1
  field_simp [hB.ne']

end
end krylov.Functions
