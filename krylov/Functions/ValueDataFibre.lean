import krylov.Functions.PolynomialValueModel

/-!
Article: main_krylov, prop:Fcycle(iii), exact function-value data fibres.
Use: construct actual cubic functions whose values and gradients agree at
all three planar observed points, while their final Hessians differ.
Source: Appendix G, Delta f=(Delta C/2)Y(X-p)(Y-rX).
-/

namespace krylov.Functions
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exact cubic perturbation invisible to the three planar value-gradient samples.
Article: main_krylov, prop:Fcycle(iii). -/
def valueFibreCubic (φ ψ : E →L[ℝ] ℝ) (d p r : ℝ) (x : E) : ℝ :=
  d / 2 * ψ x * (φ x - p) * (ψ x - r * φ x)

/-- The genuine first-differential field of the exact cubic data fibre.
Article: main_krylov, prop:Fcycle(iii). -/
def valueFibreDerivative (φ ψ : E →L[ℝ] ℝ) (d p r : ℝ) (x : E) : E →L[ℝ] ℝ :=
  (d / 2 * ψ x * (ψ x - 2 * r * φ x + r * p)) • φ +
    (d / 2 * (φ x - p) * (2 * ψ x - r * φ x)) • ψ

/-- The exact cubic data fibre is smooth to every finite order.
Article: main_krylov, prop:Fcycle(iii). -/
theorem valueFibreCubic_contDiff (φ ψ : E →L[ℝ] ℝ) (d p r : ℝ) (n : ℕ) :
    ContDiff ℝ n (valueFibreCubic φ ψ d p r) := by
  unfold valueFibreCubic
  fun_prop

/-- The displayed derivative is the actual Frechet derivative of the cubic perturbation.
Article: main_krylov, prop:Fcycle(iii).
Proof: differentiate the three genuine affine factors and collect the two covectors. -/
theorem valueFibreCubic_hasFDerivAt (φ ψ : E →L[ℝ] ℝ) (d p r : ℝ) (x : E) :
    HasFDerivAt (valueFibreCubic φ ψ d p r) (valueFibreDerivative φ ψ d p r x) x := by
  have hφ := φ.hasFDerivAt (x := x)
  have hψ := ψ.hasFDerivAt (x := x)
  have h := (((hψ.mul (hφ.sub_const p)).mul
    (hψ.sub (hφ.const_mul r))).const_mul (d / 2))
  convert! h using 1
  · ext y
    simp only [valueFibreCubic, Pi.mul_apply, Pi.sub_apply]
    ring
  · ext v
    simp only [valueFibreDerivative, smul_apply, add_apply,
      smul_eq_mul, sub_apply, Pi.mul_apply, Pi.sub_apply]
    ring

/-- The exact Hessian field of the data-fibre perturbation.
Article: main_krylov, prop:Fcycle(iii). -/
def valueFibreHessian (φ ψ : E →L[ℝ] ℝ) (d p r : ℝ) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (-d * r * ψ x) • φ.smulRight φ +
    (d / 2 * (2 * ψ x - 2 * r * φ x + r * p)) •
      (φ.smulRight ψ + ψ.smulRight φ) +
    (d * (φ x - p)) • ψ.smulRight ψ

/-- The claimed data-fibre Hessian differentiates the actual first-differential field.
Article: main_krylov, prop:Fcycle(iii).
Proof: differentiate its two scalar coefficients using the genuine product rule. -/
theorem valueFibreDerivative_hasFDerivAt (φ ψ : E →L[ℝ] ℝ) (d p r : ℝ) (x : E) :
    HasFDerivAt (valueFibreDerivative φ ψ d p r) (valueFibreHessian φ ψ d p r x) x := by
  have hφ := φ.hasFDerivAt (x := x)
  have hψ := ψ.hasFDerivAt (x := x)
  have hα := (hψ.mul
    ((hψ.sub (hφ.const_mul (2 * r))).add_const (r * p))).const_mul (d / 2)
  have hβ := ((hφ.sub_const p).mul
    ((hψ.const_mul 2).sub (hφ.const_mul r))).const_mul (d / 2)
  have h := (hα.smul_const φ).add (hβ.smul_const ψ)
  convert! h using 1
  · ext y v
    simp only [valueFibreDerivative, Pi.mul_apply, Pi.sub_apply, Pi.add_apply,
      add_apply, smul_apply, smul_eq_mul]
    ring
  · ext v w
    simp only [valueFibreHessian, smul_apply, add_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, sub_apply, Pi.sub_apply]
    ring

/-- The constant genuine third derivative of the exact data-fibre cubic.
Article: main_krylov, prop:Fcycle(iii). -/
def valueFibreThird (φ ψ : E →L[ℝ] ℝ) (d r : ℝ) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := by
  letI : AddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.addCommGroup (R := ℝ) (R₂ := ℝ) (M := E) (M₂ := E →L[ℝ] E →L[ℝ] ℝ)
  exact (-d * r) • ψ.smulRight (φ.smulRight φ) +
    d • (ψ - r • φ).smulRight (φ.smulRight ψ + ψ.smulRight φ) +
    d • φ.smulRight (ψ.smulRight ψ)

/-- The actual Hessian differentiates to the stated constant cubic tensor.
Article: main_krylov, prop:Fcycle(iii).
Proof: differentiate the three affine Hessian coefficients. -/
theorem valueFibreHessian_hasFDerivAt (φ ψ : E →L[ℝ] ℝ) (d p r : ℝ) (x : E) :
    HasFDerivAt (valueFibreHessian φ ψ d p r) (valueFibreThird φ ψ d r) x := by
  have : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  have hφ := φ.hasFDerivAt (x := x)
  have hψ := ψ.hasFDerivAt (x := x)
  have hα := hψ.const_mul (-d * r)
  have hβ := (((hψ.const_mul 2).sub (hφ.const_mul (2 * r))).add_const (r * p)).const_mul (d / 2)
  have hγ := (hφ.sub_const p).const_mul d
  have h := ((hα.smul_const (φ.smulRight φ)).add
    (hβ.smul_const (φ.smulRight ψ + ψ.smulRight φ))).add (hγ.smul_const (ψ.smulRight ψ))
  convert! h using 1
  ext u v w
  simp only [valueFibreThird, smul_apply, add_apply, sub_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

/-- Values and genuine derivatives vanish at each of the three observed planar points.
Article: main_krylov, prop:Fcycle(iii), exact indistinguishability.
Proof: use their actual coordinates (0,0), (p,0), (p,rp) in the proved derivative formula. -/
theorem valueFibreCubic_sample_zero (φ ψ : E →L[ℝ] ℝ) (d p r : ℝ) (x : E)
    (hx : (φ x = 0 ∧ ψ x = 0) ∨ (φ x = p ∧ ψ x = 0) ∨
      (φ x = p ∧ ψ x = r * p)) :
    valueFibreCubic φ ψ d p r x = 0 ∧
      HasFDerivAt (valueFibreCubic φ ψ d p r) (0 : E →L[ℝ] ℝ) x := by
  have hz : valueFibreCubic φ ψ d p r x = 0 ∧ valueFibreDerivative φ ψ d p r x = 0 := by
    rcases hx with h | h | h
    all_goals
      rcases h with ⟨hφ, hψ⟩
      constructor
      · dsimp only [valueFibreCubic]
        rw [hφ, hψ]
        ring
      · ext v
        simp only [valueFibreDerivative, hφ, hψ, smul_apply, add_apply, smul_eq_mul, zero_apply]
        ring
  exact ⟨hz.1, by simpa only [hz.2] using valueFibreCubic_hasFDerivAt φ ψ d p r x⟩

/-- Adding the cubic preserves the actual observed value and actual derivative of any base objective.
Article: main_krylov, prop:Fcycle(iii), exact data fibres. -/
theorem add_valueFibreCubic_sample (f : E → ℝ) (D : E →L[ℝ] ℝ)
    (φ ψ : E →L[ℝ] ℝ) (d p r : ℝ) (x : E) (hf : HasFDerivAt f D x)
    (hx : (φ x = 0 ∧ ψ x = 0) ∨ (φ x = p ∧ ψ x = 0) ∨
      (φ x = p ∧ ψ x = r * p)) :
    f x + valueFibreCubic φ ψ d p r x = f x ∧
      HasFDerivAt (fun y => f y + valueFibreCubic φ ψ d p r y) D x := by
  have hz := valueFibreCubic_sample_zero φ ψ d p r x hx
  exact ⟨by rw [hz.1, add_zero], by simpa only [add_zero] using! hf.add hz.2⟩

/-- The unobserved final Hessian differs by the exact printed rank-two tensor.
Article: main_krylov, prop:Fcycle(iii), the final Hessian matrix formula. -/
theorem valueFibreHessian_final (φ ψ : E →L[ℝ] ℝ) (d p r : ℝ) (x : E)
    (hφ : φ x = p) (hψ : ψ x = r * p) :
    valueFibreHessian φ ψ d p r x = (p * d / 2) •
      ((-2 * r ^ 2) • φ.smulRight φ + r • (φ.smulRight ψ + ψ.smulRight φ)) := by
  ext v w
  simp only [valueFibreHessian, hφ, hψ, smul_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

end
end krylov.Functions
