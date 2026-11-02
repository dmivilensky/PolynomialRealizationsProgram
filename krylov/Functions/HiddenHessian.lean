import krylov.Functions.HiddenCubic
import krylov.Functions.SegmentHessian

/-!
Article: main_krylov, thm:struct and apA:lem:angle, exact hidden Hessian drift.
Use: compute the actual second and third derivatives of the indistinguishable
cubic, and its first, interior and correction secants through genuine integrals.
Source: explicit cubic family in Appendix G of main_krylov.
-/

namespace krylov.Functions
noncomputable section
open chebyshev1.Nonlinear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The rank-one symmetric bilinear form associated with a linear coordinate.
Article: main_krylov, thm:struct. -/
def coordinateSquare (φ : E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ := φ.smulRight φ

/-- The actual derivative field of the hidden cubic.
Article: main_krylov, thm:struct. -/
def hiddenDerivative (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ x : E) : E →L[ℝ] ℝ :=
  (c * (φ (x - x₀) * (φ (x - x₀) - 1) / 2)) • φ

/-- Its affine Hessian field.
Article: main_krylov, thm:struct. -/
def hiddenHessian (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (c * (φ (x - x₀) - 1 / 2)) • coordinateSquare φ

/-- The hidden polynomial has the claimed actual first derivative field.
Article: main_krylov, thm:struct. Proof: use the proved scalar chain rule. -/
theorem fderiv_hiddenCubic (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ x : E) :
    fderiv ℝ (hiddenCubic φ c x₀) x = hiddenDerivative φ c x₀ x :=
  (hiddenCubic_hasFDerivAt φ c x₀ x).fderiv

/-- Differentiate the actual derivative field, yielding the hidden affine Hessian.
Article: main_krylov, thm:struct.
Proof: differentiate the scalar quadratic coefficient and apply its linear rank-one action. -/
theorem hiddenDerivative_hasFDerivAt (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ x : E) :
    HasFDerivAt (hiddenDerivative φ c x₀) (hiddenHessian φ c x₀ x) x := by
  have hφ : HasFDerivAt (fun y => φ (y - x₀)) φ x := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using!
      φ.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x₀)
  have h := ((hφ.mul (hφ.sub_const 1)).mul_const (1 / 2 : ℝ)).const_mul c
  convert! h.smul_const φ using 1
  · ext y
    simp only [hiddenDerivative, div_eq_mul_inv, Pi.mul_apply, one_mul]
  · ext u v
    simp only [hiddenHessian, coordinateSquare, smul_apply, ContinuousLinearMap.smulRight_apply,
      add_apply, smul_eq_mul]
    ring

/-- The genuine third derivative field is the constant rank-one tensor c phi^3.
Article: main_krylov, thm:struct.
Proof: differentiate the affine Hessian coefficient. -/
theorem hiddenHessian_hasFDerivAt (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ x : E) :
    HasFDerivAt (hiddenHessian φ c x₀) ((c • φ).smulRight (coordinateSquare φ)) x := by
  let T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := (c • φ).smulRight (coordinateSquare φ)
  let C := (-c * (φ x₀ + 1 / 2)) • coordinateSquare φ
  have h := (T.hasFDerivAt (𝕜 := ℝ) (x := x)).add_const C
  convert! h using 1
  ext y v w
  simp only [hiddenHessian, T, C, coordinateSquare, ContinuousLinearMap.smulRight_apply,
    add_apply, smul_apply, map_sub, smul_eq_mul]
  ring

/-- The actual average Hessian of the hidden cubic is its midpoint Hessian.
Article: main_krylov, thm:struct.
Proof: identify its affine continuous-linear field, then reuse the genuine midpoint integral theorem. -/
theorem averaged_hiddenHessian (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ a u : E) :
    averagedDerivative (hiddenHessian φ c x₀) a u =
      hiddenHessian φ c x₀ (a + (1 / 2 : ℝ) • u) := by
  let H₀ := (-c * (φ x₀ + 1 / 2)) • coordinateSquare φ
  let T := (c • φ).smulRight (coordinateSquare φ)
  have he (x : E) : hiddenHessian φ c x₀ x = H₀ + T x := by
    ext v w
    simp only [hiddenHessian, H₀, T, coordinateSquare, smul_apply, map_sub,
      ContinuousLinearMap.smulRight_apply, add_apply, smul_eq_mul]
    ring
  rw [show hiddenHessian φ c x₀ = (fun x => H₀ + T x) from funext he]
  exact averagedHessian_affine H₀ T a u

/-- The first sampled segment has exactly zero hidden secant.
Article: main_krylov, thm:struct. Proof: the midpoint coordinate is one half. -/
theorem hidden_first_secant (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ s : E) (hs : φ s = 1) :
    averagedDerivative (hiddenHessian φ c x₀) x₀ s = 0 := by
  rw [averaged_hiddenHessian]
  simp [hiddenHessian, hs]

/-- Every interior sampled segment has the same hidden rank-one secant.
Article: main_krylov, thm:struct.
Proof: both endpoints have coordinate one, so the affine Hessian is constant on the segment. -/
theorem hidden_interior_secant (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ a s : E)
    (ha : φ (a - x₀) = 1) (hs : φ s = 0) :
    averagedDerivative (hiddenHessian φ c x₀) a s = (c / 2) • coordinateSquare φ := by
  rw [averaged_hiddenHessian]
  have he : φ (a + (1 / 2 : ℝ) • s - x₀) = 1 := by
    rw [show a + (1 / 2 : ℝ) • s - x₀ = (a - x₀) + (1 / 2 : ℝ) • s by abel,
      map_add, map_smul, ha, hs, smul_zero, add_zero]
  simp only [hiddenHessian, he]
  congr 1
  ring

/-- An arbitrary correction from the last sampled point has the exact source coefficient.
Article: main_krylov, thm:struct, B_c-A=(c/2)(1+w_0) phi phi^T.
Proof: evaluate the actual affine Hessian at the correction midpoint. -/
theorem hidden_correction_secant (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ a u : E)
    (ha : φ (a - x₀) = 1) :
    averagedDerivative (hiddenHessian φ c x₀) a u =
      (c / 2 * (1 + φ u)) • coordinateSquare φ := by
  rw [averaged_hiddenHessian]
  have he : φ (a + (1 / 2 : ℝ) • u - x₀) = 1 + (1 / 2 : ℝ) * φ u := by
    rw [show a + (1 / 2 : ℝ) • u - x₀ = (a - x₀) + (1 / 2 : ℝ) • u by abel,
      map_add, map_smul, ha, smul_eq_mul]
  simp only [hiddenHessian, he]
  congr 1
  ring

end
end krylov.Functions
