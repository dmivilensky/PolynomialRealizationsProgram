import krylov.Functions.RankOneGeometry

/-!
Article: main_krylov, apA:lem:angle, the complete actual hidden increment sequence.
Use: recover the first, every interior and final correction increment from
the genuine trajectory and actual averaged Hessians; retain monotonicity as
nonnegativity of each real quadratic form.
Source: the explicitly differentiated hidden-cubic family in Appendix G.
-/

/-!
Article: krylov, Lemma E.11 [apA:lem:angle].

The entire hidden increment sequence has the stated rank-one form, and affine Hessians give the
exact midpoint contraction and normalized absolute cosine.
The divided identity requires nonzero cubic coefficient and midpoint displacement; the
undivided identity covers zero cases.
-/

namespace krylov.Functions
noncomputable section
open Set chebyshev1.Nonlinear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every actual sampled hidden secant has its exact first-or-interior value.
Article: main_krylov, apA:lem:angle.
Proof: the true step recurrence gives coordinates zero, one, one, ...; use
the previously proved actual first and interior Hessian integrals. -/
theorem hidden_trajectory_secant (p : ℕ) (x s : ℕ → E) (φ : E →L[ℝ] ℝ)
    (hstep : ∀ i < p, x (i + 1) = x i + s i)
    (hφ : ∀ i < p, φ (s i) = if i = 0 then 1 else 0)
    (c : ℝ) {i : ℕ} (hi : i < p) :
    averagedDerivative (hiddenHessian φ c (x 0)) (x i) (s i) =
      if i = 0 then 0 else (c / 2) • coordinateSquare φ := by
  by_cases hi₀ : i = 0
  · subst i
    rw [ite_eq_left rfl]
    exact hidden_first_secant φ c (x 0) (s 0) (by simpa using hφ 0 hi)
  · rw [ite_eq_right hi₀]
    apply hidden_interior_secant
    · have h := hidden_coordinate_of_steps p x s φ hstep hφ hi.le
      simpa only [ite_eq_right hi₀] using h
    · simpa only [ite_eq_right hi₀] using hφ i hi

/-- The first actual operator increment is the printed rank-one half-cubic slice.
Article: main_krylov, apA:lem:angle.
Proof: subtract the exact first and interior true secants. -/
theorem hidden_first_increment (p : ℕ) (hp : 2 ≤ p) (x s : ℕ → E) (φ : E →L[ℝ] ℝ)
    (hstep : ∀ i < p, x (i + 1) = x i + s i)
    (hφ : ∀ i < p, φ (s i) = if i = 0 then 1 else 0) (c : ℝ) :
    averagedDerivative (hiddenHessian φ c (x 0)) (x 1) (s 1) -
      averagedDerivative (hiddenHessian φ c (x 0)) (x 0) (s 0) =
        (c / 2) • coordinateSquare φ := by
  rw [hidden_trajectory_secant p x s φ hstep hφ c (by omega : 1 < p),
    hidden_trajectory_secant p x s φ hstep hφ c (by omega : 0 < p)]
  simp

/-- Every genuine interior hidden operator increment vanishes.
Article: main_krylov, apA:lem:angle.
Proof: consecutive actual interior segments have exactly the same rank-one secant. -/
theorem hidden_interior_increment (p : ℕ) (x s : ℕ → E) (φ : E →L[ℝ] ℝ)
    (hstep : ∀ i < p, x (i + 1) = x i + s i)
    (hφ : ∀ i < p, φ (s i) = if i = 0 then 1 else 0) (c : ℝ)
    {i : ℕ} (hi : 1 ≤ i) (hip : i + 1 < p) :
    averagedDerivative (hiddenHessian φ c (x 0)) (x (i + 1)) (s (i + 1)) -
      averagedDerivative (hiddenHessian φ c (x 0)) (x i) (s i) = 0 := by
  rw [hidden_trajectory_secant p x s φ hstep hφ c hip,
    hidden_trajectory_secant p x s φ hstep hφ c (by omega : i < p)]
  simp only [Nat.add_one_ne_zero, ite_false, ite_eq_right (by omega : i ≠ 0), sub_self]

/-- The actual final correction increment is c/2 times the hidden correction coordinate.
Article: main_krylov, apA:lem:angle.
Proof: subtract the last actual sampled secant from the actual correction
secant, whose midpoint coefficient was already evaluated exactly. -/
theorem hidden_final_increment (p : ℕ) (hp : 2 ≤ p) (x s : ℕ → E) (φ : E →L[ℝ] ℝ)
    (hstep : ∀ i < p, x (i + 1) = x i + s i)
    (hφ : ∀ i < p, φ (s i) = if i = 0 then 1 else 0) (c : ℝ) (u : E) :
    averagedDerivative (hiddenHessian φ c (x 0)) (x p) u -
      averagedDerivative (hiddenHessian φ c (x 0)) (x (p - 1)) (s (p - 1)) =
        (c / 2 * φ u) • coordinateSquare φ := by
  have hx : φ (x p - x 0) = 1 := by
    simpa only [ite_eq_right (by omega : p ≠ 0)] using
      hidden_coordinate_of_steps p x s φ hstep hφ (le_refl p)
  rw [hidden_correction_secant φ c (x 0) (x p) u hx,
    hidden_trajectory_secant p x s φ hstep hφ c (by omega : p - 1 < p),
    ite_eq_right (by omega : p - 1 ≠ 0), ← sub_smul]
  congr 1
  ring

/-- Nonnegative rank-one coefficients give genuine nonnegative quadratic increments.
Article: main_krylov, apA:lem:angle, monotone hidden drift.
Proof: the exact quadratic form is a nonnegative scalar times a real square. -/
theorem coordinateSquare_quadratic_nonneg (φ : E →L[ℝ] ℝ) {c : ℝ} (hc : 0 ≤ c) (v : E) :
    0 ≤ (c • coordinateSquare φ) v v := by
  change 0 ≤ c * (φ v * φ v)
  exact mul_nonneg hc (mul_self_nonneg _)

end
end krylov.Functions
