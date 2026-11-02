import krylov.Secant.ModelConvergence

/-!
Article: main_krylov, apG:mss, refined oldest-pair asymptotics.
Use: retain the actual leading oldest diagonal divided by its actual squared
distance, and prove that every remaining coefficient is little-o of the stated scale.
Source: the actual refined model-step bound and proved inverse-model convergence.
-/

namespace krylov.Secant
noncomputable section
open Matrix Filter Asymptotics Topology krylov.LinearAlgebra
open scoped Matrix Matrix.Norms.L2Operator
variable {α : Type*} {n : ℕ} {f : Filter α}

/-- The complete refined actual model step has its printed oldest-diagonal coefficient and little-o remainder.
Use: applies directly to X_D from the actual physical corrected-data identity,
including zero current errors and arbitrary filters of convergent nondegenerate models.
Article: main_krylov, apG:mss, final displayed asymptotic inequality.
Proof: uniform actual inverse norms bound both the oldest dual and the remainder
congruence. Inverse-model convergence makes the inverse-norm excess vanish;
its product with the first-order oldest diagonal and all other terms are little-o. -/
theorem oldest_model_asymptotic_bound
    (V X A : α → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (v : α → EuclideanSpace ℝ (Fin (n+1))) (q : α → ℝ)
    {C : ℝ} (hC : 0≤C) (hVU : ∀ᶠ x in f, IsUnit (V x).det)
    (hV : ∀ᶠ x in f, ‖(V x)⁻¹‖≤C)
    (hX : Tendsto X f (𝓝 0)) (hA : Tendsto A f (𝓝 1))
    (hdiag : (fun x => X x 0 0) =O[f] q)
    (hrest : (fun x => X x-X x 0 0 • vecMulVec (Pi.single 0 1) (Pi.single 0 1)) =o[f] q)
    (hnew : (fun x => A x-1) =o[f] q) :
    let J := fun x => 1+inverseCongruence (V x) (X x)
    ∃ r : α → ℝ, r =o[f] q ∧ ∀ᶠ x in f,
      ‖WithLp.toLp 2 (WithLp.ofLp (v x)-(J x)⁻¹*ᵥ (A x*ᵥ WithLp.ofLp (v x)))‖≤
        (|X x 0 0|/(Metric.infDist (euclideanColumn (V x) 0) (newerColumnSpan (V x) : Set _))^2+r x)*‖v x‖ := by
  let J := fun x => 1+inverseCongruence (V x) (X x)
  let R := fun x => X x-X x 0 0 • vecMulVec (Pi.single 0 1) (Pi.single 0 1)
  let a := fun x => |X x 0 0| * ‖oldestDual (V x)‖^2
  let b := fun x => ‖(V x)⁻¹‖^2*‖R x‖+‖A x-1‖
  have hconv := conditioned_model_convergence V X A v hC hV hX hA
  have hc2 : (fun x => ‖(V x)⁻¹‖^2) =O[f] (fun _ => (1 : ℝ)) := by
    apply IsBigO.of_bound (C^2)
    filter_upwards [hV] with x hx
    simpa only [Real.norm_of_nonneg (sq_nonneg _), norm_one, mul_one] using
      (sq_le_sq₀ (norm_nonneg _) hC).mpr hx
  have hb2 : (fun x => ‖oldestDual (V x)‖^2) =O[f] (fun _ => (1 : ℝ)) := by
    apply IsBigO.of_bound (C^2)
    filter_upwards [hV] with x hx
    simpa only [Real.norm_of_nonneg (sq_nonneg _), norm_one, mul_one] using
      (sq_le_sq₀ (norm_nonneg _) hC).mpr ((oldestDual_norm_le_inverse (V x)).trans hx)
  have ha : a =O[f] q := by simpa only [a, Real.norm_eq_abs, mul_one] using hdiag.norm_left.mul hb2
  have hb : b =o[f] q := by
    have hr := hc2.mul_isLittleO hrest.norm_left
    simp only [one_mul] at hr
    exact hr.add hnew.norm_left
  let r := fun x => (‖(J x)⁻¹‖-1)*a x+‖(J x)⁻¹‖*b x
  have hr : r =o[f] q := by
    have h1 := hconv.2.2.2.1.mul_isBigO ha
    have h2 := (hconv.2.1.norm.isBigO_one ℝ).mul_isLittleO hb
    simpa only [one_mul] using h1.add h2
  refine ⟨r, hr, ?_⟩
  -- The pointwise estimate uses the actual domains proved by model convergence.
  filter_upwards [hVU, hconv.2.2.1] with x hxV hxJ
  have hp := oldest_model_step_bound (V x) (X x) (A x) (J x) hxV
    (by dsimp only [J]; abel) hxJ (v x)
  convert hp using 1
  rw [oldest_column_distance (V x) hxV]
  simp only [leastGain, inv_pow, inv_inv, div_eq_mul_inv]
  dsimp only [r, a, b, R]
  ring

end
end krylov.Secant
