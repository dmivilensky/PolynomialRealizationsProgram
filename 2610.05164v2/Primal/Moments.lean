import «2610.05164v2».Primal.Density
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Article: 2610.05164v2, Theorem 5.1.
Moments.
Use: `«2610.05164v2».Primal.density_moment_cubic` feeds
`«2610.05164v2».Primal.moment_directional_c1` (moment directional c1).
-/
namespace «2610.05164v2».Primal
noncomputable section
open Set MeasureTheory Real «2610.05164v2».PrescribedSpeed
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `(∫ q in (0:ℝ)..2,f q)=∫ t in (0:ℝ)..1,2*g t`.

Use: `«2610.05164v2».Primal.density_moment_cubic` rewrites with this identity to establish the
precise assertion is `(∫ x,(speedData φ hφ).density κ x^((j:ℝ)/2))= ∫ t in (0:ℝ)..1,6*exp (-φ
t)*t^j*(normalizedAmplitude φ κ t)^j`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.density_moment_cubic`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem symmetric_cubic_integral {f g : ℝ → ℝ}
    (hi : IntervalIntegrable f volume 0 2)
    (hsym : ∀ q,f (2-q)=f q)
    (hg : ∀ t∈Icc (0:ℝ) 1,f (t^3)*(3*t^2)=g t) :
    (∫ q in (0:ℝ)..2,f q)=∫ t in (0:ℝ)..1,2*g t := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hl : IntervalIntegrable f volume 0 1 := hi.mono_set (by
    simp only [uIcc_of_le (by norm_num : (0:ℝ)≤1),uIcc_of_le (by norm_num : (0:ℝ)≤2)]
    intro q hq
    exact ⟨hq.1,hq.2.trans (by norm_num)⟩)
  have hr : IntervalIntegrable f volume 1 2 := hi.mono_set (by
    simp only [uIcc_of_le (by norm_num : (1:ℝ)≤2),uIcc_of_le (by norm_num : (0:ℝ)≤2)]
    intro q hq
    exact ⟨(by norm_num : (0:ℝ)≤1).trans hq.1,hq.2⟩)
  have href := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1) f 2
  have he : (∫ q in (0:ℝ)..1,f (2-q))=∫ q in (0:ℝ)..1,f q :=
    intervalIntegral.integral_congr (fun q _ => hsym q)
  rw [he] at href
  norm_num only [sub_zero,show (2:ℝ)-1=1 by norm_num] at href
  have hc := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun t : ℝ => t^3) (f' := fun t => 3*t^2) (g := f) (a := 0) (b := 1)
    (by fun_prop) (fun t _ => by convert! (hasDerivAt_id t).pow 3 using 1;norm_num)
    (fun t _ => by positivity)
  norm_num only [zero_pow (by decide : 3≠0),one_pow] at hc
  have hc' : (∫ t in (0:ℝ)..1,g t)=∫ q in (0:ℝ)..1,f q := by
    rw [← hc]
    apply intervalIntegral.integral_congr
    intro t ht
    exact (hg t (by simpa only [uIcc_of_le zero_le_one] using ht)).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals hl hr,← href,← hc',
    intervalIntegral.integral_const_mul]
  ring

/--
Defines `normalizedAmplitude` of type `ℝ` by `sqrt ((exp (φ t)+t*(2-t^3))/κ)`.

Use: `«2610.05164v2».Primal.density_moment_cubic` uses this definition to establish the precise
assertion is `(∫ x,(speedData φ hφ).density κ x^((j:ℝ)/2))= ∫ t in (0:ℝ)..1,6*exp (-φ
t)*t^j*(normalizedAmplitude φ κ t)^j`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.density_moment_cubic`.
-/
def normalizedAmplitude (φ : ℝ → ℝ) (κ t : ℝ) : ℝ :=
  sqrt ((exp (φ t)+t*(2-t^3))/κ)

/--
The precise assertion is `((speed φ (t^3)+t^3*(2-t^3))/κ)^((j:ℝ)/2)= t^j*(normalizedAmplitude φ
κ t)^j`.

Use: `«2610.05164v2».Primal.density_moment_cubic` rewrites with this identity to establish the
precise assertion is `(∫ x,(speedData φ hφ).density κ x^((j:ℝ)/2))= ∫ t in (0:ℝ)..1,6*exp (-φ
t)*t^j*(normalizedAmplitude φ κ t)^j`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.density_moment_cubic`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.speed_cubic` with the arguments
shown in the proof.
-/
theorem moment_power {φ : ℝ → ℝ} {κ t : ℝ} (hκ : 0<κ)
    (ht : t∈Icc (0:ℝ) 1) (j : Nat) :
    ((speed φ (t^3)+t^3*(2-t^3))/κ)^((j:ℝ)/2)=
      t^j*(normalizedAmplitude φ κ t)^j := by
  -- Use the identities/estimates `«2610.05164v2».Primal.speed_cubic` with the arguments shown
  -- in the proof.
  have hA : 0≤(exp (φ t)+t*(2-t^3))/κ := by
    have ht3 : t^3≤1 := pow_le_one₀ ht.1 ht.2
    exact div_nonneg (add_nonneg (exp_pos _).le
      (mul_nonneg ht.1 (by linarith))) hκ.le
  have he : (speed φ (t^3)+t^3*(2-t^3))/κ=
      t^2*((exp (φ t)+t*(2-t^3))/κ) := by
    rw [speed_cubic φ ht]
    ring
  rw [he]
  have hn : 0≤t^2*((exp (φ t)+t*(2-t^3))/κ) := mul_nonneg (sq_nonneg t) hA
  have hs : (t^2*((exp (φ t)+t*(2-t^3))/κ))^((j:ℝ)/2)=
      (sqrt (t^2*((exp (φ t)+t*(2-t^3))/κ)))^j := by
    rw [sqrt_eq_rpow,← rpow_mul_natCast hn]
    congr 1
    ring
  rw [hs,sqrt_mul (sq_nonneg t),sqrt_sq ht.1,mul_pow]
  rfl

/--
The precise assertion is `(∫ x,(speedData φ hφ).density κ x^((j:ℝ)/2))= ∫ t in (0:ℝ)..1,6*exp
(-φ t)*t^j*(normalizedAmplitude φ κ t)^j`.

Use: `«2610.05164v2».Primal.density_energy_stability` uses this identity to establish the
stated quantitative bound `(∫ x,(speedData φ hφ).density κ x^(3/2:ℝ))≤ exp δ*(∫ x,(speedData ψ
hψ).density κ x^(3/2:ℝ))`.

Article: 2610.05164v2, Theorem 5.1.

Proof: Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Clear the denominators using the available nonzero hypotheses, then verify the
remaining algebraic identity.
-/
theorem density_moment_cubic {φ : ℝ → ℝ} (hφ : Continuous φ) {κ : ℝ} (hκ : 0<κ)
    {j : Nat} (hj : 0<j) :
    (∫ x,(speedData φ hφ).density κ x^((j:ℝ)/2))=
      ∫ t in (0:ℝ)..1,6*exp (-φ t)*t^j*(normalizedAmplitude φ κ t)^j := by
  -- Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  let f : ℝ → ℝ := fun q => ((speed φ q+q*(2-q))/κ)^((j:ℝ)/2)/speed φ q
  let g : ℝ → ℝ := fun t => 3*exp (-φ t)*t^j*(normalizedAmplitude φ κ t)^j
  have hj' : 0<(j:ℝ)/2 := by positivity
  have hi : IntervalIntegrable f volume 0 2 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤2)).mpr
      ((speedData φ hφ).density_moment_rhs_integrable hκ hj')
  have hsym : ∀ q,f (2-q)=f q := by
    intro q
    have hD : speed φ (2-q)=speed φ q := by rw [speed,speed,coordinate_reflection]
    dsimp [f]
    rw [hD,show (2-q)*(2-(2-q))=q*(2-q) by ring]
  have hg : ∀ t∈Icc (0:ℝ) 1,f (t^3)*(3*t^2)=g t := by
    intro t ht
    dsimp [f,g]
    rw [moment_power hκ ht j,speed_cubic φ ht,exp_neg]
    by_cases ht0 : t=0
    · subst t
      simp [zero_pow hj.ne']
    · field_simp [ht0,exp_ne_zero]
  rw [(speedData φ hφ).density_moment hj']
  change (∫ q in Ioo (0:ℝ) 2,f q)=_
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤2),
    symmetric_cubic_integral hi hsym hg]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [g]
  ring

end
end «2610.05164v2».Primal
