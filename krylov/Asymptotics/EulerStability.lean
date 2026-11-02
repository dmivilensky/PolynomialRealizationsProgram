import Mathlib.Analysis.ODE.DiscreteGronwall
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-!
Article: main_krylov, lower bound in thm:limit.
Use: a finite-grid stability estimate with the actual discrete evolution.
The proof reuses mathlib's discrete Grönwall theorem; finite hypotheses are
extended by clamping the error at its terminal value. A proved quadratic
one-step defect then gives the printed uniform first-order state error.
Source: discrete Grönwall, as in Hairer--Nørsett--Wanner, Solving ODEs I, II.3.
-/
namespace krylov.Asymptotics
noncomputable section
open Real Finset
open scoped BigOperators

/-- Finite-window form of the standard discrete Grönwall estimate. -/
theorem finite_grid_gronwall {N : ℕ} {e : ℕ → ℝ} {C L h Y : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hh : 0 ≤ h) (hNY : (N : ℝ) * h ≤ Y)
    (he₀ : e 0 = 0) (he : ∀ j ≤ N, 0 ≤ e j)
    (hrec : ∀ j < N, e (j + 1) ≤ (1 + L * h) * e j + C * h ^ 2)
    {j : ℕ} (hj : j ≤ N) : e j ≤ C * Y * exp (L * Y) * h := by
  let u : ℕ → ℝ := fun k ↦ e (min k N)
  have hu₀ : 0 ≤ u 0 := by simpa only [u, min_eq_left (Nat.zero_le N)] using he 0 (Nat.zero_le N)
  have hu (k : ℕ) (_hk : 0 ≤ k) :
      u (k + 1) ≤ (1 + L * h) * u k + C * h ^ 2 := by
    by_cases hk : k < N
    · simpa only [u, min_eq_left (Nat.succ_le_of_lt hk), min_eq_left hk.le] using hrec k hk
    · have hkN : N ≤ k := Nat.le_of_not_gt hk
      simp only [u, min_eq_right hkN, min_eq_right (hkN.trans (Nat.le_succ k))]
      nlinarith [mul_nonneg (mul_nonneg hL hh) (he N le_rfl), mul_nonneg hC (sq_nonneg h)]
  have hgr := discrete_gronwall (u := u) (c := fun _ ↦ L * h) (b := fun _ ↦ C * h ^ 2)
    hu₀ hu (fun _ _ ↦ mul_nonneg hL hh) (fun _ _ ↦ mul_nonneg hC (sq_nonneg h)) (Nat.zero_le j)
  simp only [u, min_eq_left hj, min_eq_left (Nat.zero_le N), he₀, zero_add,
    Nat.card_Ico, sum_const, Nat.sub_zero, nsmul_eq_mul] at hgr
  have hjh : (j : ℝ) * h ≤ Y := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) hh).trans hNY
  have hY : 0 ≤ Y := (mul_nonneg (Nat.cast_nonneg N) hh).trans hNY
  calc
    e j ≤ (j : ℝ) * (C * h ^ 2) * exp ((j : ℝ) * (L * h)) := hgr
    _ ≤ C * Y * exp (L * Y) * h := by
      have hpow : (j : ℝ) * (C * h ^ 2) = C * ((j : ℝ) * h) * h := by ring
      rw [hpow, show (j : ℝ) * (L * h) = L * ((j : ℝ) * h) by ring]
      have hexp : exp (L * ((j : ℝ) * h)) ≤ exp (L * Y) :=
        exp_le_exp.mpr (mul_le_mul_of_nonneg_left hjh hL)
      have hmul : C * ((j : ℝ) * h) * h ≤ C * Y * h := by gcongr
      calc
        C * ((j : ℝ) * h) * h * exp (L * ((j : ℝ) * h)) ≤ C * Y * h * exp (L * Y) := by gcongr
        _ = C * Y * exp (L * Y) * h := by ring

/-- The actual nonautonomous discrete step evolution. -/
def evolution {E : Type*} (step : ℕ → E → E) (initial : E) : ℕ → E
  | 0 => initial
  | k + 1 => step k (evolution step initial k)

/-- Genuine stable steps plus genuine local defects imply a uniform global
error bound for the constructed discrete evolution. -/
theorem evolution_error_bound {E : Type*} [NormedAddCommGroup E]
    {N : ℕ} {step : ℕ → E → E} {initial : E} {reference : ℕ → E}
    {C L h Y : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hNY : (N : ℝ) * h ≤ Y) (hinit : initial = reference 0)
    (hstep : ∀ j < N, ∀ x z, ‖step j x - step j z‖ ≤ (1 + L * h) * ‖x - z‖)
    (hdefect : ∀ j < N, ‖step j (reference j) - reference (j + 1)‖ ≤ C * h ^ 2)
    {j : ℕ} (hj : j ≤ N) :
    ‖evolution step initial j - reference j‖ ≤ C * Y * exp (L * Y) * h := by
  apply finite_grid_gronwall hC hL hh hNY (e := fun j ↦ ‖evolution step initial j - reference j‖)
    (by simp [evolution, hinit]) (fun _ _ ↦ norm_nonneg _) ?_ hj
  intro k hk
  change ‖step k (evolution step initial k) - reference (k + 1)‖ ≤ _
  calc
    _ ≤ ‖step k (evolution step initial k) - step k (reference k)‖ +
        ‖step k (reference k) - reference (k + 1)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1 + L * h) * ‖evolution step initial k - reference k‖ + C * h ^ 2 :=
      add_le_add (hstep k hk _ _) (hdefect k hk)

end
end krylov.Asymptotics
