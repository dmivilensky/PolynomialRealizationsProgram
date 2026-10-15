import «2610.05164v2».Primal.ParameterBounds
import «2610.05164v2».Primal.Moments
import «2610.05164v2».Calibration.OneDeterminant
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: 2610.05164v2, Proposition 13.
Energy Stability.
Use: `«2610.05164v2».Primal.density_energy_stability` feeds
`«2610.05164v2».Primal.family_energy_ceiling` (family energy ceiling).
Proof chain: `«2610.05164v2».Primal.exact_primal_family_of_contraction` — 2610.05164v2, Theorem 5.2;
Contraction implies exact feasible density, uniqueness, iteration error and energy bound.
-/
namespace «2610.05164v2».Primal
noncomputable section
open Set MeasureTheory Real
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `logEnergyKernel` of type `ℝ` by `(3/2:ℝ)*log (exp y+c)-y`.

Use: `«2610.05164v2».Primal.energyKernel_stability` uses this definition to establish the
stated quantitative bound `energyKernel c u≤exp δ*energyKernel c v`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.family_energy_ceiling`.
-/
def logEnergyKernel (c y : ℝ) : ℝ := (3/2:ℝ)*log (exp y+c)-y
/--
Defines `energyKernel` of type `ℝ` by `(sqrt (exp y+c))^3*exp (-y)`.

Use: `«2610.05164v2».Primal.energy_integrand_factor` rewrites with this definition to establish
the precise assertion is `6*exp (-φ t)*t^3*(normalizedAmplitude φ κ t)^3= (6*t^3/(sqrt
κ)^3)*energyKernel (t*(2-t^3)) (φ t)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.family_energy_ceiling`.
-/
def energyKernel (c y : ℝ) : ℝ := (sqrt (exp y+c))^3*exp (-y)

/--
The actual derivative at the stated point: `HasDerivAt (logEnergyKernel c) ((3/2:ℝ)*(exp y/(exp
y+c))-1) y`.

Use: `«2610.05164v2».Primal.logEnergyKernel_lipschitz` uses this derivative formula to
establish the stated quantitative bound `|logEnergyKernel c u-logEnergyKernel c v|≤|u-v|`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.family_energy_ceiling`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem logEnergyKernel_derivative {c : ℝ} (hc : 0≤c) (y : ℝ) :
    HasDerivAt (logEnergyKernel c) ((3/2:ℝ)*(exp y/(exp y+c))-1) y :=
  (((Real.hasDerivAt_exp y).add_const c).log
    (ne_of_gt (add_pos_of_pos_of_nonneg (exp_pos y) hc))).const_mul (3/2) |>.sub
      (hasDerivAt_id y)
/--
The stated quantitative bound `|logEnergyKernel c u-logEnergyKernel c v|≤|u-v|`.

Use: `«2610.05164v2».Primal.energyKernel_stability` uses this bound to establish the stated
quantitative bound `energyKernel c u≤exp δ*energyKernel c v`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.family_energy_ceiling`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.logEnergyKernel_derivative` with the
arguments shown in the proof.
-/
theorem logEnergyKernel_lipschitz {c : ℝ} (hc : 0≤c) (u v : ℝ) :
    |logEnergyKernel c u-logEnergyKernel c v|≤|u-v| := by
  -- Use the identities/estimates `«2610.05164v2».Primal.logEnergyKernel_derivative` with the
  -- arguments shown in the proof.
  have hd := fun y (_ : y∈(univ:Set ℝ)) => (logEnergyKernel_derivative hc y).hasDerivWithinAt (s := Set.univ)
  have hb : ∀ y∈(univ:Set ℝ),‖(3/2:ℝ)*(exp y/(exp y+c))-1‖≤1 := by
    intro y _
    have hp : 0<exp y+c := add_pos_of_pos_of_nonneg (exp_pos y) hc
    have h0 : 0≤exp y/(exp y+c) := div_nonneg (exp_pos y).le hp.le
    have h1 : exp y/(exp y+c)≤1 := (div_le_one hp).mpr (by linarith)
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> linarith
  simpa only [Real.norm_eq_abs,one_mul] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb convex_univ (mem_univ v) (mem_univ u)

/--
Exact identity `exp (logEnergyKernel c y)=energyKernel c y`.

Use: `«2610.05164v2».Primal.energyKernel_stability` rewrites with this identity to establish
the stated quantitative bound `energyKernel c u≤exp δ*energyKernel c v`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.family_energy_ceiling`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.sqrt_cube_eq_rpow` with the
arguments shown in the proof.
-/
theorem exp_logEnergyKernel {c : ℝ} (hc : 0≤c) (y : ℝ) :
    exp (logEnergyKernel c y)=energyKernel c y := by
  have hp : 0<exp y+c := add_pos_of_pos_of_nonneg (exp_pos y) hc
  rw [logEnergyKernel,energyKernel,sub_eq_add_neg,exp_add,
    «2610.05164v2».Calibration.sqrt_cube_eq_rpow hp.le,rpow_def_of_pos hp]
  congr 2
  ring

/--
The stated quantitative bound `energyKernel c u≤exp δ*energyKernel c v`.

Use: `«2610.05164v2».Primal.density_energy_stability` uses this bound to establish the stated
quantitative bound `(∫ x,(speedData φ hφ).density κ x^(3/2:ℝ))≤ exp δ*(∫ x,(speedData ψ
hψ).density κ x^(3/2:ℝ))`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.family_energy_ceiling`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.logEnergyKernel_lipschitz`,
`«2610.05164v2».Primal.exp_logEnergyKernel` with the arguments shown in the proof.
-/
theorem energyKernel_stability {c δ u v : ℝ} (hc : 0≤c) (hδ : |u-v|≤δ) :
    energyKernel c u≤exp δ*energyKernel c v := by
  have h := (le_abs_self (logEnergyKernel c u-logEnergyKernel c v)).trans
    ((logEnergyKernel_lipschitz hc u v).trans hδ)
  have he := exp_le_exp.mpr (show logEnergyKernel c u≤δ+logEnergyKernel c v by linarith)
  rw [exp_add,exp_logEnergyKernel hc u,exp_logEnergyKernel hc v] at he
  exact he

/--
The precise assertion is `6*exp (-φ t)*t^3*(normalizedAmplitude φ κ t)^3= (6*t^3/(sqrt
κ)^3)*energyKernel (t*(2-t^3)) (φ t)`.

Use: `«2610.05164v2».Primal.density_energy_stability` rewrites with this identity to establish
the stated quantitative bound `(∫ x,(speedData φ hφ).density κ x^(3/2:ℝ))≤ exp δ*(∫
x,(speedData ψ hψ).density κ x^(3/2:ℝ))`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.family_energy_ceiling`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem energy_integrand_factor (φ : ℝ → ℝ) (κ t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    6*exp (-φ t)*t^3*(normalizedAmplitude φ κ t)^3=
      (6*t^3/(sqrt κ)^3)*energyKernel (t*(2-t^3)) (φ t) := by
  have ht3 : t^3≤1 := pow_le_one₀ ht.1 ht.2
  have hp : 0≤exp (φ t)+t*(2-t^3) :=
    add_nonneg (exp_pos _).le (mul_nonneg ht.1 (by linarith))
  rw [normalizedAmplitude,sqrt_div hp,div_pow,energyKernel]
  ring

/--
The stated quantitative bound `(∫ x,(speedData φ hφ).density κ x^(3/2:ℝ))≤ exp δ*(∫
x,(speedData ψ hψ).density κ x^(3/2:ℝ))`.

Use: `«2610.05164v2».Primal.family_energy_ceiling` uses this bound to establish the stated
quantitative bound `(∫ x,(familySpeed c directions a).density κ x^(3/2:ℝ))≤ exp (6*ρ)*(∫
x,(familySpeed c directions 0).density κ x^(3/2:ℝ))`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.family_energy_ceiling`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.density_moment_cubic`,
`«2610.05164v2».Primal.energy_integrand_factor`, `«2610.05164v2».Primal.energyKernel_stability`
with the arguments shown in the proof.
-/
theorem density_energy_stability {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    {κ δ : ℝ} (hκ : 0<κ) (hδ : ∀ t∈Icc (0:ℝ) 1,|φ t-ψ t|≤δ) :
    (∫ x,(speedData φ hφ).density κ x^(3/2:ℝ))≤
      exp δ*(∫ x,(speedData ψ hψ).density κ x^(3/2:ℝ)) := by
  -- Use the identities/estimates `«2610.05164v2».Primal.density_moment_cubic`,
  -- `«2610.05164v2».Primal.energy_integrand_factor`,
  -- `«2610.05164v2».Primal.energyKernel_stability` with the arguments shown in the proof.
  have hφ' := density_moment_cubic hφ hκ (j := 3) (by decide)
  have hψ' := density_moment_cubic hψ hκ (j := 3) (by decide)
  norm_num only [Nat.cast_ofNat] at hφ' hψ'
  rw [hφ',hψ',← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on zero_le_one
  · apply Continuous.intervalIntegrable
    dsimp [normalizedAmplitude]
    fun_prop
  · apply Continuous.intervalIntegrable
    dsimp [normalizedAmplitude]
    fun_prop
  · intro t ht
    have ht3 : t^3≤1 := pow_le_one₀ ht.1 ht.2
    have hc : 0≤t*(2-t^3) := mul_nonneg ht.1 (by linarith)
    rw [energy_integrand_factor φ κ t ht,energy_integrand_factor ψ κ t ht]
    have hC : 0≤6*t^3/(sqrt κ)^3 :=
      div_nonneg (mul_nonneg (by norm_num) (pow_nonneg ht.1 _))
        (pow_nonneg (sqrt_nonneg κ) _)
    have h := mul_le_mul_of_nonneg_left (energyKernel_stability hc (hδ t ht)) hC
    convert h using 1
    ring

/--
The stated quantitative bound `(∫ x,(familySpeed c directions a).density κ x^(3/2:ℝ))≤ exp
(6*ρ)*(∫ x,(familySpeed c directions 0).density κ x^(3/2:ℝ))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem 5.2.

Proof: Use the identities/estimates `«2610.05164v2».Primal.density_energy_stability`,
`«2610.05164v2».Primal.profile_continuous`, `«2610.05164v2».Primal.profile_difference_bound`
with the arguments shown in the proof.
-/
theorem family_energy_ceiling (c : Fin 17 → ℝ) (directions : Fin 6 → Nat)
    {a : Fin 6 → ℝ} {ρ κ : ℝ} (ha : ‖a‖≤ρ) (hκ : 0<κ) :
    (∫ x,(familySpeed c directions a).density κ x^(3/2:ℝ))≤
      exp (6*ρ)*(∫ x,(familySpeed c directions 0).density κ x^(3/2:ℝ)) := by
  apply density_energy_stability (profile_continuous c directions a)
    (profile_continuous c directions 0) hκ
  intro t ht
  exact profile_difference_bound c directions (by simpa using ha) ht

end
end «2610.05164v2».Primal
