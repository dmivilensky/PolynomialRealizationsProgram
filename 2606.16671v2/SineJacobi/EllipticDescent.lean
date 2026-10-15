import «2606.16671v2».SineJacobi.EllipticLanden

/-!
Article: 2606.16671v2, Theorem 5.2.
One certified descent step; no special-function identity is assumed.
Use: `«2606.16671v2».SineJacobi.ellipticA_bounds` feeds
`«2610.05164v2».SineContinuum.complementary_K_bound` (complementary K bound).
Proof chain: `«2606.16671v2».SineJacobi.sineEnergy_decimal` — 2606.16671v2, Theorem 5.2; Exact sine
gain, resolvent expression, asymptotics and energy value.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Real Set MeasureTheory

/--
Elliptic integral divided by π/2, with the squared-modulus convention.

Use: `«2606.16671v2».SineJacobi.ellipticA_bounds` uses this definition to establish the stated
quantitative bound `1 ≤ ellipticA x ∧ ellipticA x ≤ 1/sqrt (1-x)`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def ellipticA (x : ℝ) : ℝ := (2/Real.pi)*ellipticK (sqrt x)

/--
Defines `descendingModulus` of type `ℝ` by `(1-sqrt (1-x))/(1+sqrt (1-x))`.

Use: `«2606.16671v2».SineJacobi.descendingModulus_identity` uses this definition to establish
exact identity `2*sqrt (descendingModulus x)/(1+descendingModulus x) = sqrt x`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.
-/
def descendingModulus (x : ℝ) : ℝ := (1-sqrt (1-x))/(1+sqrt (1-x))

/--
Membership in the specified domain/enclosure: `descendingModulus x ∈ Ico (0:ℝ) 1`.

Use: `«2606.16671v2».SineJacobi.descendingModulus_identity` uses this assertion to establish
exact identity `2*sqrt (descendingModulus x)/(1+descendingModulus x) = sqrt x`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem descendingModulus_range {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    descendingModulus x ∈ Ico (0:ℝ) 1 := by
  have hs : 0 < sqrt (1-x) := sqrt_pos.mpr (by linarith [hx.2])
  have hs1 : sqrt (1-x) ≤ 1 := by
    have hh := sqrt_le_sqrt (show 1-x ≤ 1 by linarith [hx.1])
    simpa using hh
  unfold descendingModulus
  exact ⟨div_nonneg (by linarith) (by positivity), (div_lt_one (by positivity)).mpr (by linarith)⟩

/--
Exact identity `2*sqrt (descendingModulus x)/(1+descendingModulus x) = sqrt x`.

Use: `«2606.16671v2».SineJacobi.ellipticA_descent` rewrites with this identity to establish
exact identity `ellipticA x = (1+descendingModulus x)*ellipticA (descendingModulus x^2)`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem descendingModulus_identity {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    2*sqrt (descendingModulus x)/(1+descendingModulus x) = sqrt x := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hq := descendingModulus_range hx
  have hr := sq_sqrt (show 0 ≤ 1-x by linarith [hx.2])
  have hd : 1+sqrt (1-x) ≠ 0 := by positivity
  have hh : (2*sqrt (descendingModulus x)/(1+descendingModulus x))^2 = x := by
    rw [div_pow, mul_pow, sq_sqrt hq.1]
    unfold descendingModulus
    generalize sqrt (1-x) = r at hd hr ⊢
    field_simp
    nlinarith [hr]
  have hp : 0 ≤ 2*sqrt (descendingModulus x)/(1+descendingModulus x) :=
    div_nonneg (by positivity) (by linarith [hq.1])
  have ht := sq_sqrt hx.1
  nlinarith [sqrt_nonneg x]

/--
One certified descent step; no special-function identity is assumed.

Exact identity `ellipticA x = (1+descendingModulus x)*ellipticA (descendingModulus x^2)`.

Use: `«2606.16671v2».SineJacobi.ellipticWitnessValue_correct` rewrites with this identity to
establish membership in the specified domain/enclosure: `ellipticA x ∈ ellipticWitnessValue
ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.descendingModulus_range`,
`«2606.16671v2».SineJacobi.ellipticK_landen`,
`«2606.16671v2».SineJacobi.descendingModulus_identity` with the arguments shown in the proof.
-/
theorem ellipticA_descent {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    ellipticA x = (1+descendingModulus x)*ellipticA (descendingModulus x^2) := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.descendingModulus_range`,
  -- `«2606.16671v2».SineJacobi.ellipticK_landen`,
  -- `«2606.16671v2».SineJacobi.descendingModulus_identity` with the arguments shown in the
  -- proof.
  have hq := descendingModulus_range hx
  have hh := ellipticK_landen hq.1 hq.2
  rw [descendingModulus_identity hx] at hh
  unfold ellipticA
  rw [sqrt_sq hq.1, hh]
  ring

/--
The stated quantitative bound `1 ≤ ellipticA x ∧ ellipticA x ≤ 1/sqrt (1-x)`.

Use: `«2606.16671v2».SineJacobi.ellipticWitnessValue_correct` uses this bound to establish
membership in the specified domain/enclosure: `ellipticA x ∈ ellipticWitnessValue ws`.

Article: 2606.16671v2, Theorem 5.2 via `«2606.16671v2».SineJacobi.sineEnergy_decimal`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem ellipticA_bounds {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    1 ≤ ellipticA x ∧ ellipticA x ≤ 1/sqrt (1-x) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hk : |sqrt x| < 1 := by
    rw [abs_of_nonneg (sqrt_nonneg x)]
    simpa using sqrt_lt_sqrt hx.1 hx.2
  have hc := elliptic_integrand_continuous (sqrt x) hk
  have hi := hc.intervalIntegrable (μ := volume) 0 (Real.pi/2)
  have hp := sqrt_pos.mpr (show 0 < 1-x by linarith [hx.2])
  have hl : Real.pi/2 ≤ ellipticK (sqrt x) := by
    have hh := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) (half_pos pi_pos).le
      (f := fun _ : ℝ => 1) (g := fun theta => 1/sqrt (1-(sqrt x)^2*sin theta^2))
      intervalIntegrable_const hi
      (fun theta _ => by
        rw [le_div_iff₀ (sqrt_pos.mpr (elliptic_den_pos _ theta hk))]
        have hs := sqrt_le_sqrt (show 1-(sqrt x)^2*sin theta^2 ≤ 1 by nlinarith [sq_nonneg (sqrt x*sin theta)])
        simpa using hs)
    simpa [ellipticK] using hh
  have hu : ellipticK (sqrt x) ≤ (Real.pi/2)*(1/sqrt (1-x)) := by
    have hh := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) (half_pos pi_pos).le
      hi (f := fun theta => 1/sqrt (1-(sqrt x)^2*sin theta^2))
      (g := fun _ : ℝ => 1/sqrt (1-x)) intervalIntegrable_const
      (fun theta _ => by
        apply one_div_le_one_div_of_le hp
        apply sqrt_le_sqrt
        rw [sq_sqrt hx.1]
        nlinarith [mul_le_mul_of_nonneg_left (sin_sq_le_one theta) hx.1])
    simpa [ellipticK] using hh
  unfold ellipticA
  constructor
  · have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2/Real.pi by positivity)
    have he : (2/Real.pi)*(Real.pi/2) = 1 := by field_simp
    rwa [he] at hh
  · have hh := mul_le_mul_of_nonneg_left hu (show 0 ≤ 2/Real.pi by positivity)
    convert hh using 1
    field_simp

end
end «2606.16671v2».SineJacobi
