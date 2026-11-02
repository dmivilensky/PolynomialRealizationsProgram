import krylov.ContinuumControl.Feedback

/-!
Article: main_krylov, apC:eq:f and apC:lem:fund.
Use: differentiate the actual state potential along drift and mass increments.
The statements concern genuine derivatives of scalar state curves; no Bellman
identity or potential derivative is included as an assumed certificate field.
Source: the chain, product, quotient and real-power rules of mathlib.
-/

namespace krylov.ContinuumControl
noncomputable section

/-- The homogeneous state potential of the continuum string problem.
Article: main_krylov, apC:eq:f. -/
def stateValue (γ : ℝ) (σ : ℝ → ℝ) (φ p K : ℝ) : ℝ :=
  K ^ (-γ) * feedbackValue γ σ (φ * p / K)

/-- Algebraic state-chain cancellation. Drift has velocity (p,0,0), and a unit
mass increment has velocity (0,φ,φ²). Both rates are kept arbitrary here.
Article: main_krylov, apC:lem:fund, the two directional identities. -/
theorem state_chain_algebra (γ φ p K t f dx dm : ℝ)
    (hφ : φ ≠ 0) (hp : p ≠ 0) (hK : K ≠ 0) (ht : t ≠ 0)
    (hb : (1 - φ * p / K) * (-1 / (2 * (φ * p / K) * t)) - γ * f =
      -t / (2 * (φ * p / K))) :
    (φ ^ 2 * dm * (-γ) / K) * f + (-1 / (2 * (φ * p / K) * t)) *
      (((p * dx * p + φ * (φ * dm)) * K - φ * p * (φ ^ 2 * dm)) / K ^ 2) =
      -1 / 2 * (p / (φ * t) * dx + φ * t / p * dm) := by
  field_simp at hb ⊢
  linear_combination φ ^ 2 * dm * hb

/-- The potential derivative along any smooth state path driven by drift and
mass, including an atom unfolded into a straight mass increment.
Article: main_krylov, apC:lem:fund. -/
theorem hasDerivAt_stateValue {γ x dx dm : ℝ} {σ φ p K : ℝ → ℝ}
    (hγ : γ ≠ 0) (hφ : φ x ≠ 0) (hp : p x ≠ 0) (hK : 0 < K x)
    (hs : 0 < σ (φ x * p x / K x))
    (hσ : HasDerivAt σ (deriv σ (φ x * p x / K x)) (φ x * p x / K x))
    (hgraph : (φ x * p x / K x) * deriv σ (φ x * p x / K x) *
        (σ (φ x * p x / K x) + 1 - φ x * p x / K x) =
      2 * σ (φ x * p x / K x) *
        (σ (φ x * p x / K x) - 1 - γ * (φ x * p x / K x)))
    (hdφ : HasDerivAt φ (p x * dx) x)
    (hdp : HasDerivAt p (φ x * dm) x)
    (hdK : HasDerivAt K (φ x ^ 2 * dm) x) :
    HasDerivAt (fun u => stateValue γ σ (φ u) (p u) (K u))
      (-(K x ^ (-γ)) / 2 *
        (p x / (φ x * Real.sqrt (σ (φ x * p x / K x))) * dx +
          φ x * Real.sqrt (σ (φ x * p x / K x)) / p x * dm)) x := by
  have hKn : K x ≠ 0 := ne_of_gt hK
  have hr : φ x * p x / K x ≠ 0 := div_ne_zero (mul_ne_zero hφ hp) hKn
  have hf := hasDerivAt_feedbackValue hγ hr hs hσ hgraph
  have hratio := (hdφ.mul hdp).div hdK hKn
  have hpow := hdK.rpow_const (Or.inl hKn) (p := -γ)
  have hd := hpow.mul (hf.comp x hratio)
  convert hd using 1
  · rfl
  · rw [Real.rpow_sub_one hKn]
    simp only [Function.comp_apply, Pi.mul_apply, Pi.div_apply]
    have hc := state_chain_algebra γ (φ x) (p x) (K x)
      (Real.sqrt (σ (φ x * p x / K x)))
      (feedbackValue γ σ (φ x * p x / K x)) dx dm hφ hp hKn
      (ne_of_gt (Real.sqrt_pos.2 hs)) (feedback_bellman γ σ hγ hr hs)
    linear_combination -(K x ^ (-γ)) * hc

/-- The terminal potential is strictly positive along every positive string
state satisfying the invariant φp ≥ K.
Article: main_krylov, proof of thm:value. -/
theorem stateValue_pos {γ φ p K : ℝ} {σ : ℝ → ℝ}
    (hγ : 0 < γ) (hK : 0 < K) (hdom : K ≤ φ * p)
    (hs : 0 < σ (φ * p / K)) :
    0 < stateValue γ σ φ p K := by
  exact mul_pos (Real.rpow_pos_of_pos hK _) (feedbackValue_pos hγ
    ((le_div_iff₀ hK).2 (by simpa using hdom)) hs)

/-- Completing the square with two reciprocal positive coefficients.
Article: main_krylov, apC:lem:fund. -/
theorem reciprocal_square {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a * b = 1) (v : ℝ) :
    (Real.sqrt a - v * Real.sqrt b) ^ 2 = a - 2 * v + b * v ^ 2 := by
  have hs : Real.sqrt a * Real.sqrt b = 1 := by
    rw [← Real.sqrt_mul ha.le b, hab, Real.sqrt_one]
  rw [sub_sq, mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
  calc
    _ = a - 2 * v * (Real.sqrt a * Real.sqrt b) + b * v ^ 2 := by ring
    _ = _ := by rw [hs]; ring

/-- The state derivative splits exactly into collected reward and square loss.
Article: main_krylov, apC:eq:fundamental, absolutely continuous part. -/
theorem drift_mass_square {φ p t : ℝ} (hφ : 0 < φ) (hp : 0 < p)
    (ht : 0 < t) (v : ℝ) :
    1 / 2 * (p / (φ * t) + φ * t / p * v ^ 2) =
      v + 1 / 2 *
        (Real.sqrt (p / (φ * t)) - v * Real.sqrt (φ * t / p)) ^ 2 := by
  have hrec : p / (φ * t) * (φ * t / p) = 1 := by
    field_simp
  rw [reciprocal_square (div_pos hp (mul_pos hφ ht))
    (div_pos (mul_pos hφ ht) hp) hrec v]
  ring

/-- Vanishing square loss identifies the unique feedback density.
Article: main_krylov, proof of thm:value, equality case. -/
theorem square_zero_iff_feedback {φ p t : ℝ} (hφ : 0 < φ) (hp : 0 < p)
    (ht : 0 < t) (v : ℝ) :
    (Real.sqrt (p / (φ * t)) - v * Real.sqrt (φ * t / p)) ^ 2 = 0 ↔
      v = p / (φ * t) := by
  have ha : 0 < p / (φ * t) := div_pos hp (mul_pos hφ ht)
  have hb : 0 < φ * t / p := div_pos (mul_pos hφ ht) hp
  have hrec : p / (φ * t) * (φ * t / p) = 1 := by field_simp
  have hs : Real.sqrt (p / (φ * t)) * Real.sqrt (φ * t / p) = 1 := by
    rw [← Real.sqrt_mul ha.le, hrec, Real.sqrt_one]
  rw [sq_eq_zero_iff, sub_eq_zero]
  constructor
  · intro hv
    have he := congrArg (fun u => u * Real.sqrt (p / (φ * t))) hv
    rw [← sq, Real.sq_sqrt ha.le] at he
    calc
      v = v * (Real.sqrt (p / (φ * t)) * Real.sqrt (φ * t / p)) := by rw [hs]; ring
      _ = p / (φ * t) := by linear_combination -he
  · intro hv
    rw [hv]
    calc
      _ = Real.sqrt (p / (φ * t)) *
          (Real.sqrt (p / (φ * t)) * Real.sqrt (φ * t / p)) := by rw [hs]; ring
      _ = _ := by rw [← mul_assoc, ← sq, Real.sq_sqrt ha.le]

end
end krylov.ContinuumControl
