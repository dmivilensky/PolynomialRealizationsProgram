import krylov.Tensor.BinaryMixed

/-!
Article: main_krylov, thm:H, the gradient-only planar information witnesses.
Use: construct the source's two actual compatible binary cubics in the
genuine diagonal unit ball. Their observed cross coefficients agree while
their hidden tensor coordinates differ. Source: the two harmonic cubics
and a bounded pure mixed monomial, combined by the triangle inequality.
-/

namespace krylov.Tensor.BinaryCubic
noncomputable section
open Real

/-- The two unit harmonic binary tensors before the small cross-coefficient adjustment.
Article: main_krylov, proof of thm:H. -/
def gradientHarmonic (σ : ℝ) : BinaryCubic :=
  ⟨σ / sqrt 2, 1 / sqrt 2, -σ / sqrt 2, -1 / sqrt 2⟩

/-- Both signed harmonic tensors belong to the actual diagonal unit ball.
Article: main_krylov, thm:H, harmonic compatibility. -/
theorem gradientHarmonic_inBall (σ : ℝ) (hσ : σ ^ 2 = 1) :
    (gradientHarmonic σ).InBall := by
  intro c s hcs
  let A := c ^ 3 - 3 * c * s ^ 2
  let B := 3 * c ^ 2 * s - s ^ 3
  have hab : A ^ 2 + B ^ 2 = 1 := by
    calc
      _ = (c ^ 2 + s ^ 2) ^ 3 := by dsimp only [A, B]; ring
      _ = 1 := by rw [hcs]; norm_num
  have hsum : (σ * A + B) ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg (A - σ * B)]
  have he : (gradientHarmonic σ).eval c s = (σ * A + B) / sqrt 2 := by
    simp only [gradientHarmonic, eval, A, B]
    ring
  have hsq : ((gradientHarmonic σ).eval c s) ^ 2 ≤ 1 := by
    rw [he, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg ((gradientHarmonic σ).eval c s + 1)],
    by nlinarith [sq_nonneg ((gradientHarmonic σ).eval c s - 1)]⟩

/-- The small pure mixed monomial used to equalize the two observed probes.
Article: main_krylov, thm:H, the additional term of norm at most v*r. -/
def gradientMixed : BinaryCubic := ⟨0, 1 / sqrt 2, 0, 0⟩

/-- The adjustment is an actual admissible binary tensor.
Article: main_krylov, thm:H, the norm bound for the nonharmonic part. -/
theorem gradientMixed_inBall : gradientMixed.InBall := by
  intro c s hcs
  have hp : 0 ≤ (3 * c ^ 2 - 2) ^ 2 * (3 * c ^ 2 + 1) := by positivity
  have hmax : 27 * c ^ 4 * s ^ 2 ≤ 4 := by
    have hs : s ^ 2 = 1 - c ^ 2 := by linarith
    rw [hs]
    nlinarith only [hp]
  have he : (gradientMixed.eval c s) ^ 2 = 9 / 2 * c ^ 4 * s ^ 2 := by
    simp only [gradientMixed, eval, mul_zero, zero_mul, zero_add, add_zero]
    rw [show 3 * (1 / sqrt 2) * c ^ 2 * s = (3 * c ^ 2 * s) / sqrt 2 by ring,
      div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hsq : (gradientMixed.eval c s) ^ 2 ≤ 1 := by rw [he]; linarith only [hmax]
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (gradientMixed.eval c s + 1)],
    by nlinarith [sq_nonneg (gradientMixed.eval c s - 1)]⟩

/-- The actual signed gradient-only witness, with common observed t1+r*t2.
Article: main_krylov, thm:H, t^plus and t^minus. -/
def gradientWitness (r σ : ℝ) : BinaryCubic :=
  ⟨σ / (sqrt 2 * (1+r)), (1+σ*r) / (sqrt 2 * (1+r)),
    -σ / (sqrt 2 * (1+r)), -1 / (sqrt 2 * (1+r))⟩

/-- The source's two equal-probe witnesses are genuinely compatible tensors in the original binary ball.
Article: main_krylov, thm:H, the original uncertainty class. -/
theorem gradientWitness_inBall {r σ : ℝ} (hr : 0 ≤ r) (hσ : σ ^ 2 = 1) :
    (gradientWitness r σ).InBall := by
  have hσabs : |σ| = 1 := by nlinarith [sq_abs σ, abs_nonneg σ]
  have hd : 0 < 1 + r := by linarith
  intro c s hcs
  have he : (gradientWitness r σ).eval c s =
      ((gradientHarmonic σ).eval c s + σ * r * gradientMixed.eval c s) / (1+r) := by
    simp only [gradientWitness, gradientHarmonic, gradientMixed, eval]
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hd]
  apply (div_le_one hd).mpr
  have h := abs_add_le ((gradientHarmonic σ).eval c s) (σ * r * gradientMixed.eval c s)
  rw [abs_mul, abs_mul, hσabs, one_mul, abs_of_nonneg hr] at h
  have hh := gradientHarmonic_inBall σ hσ c s hcs
  have hm := gradientMixed_inBall c s hcs
  nlinarith [mul_le_mul_of_nonneg_left hm hr]

/-- The true observed cross coefficient agrees for both signs.
Article: main_krylov, thm:H, both last probes h+psi*e. -/
theorem gradientWitness_cross (r σ : ℝ) :
    (gradientWitness r σ).t1 + r * (gradientWitness r σ).t2 = 1 / (sqrt 2 * (1+r)) := by
  simp only [gradientWitness]
  ring

/-- The hidden base coefficient that cancels the true last diagonal observation.
Article: main_krylov, thm:H, beta_plus and beta_minus. -/
theorem gradientWitness_hidden (r σ k : ℝ) :
    -k * ((gradientWitness r σ).t2 + r * (gradientWitness r σ).t3) =
      (k / (sqrt 2 * (1+r))) * (σ+r) := by
  simp only [gradientWitness]
  ring

/-- The real unknown base lies inside the original uncertainty budget.
Article: main_krylov, thm:H, |beta_sign|<=k/sqrt(2)<=e_c. -/
theorem gradientWitness_base_bound {r σ k e : ℝ} (hr : 0 ≤ r) (hσ : σ ^ 2 = 1)
    (hk : 0 ≤ k) (hke : k ≤ e) :
    |(k / (sqrt 2 * (1+r))) * (σ+r)| ≤ e := by
  have hσabs : |σ| = 1 := by nlinarith [sq_abs σ, abs_nonneg σ]
  have hs : 1 ≤ sqrt (2 : ℝ) := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hd : 0 < 1 + r := by linarith
  have hb : |σ+r| ≤ 1+r := by simpa only [hσabs, abs_of_nonneg hr] using abs_add_le σ r
  rw [abs_mul, abs_of_nonneg (div_nonneg hk (by positivity))]
  calc
    _ ≤ k / (sqrt 2 * (1+r)) * (1+r) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = k / sqrt 2 := by field_simp
    _ ≤ k := (div_le_iff₀ (by positivity : 0 < sqrt (2 : ℝ))).mpr (by nlinarith only [hk, hs])
    _ ≤ e := hke

end
end krylov.Tensor.BinaryCubic
