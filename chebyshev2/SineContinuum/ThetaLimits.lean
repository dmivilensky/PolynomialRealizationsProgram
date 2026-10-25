import chebyshev2.SineContinuum.ThetaPoisson

/-!
Article: chebyshev2, Proposition 2.
Theta Limits.
Use: `chebyshev2.SineContinuum.thetaTwo_tendsto_zero` feeds
`chebyshev2.SineContinuum.thetaModulus_tendsto_zero` (theta Modulus tendsto zero).
Proof chain: `chebyshev2.LocalObstruction.sine_green_scale_tail` — chebyshev2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities. The needed form is proved here.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `thetaThree v = 1+2*∑' j : ℕ, exp (-π*v)^((j+1)^2)`.

Use: `chebyshev2.SineContinuum.thetaThree_bounds` rewrites with this identity to establish
the stated quantitative bound `0 ≤ thetaThree v-1 ∧ thetaThree v-1 ≤ 2*exp (-π*v)/(1-exp
(-π*v))`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
private theorem thetaThree_nat {v : ℝ} (hv : 0 < v) :
    thetaThree v = 1+2*∑' j : ℕ, exp (-π*v)^((j+1)^2) := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hq : exp (-π*v)<1 := exp_lt_one_iff.mpr (by nlinarith [pi_pos])
  -- Prove the summability hs needed for the later infinite-sum manipulations.
  have hs : Summable (fun j : ℕ => exp (-π*v)^((j+1)^2)) := by
    apply (summable_geometric_of_lt_one (exp_pos _).le hq).of_nonneg_of_le
    · intro j; positivity
    · intro j
      exact pow_le_pow_of_le_one (exp_pos _).le hq.le (by nlinarith : j ≤ (j+1)^2)
  have ht (j : ℕ) : exp (-π*v)^((j+1)^2) = gaussianThetaTerm 0 v ((j:ℤ)+1) := by
    rw [← exp_nat_mul]
    unfold gaussianThetaTerm
    congr 1
    push_cast
    ring
  have hp : HasSum (fun j : ℕ => gaussianThetaTerm 0 v ((j:ℤ)+1))
      (∑' j : ℕ, exp (-π*v)^((j+1)^2)) := by
    simpa only [ht] using hs.hasSum
  have hn (j : ℕ) : gaussianThetaTerm 0 v (-((j:ℤ)+1)) =
      gaussianThetaTerm 0 v ((j:ℤ)+1) := by
    unfold gaussianThetaTerm
    congr 1
    push_cast
    ring
  have hp' : HasSum (fun j : ℕ => gaussianThetaTerm 0 v (-((j:ℤ)+1)))
      (∑' j : ℕ, exp (-π*v)^((j+1)^2)) := by simpa only [hn] using hp
  have h := hp.of_add_one_of_neg_add_one hp'
  change (∑' j : ℤ, gaussianThetaTerm 0 v j) = _
  rw [h.tsum_eq]
  simp only [gaussianThetaTerm,Int.cast_zero,zero_add,zero_pow (by norm_num : 2 ≠ 0),
    mul_zero,zero_mul,exp_zero]
  ring

/--
The stated quantitative bound `0 ≤ thetaThree v-1 ∧ thetaThree v-1 ≤ 2*exp (-π*v)/(1-exp
(-π*v))`.

Use: `chebyshev2.SineContinuum.thetaThree_tendsto_one` uses this bound to establish
convergence along the specified source filter to the specified limit: `Tendsto thetaThree atTop
(𝓝 1)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Use the identities/estimates
`_private.chebyshev2.SineContinuum.ThetaLimits.0.chebyshev2.SineContinuum.thetaThree_nat`
with the arguments shown in the proof.
-/
theorem thetaThree_bounds {v : ℝ} (hv : 0 < v) :
    0 ≤ thetaThree v-1 ∧ thetaThree v-1 ≤ 2*exp (-π*v)/(1-exp (-π*v)) := by
  -- Apply
  -- `_private.chebyshev2.SineContinuum.ThetaLimits.0.chebyshev2.SineContinuum.thetaThree_nat`
  -- to the displayed hypotheses, then match the resulting expression to the goal.
  have hq : exp (-π*v)<1 := exp_lt_one_iff.mpr (by nlinarith [pi_pos])
  have hg := (summable_geometric_of_lt_one (exp_pos (-π*v)).le hq).mul_left (exp (-π*v))
  -- Prove the summability hs needed for the later infinite-sum manipulations.
  have hs : Summable (fun j : ℕ => exp (-π*v)^((j+1)^2)) := by
    apply hg.of_nonneg_of_le
    · intro j; positivity
    · intro j
      rw [← pow_succ']
      exact pow_le_pow_of_le_one (exp_pos _).le hq.le (by nlinarith : j+1 ≤ (j+1)^2)
  have hle := hs.tsum_le_tsum (fun j => by
    rw [← pow_succ']
    exact pow_le_pow_of_le_one (exp_pos _).le hq.le (by nlinarith : j+1 ≤ (j+1)^2)) hg
  rw [tsum_mul_left,tsum_geometric_of_lt_one (exp_pos _).le hq] at hle
  rw [thetaThree_nat hv]
  constructor
  · have hn : (0:ℝ) ≤ ∑' j : ℕ, exp (-π*v)^((j+1)^2) :=
      tsum_nonneg (fun j => pow_nonneg (exp_pos (-π*v)).le ((j+1)^2))
    linarith
  · rw [div_eq_mul_inv]
    linarith

/--
Convergence along the specified source filter to the specified limit: `Tendsto thetaThree atTop
(𝓝 1)`.

Use: `chebyshev2.SineContinuum.thetaModulus_tendsto_zero` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto thetaModulus
atTop (𝓝 0)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection.
-/
theorem thetaThree_tendsto_one : Tendsto thetaThree atTop (𝓝 1) := by
  -- Record the convergence he with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have he : Tendsto (fun v : ℝ => exp (-π*v)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith [pi_pos] : -π<0))
  have hb := (he.const_mul 2).div (he.const_sub 1) (by norm_num)
  -- Record the convergence hs with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hs : Tendsto (fun v => thetaThree v-1) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (by simpa only [mul_zero,sub_zero,zero_div] using hb)
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with v hv using (thetaThree_bounds hv).1
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with v hv using (thetaThree_bounds hv).2
  convert hs.add_const 1 using 1 <;> simp

/--
Convergence along the specified source filter to the specified limit: `Tendsto thetaTwo atTop
(𝓝 0)`.

Use: `chebyshev2.SineContinuum.thetaModulus_tendsto_zero` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto thetaModulus
atTop (𝓝 0)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection. Prove equality of functions by evaluating both sides at
an arbitrary argument.
-/
theorem thetaTwo_tendsto_zero : Tendsto thetaTwo atTop (𝓝 0) := by
  -- Record the convergence he with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have he : Tendsto (fun v : ℝ => exp (-π*v)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith [pi_pos] : -π<0))
  -- Record the convergence he with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have he' : Tendsto (fun v : ℝ => exp (-π*v/4)) atTop (𝓝 0) := by
    convert tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
      (by linarith [pi_pos] : -π/4<0)) using 1
    funext v; dsimp; congr 1; ring
  have hb := (he'.const_mul 2).mul ((he.const_sub 1).inv₀ (by norm_num))
  apply squeeze_zero' _ _ (by simpa using hb)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with v hv
    exact (gaussianTheta_positive _ hv).le
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with v hv
    rw [thetaTwo_sigma₁ hv]
    simp only [neg_mul] at *
    apply mul_le_mul_of_nonneg_left (sigma₁_upper (exp_pos _).le _) (by positivity)
    exact exp_lt_one_iff.mpr (by nlinarith [pi_pos])

end
end chebyshev2.SineContinuum
