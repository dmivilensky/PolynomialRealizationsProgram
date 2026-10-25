import polyak.Duality.Certificate
import polyak.Energy.Slack

/-!
Article: Appendix A, Lemma energy, the nonnegative combination Z and cancellation of values.
Use: the actual finite strict certificate, with all original interpolation signs.
Proof: expand the interpolation slacks and use precisely the certificate's charge equation.
-/

noncomputable section

namespace polyak.Energy

open Interpolation Duality Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : C(Frequency, ℂ)} {t : ℝ}

/-- Article: Q after discounting the trajectory. Use: a translation invariant quadratic expression.
The second vector sequence is the discounted gradient, subsequently eliminated by the recurrence. -/
def certificateQuadratic (cert : StrictCertificate m t) (f σ : ℕ → E) (k : ℕ) : ℝ :=
  (∑ n ∈ cert.lags, 2 * Real.exp (-(n * t)) *
    (cert.α n * pairQuadratic 1 (f k) (Real.exp (n*t) • f (k+n))
      (σ k) (Real.exp (n*t) • σ (k+n)) +
    cert.β n * pairQuadratic (-1) (f k) (Real.exp (n*t) • f (k+n))
      (σ k) (Real.exp (n*t) • σ (k+n)))) +
    4 * cert.γplus * starQuadratic 1 (f k) (σ k) +
    4 * cert.γminus * starQuadratic (-1) (f k) (σ k)

/-- Article: H after discounting the sampled function values. -/
def certificateValue (cert : StrictCertificate m t) (h : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ n ∈ cert.lags, 2 * Real.exp (-(n*t)) * (cert.α n - cert.β n) *
    (Real.exp (2*n*t) * h (k+n) - h k)) +
    4 * (cert.γplus - cert.γminus) * h k

/-- Article: discounted signed slacks comprising Z.
Use: an exact expression before separating its quadratic and sampled-value parts. -/
def certificateSlack (cert : StrictCertificate m t)
    (f σ : ℕ → E) (h : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ n ∈ cert.lags, 2 * Real.exp (-(n*t)) *
    (cert.α n * (pairQuadratic 1 (f k) (Real.exp (n*t) • f (k+n))
      (σ k) (Real.exp (n*t) • σ (k+n)) +
        (Real.exp (2*n*t) * h (k+n) - h k)) +
     cert.β n * (pairQuadratic (-1) (f k) (Real.exp (n*t) • f (k+n))
      (σ k) (Real.exp (n*t) • σ (k+n)) -
        (Real.exp (2*n*t) * h (k+n) - h k)))) +
    4 * cert.γplus * (starQuadratic 1 (f k) (σ k) + h k) +
    4 * cert.γminus * (starQuadratic (-1) (f k) (σ k) - h k)

/-- Article: e^(-2kt) Z = Q + H. Proof: distribute the finite nonnegative combination. -/
theorem certificateSlack_eq (cert : StrictCertificate m t)
    (f σ : ℕ → E) (h : ℕ → ℝ) (k : ℕ) :
    certificateSlack cert f σ h k =
      certificateQuadratic cert f σ k + certificateValue cert h k := by
  unfold certificateSlack certificateQuadratic certificateValue
  have hs : (∑ n ∈ cert.lags, 2 * Real.exp (-(n*t)) *
      (cert.α n * (pairQuadratic 1 (f k) (Real.exp (n*t) • f (k+n))
        (σ k) (Real.exp (n*t) • σ (k+n)) +
          (Real.exp (2*n*t) * h (k+n) - h k)) +
       cert.β n * (pairQuadratic (-1) (f k) (Real.exp (n*t) • f (k+n))
        (σ k) (Real.exp (n*t) • σ (k+n)) -
          (Real.exp (2*n*t) * h (k+n) - h k)))) =
      (∑ n ∈ cert.lags, 2 * Real.exp (-(n*t)) *
        (cert.α n * pairQuadratic 1 (f k) (Real.exp (n*t) • f (k+n))
          (σ k) (Real.exp (n*t) • σ (k+n)) +
        cert.β n * pairQuadratic (-1) (f k) (Real.exp (n*t) • f (k+n))
          (σ k) (Real.exp (n*t) • σ (k+n)))) +
      (∑ n ∈ cert.lags, 2 * Real.exp (-(n*t)) * (cert.α n - cert.β n) *
        (Real.exp (2*n*t) * h (k+n) - h k)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hs]
  ring

/-- Article: every discounted interpolation slack is nonnegative, hence so is Z.
Use: a local theorem applicable directly to every actual segment.
Proof: all multipliers, including exponential weights, are nonnegative. -/
theorem certificateSlack_nonneg (cert : StrictCertificate m t)
    (f σ : ℕ → E) (h : ℕ → ℝ) (k : ℕ)
    (hp : ∀ n ∈ cert.lags,
      0 ≤ pairQuadratic 1 (f k) (Real.exp (n*t) • f (k+n))
        (σ k) (Real.exp (n*t) • σ (k+n)) +
          (Real.exp (2*n*t) * h (k+n) - h k))
    (hn : ∀ n ∈ cert.lags,
      0 ≤ pairQuadratic (-1) (f k) (Real.exp (n*t) • f (k+n))
        (σ k) (Real.exp (n*t) • σ (k+n)) -
          (Real.exp (2*n*t) * h (k+n) - h k))
    (hstarplus : 0 ≤ starQuadratic 1 (f k) (σ k) + h k)
    (hstarminus : 0 ≤ starQuadratic (-1) (f k) (σ k) - h k) :
    0 ≤ certificateSlack cert f σ h k := by
  unfold certificateSlack
  apply add_nonneg
  · apply add_nonneg
    · apply Finset.sum_nonneg
      intro n hn'
      exact mul_nonneg (by positivity) (add_nonneg
        (mul_nonneg (cert.α_nonneg n hn') (hp n hn'))
        (mul_nonneg (cert.β_nonneg n hn') (hn n hn')))
    · exact mul_nonneg (mul_nonneg (by norm_num) cert.γplus_nonneg) hstarplus
  · exact mul_nonneg (mul_nonneg (by norm_num) cert.γminus_nonneg) hstarminus

/-- Article: exponential algebra used by exact value cancellation. -/
theorem exp_neg_mul_exp_two (x : ℝ) :
    Real.exp (-x) * Real.exp (2*x) = Real.exp x := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- Article: the charge equation removes every unshifted value coefficient.
Use: all remaining value terms are differences of finite shifted sums, hence boundary terms.
Proof: exp(x)-exp(-x)=2 sinh(x) and the actual certificate charge, with no extra assumption. -/
theorem certificateValue_eq_differences (cert : StrictCertificate m t)
    (h : ℕ → ℝ) (k : ℕ) :
    certificateValue cert h k =
      ∑ n ∈ cert.lags, 2 * Real.exp (n*t) * (cert.α n - cert.β n) *
        (h (k+n) - h k) := by
  have heach (n : ℕ) :
      2 * Real.exp (-(n*t)) * (cert.α n - cert.β n) *
        (Real.exp (2*n*t) * h (k+n) - h k) =
      2 * Real.exp (n*t) * (cert.α n - cert.β n) * (h (k+n) - h k) +
      4 * h k * ((cert.α n - cert.β n) * Real.sinh (n*t)) := by
    have he := exp_neg_mul_exp_two (n*t)
    have hh : Real.exp (n*t) - Real.exp (-(n*t)) = 2 * Real.sinh (n*t) := by
      rw [Real.sinh_eq]
      ring
    rw [show 2 * (n : ℝ) * t = 2 * ((n : ℝ)*t) by ring]
    calc
      _ = 2 * (cert.α n - cert.β n) *
          ((Real.exp (-(n*t)) * Real.exp (2*(n*t))) * h (k+n) -
            Real.exp (-(n*t)) * h k) := by ring
      _ = _ := by
        rw [he]
        rw [show Real.sinh (n*t) =
          (Real.exp (n*t) - Real.exp (-(n*t))) / 2 by linarith [hh]]
        ring
  unfold certificateValue
  simp_rw [heach]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hc := congrArg (fun x : ℝ => 4 * h k * x) cert.cancel
  nlinarith [hc]

/-- Article: constant discounted values cancel identically.
Use: identifies the actual frequency symbol on exponential waves. -/
theorem certificateValue_const (cert : StrictCertificate m t) (h : ℝ) (k : ℕ) :
    certificateValue cert (fun _ => h) k = 0 := by
  rw [certificateValue_eq_differences]
  simp

/-- Article: value cancellation over an arbitrary finite set of center indices.
Use: the later interval argument concerns only the shifted boundary differences.
Proof: exchange two finite sums after pointwise charge cancellation. -/
theorem sum_certificateValue (cert : StrictCertificate m t) (h : ℕ → ℝ)
    (S : Finset ℕ) :
    (∑ k ∈ S, certificateValue cert h k) =
      ∑ n ∈ cert.lags, 2 * Real.exp (n*t) * (cert.α n - cert.β n) *
        ((∑ k ∈ S, h (k+n)) - ∑ k ∈ S, h k) := by
  simp_rw [certificateValue_eq_differences]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]

end polyak.Energy
