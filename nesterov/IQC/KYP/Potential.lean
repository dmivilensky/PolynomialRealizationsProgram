import nesterov.IQC.Certificate
import polyak.Energy.Values

/-!
Article: Proposition `lyap`, finite function-value correction.
Use: the actual certificate charge gives an exact finite telescoping
potential, with the source discount convention and explicit coefficients.
-/

namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators
variable {a : Spectral.SymbolPair} {t : ℝ}

theorem prefix_shift_difference (h : ℕ → ℝ) (k n : ℕ) :
    (∑ j ∈ Finset.range n, h (k + 1 + j)) - (∑ j ∈ Finset.range n, h (k + j)) =
      h (k + n) - h k := by
  have h1 := Finset.sum_range_succ (fun j => h (k + j)) n
  have h2 := Finset.sum_range_succ' (fun j => h (k + j)) n
  simp only [Nat.add_zero] at h2
  have he : (∑ j ∈ Finset.range n, h (k + (j + 1))) =
      ∑ j ∈ Finset.range n, h (k + 1 + j) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    omega
  rw [he] at h2
  linarith

/-- A finite boundary primitive of the discounted certificate's value part. -/
def valueBoundary (cert : Duality.StrictCertificate a t) (h : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ cert.lags, (2 * Real.exp (n * t) * (cert.α n - cert.β n)) *
    ∑ j ∈ Finset.range n, h (k + j)

theorem valueBoundary_difference (cert : Duality.StrictCertificate a t) (h : ℕ → ℝ) (k : ℕ) :
    valueBoundary cert h (k + 1) - valueBoundary cert h k =
      polyak.Energy.certificateValue (transported cert) h k := by
  rw [polyak.Energy.certificateValue_eq_differences]
  dsimp [valueBoundary]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← mul_sub, prefix_shift_difference]

def discountedValues (t : ℝ) (h : ℕ → ℝ) (k : ℕ) : ℝ :=
  Real.exp (-2 * (k : ℝ) * t) * h k

/-- The source function-value correction Ψ in undiscounted coordinates. -/
def sourcePotential (cert : Duality.StrictCertificate a t) (h : ℕ → ℝ) (k : ℕ) : ℝ :=
  Real.exp (2 * (k : ℝ) * t - 2 * t) * valueBoundary cert (discountedValues t h) k

/-- The actual, undiscounted value part of the certificate Z. -/
def sourceCertificateValue (cert : Duality.StrictCertificate a t) (h : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ n ∈ cert.lags, 2 * Real.exp (-(n * t)) * (cert.α n - cert.β n) *
    (h (k + n) - h k)) + 4 * (cert.γplus - cert.γminus) * h k

theorem sourceCertificateValue_eq_discounted (cert : Duality.StrictCertificate a t)
    (h : ℕ → ℝ) (k : ℕ) :
    sourceCertificateValue cert h k = Real.exp (2 * (k : ℝ) * t) *
      polyak.Energy.certificateValue (transported cert) (discountedValues t h) k := by
  have he0 : Real.exp (2 * (k : ℝ) * t) * Real.exp (-2 * (k : ℝ) * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have he (n : ℕ) : Real.exp (2 * (k : ℝ) * t) *
      (Real.exp (2 * (n : ℝ) * t) * discountedValues t h (k + n) - discountedValues t h k) =
      h (k + n) - h k := by
    have he1 : Real.exp (2 * (k : ℝ) * t) * Real.exp (2 * (n : ℝ) * t) *
        Real.exp (-2 * ((k + n : ℕ) : ℝ) * t) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      push_cast
      ring_nf
      exact Real.exp_zero
    dsimp [discountedValues]
    linear_combination h (k + n) * he1 - h k * he0
  unfold sourceCertificateValue polyak.Energy.certificateValue
  simp only [transported_lags, transported_α, transported_β, transported_γplus, transported_γminus]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro n _
    have hh := he n
    linear_combination -(2 * Real.exp (-(n * t)) * (cert.α n - cert.β n)) * hh
  · dsimp [discountedValues]
    linear_combination -(4 * (cert.γplus - cert.γminus) * h k) * he0

/-- The exact source telescoping identity Ψ(k+1)-r²Ψ(k)=H(k). -/
theorem sourcePotential_difference (cert : Duality.StrictCertificate a t) (h : ℕ → ℝ) (k : ℕ) :
    sourcePotential cert h (k + 1) - Real.exp (2 * t) * sourcePotential cert h k =
      sourceCertificateValue cert h k := by
  have he1 : Real.exp (2 * ((k + 1 : ℕ) : ℝ) * t - 2 * t) = Real.exp (2 * (k : ℝ) * t) := by
    congr 1
    push_cast
    ring
  have he2 : Real.exp (2 * t) * Real.exp (2 * (k : ℝ) * t - 2 * t) =
      Real.exp (2 * (k : ℝ) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [sourcePotential, sourcePotential, he1, ← mul_assoc, he2, ← mul_sub,
    valueBoundary_difference, sourceCertificateValue_eq_discounted]

/-- The finite double-sum coefficient formula, independent of time k. -/
theorem sourcePotential_eq_finite_sum (cert : Duality.StrictCertificate a t) (h : ℕ → ℝ) (k : ℕ) :
    sourcePotential cert h k = ∑ n ∈ cert.lags,
      (2 * Real.exp (n * t) * (cert.α n - cert.β n)) *
        ∑ j ∈ Finset.range n, Real.exp (-2 * ((j : ℝ) + 1) * t) * h (k + j) := by
  unfold sourcePotential valueBoundary
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : Real.exp (2 * (k : ℝ) * t - 2 * t) * Real.exp (-2 * ((k + j : ℕ) : ℝ) * t) =
      Real.exp (-2 * ((j : ℝ) + 1) * t) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  dsimp [discountedValues]
  linear_combination (2 * Real.exp (n * t) * (cert.α n - cert.β n) * h (k + j)) * he

def potentialHorizon (cert : Duality.StrictCertificate a t) : ℕ := cert.lags.sup id

/-- The exact coefficient b_j of the source potential's function values. -/
def potentialCoefficient (cert : Duality.StrictCertificate a t) (j : ℕ) : ℝ :=
  Real.exp (-2 * ((j : ℝ) + 1) * t) *
    ∑ n ∈ cert.lags, if j < n then 2 * Real.exp (n * t) * (cert.α n - cert.β n) else 0

theorem sourcePotential_eq_coefficients (cert : Duality.StrictCertificate a t) (h : ℕ → ℝ) (k : ℕ) :
    sourcePotential cert h k = ∑ j ∈ Finset.range (potentialHorizon cert),
      potentialCoefficient cert j * h (k + j) := by
  rw [sourcePotential_eq_finite_sum]
  have hexpand (n : ℕ) (hn : n ∈ cert.lags) :
      (2 * Real.exp (n * t) * (cert.α n - cert.β n)) *
        (∑ j ∈ Finset.range n, Real.exp (-2 * ((j : ℝ) + 1) * t) * h (k + j)) =
      ∑ j ∈ Finset.range (potentialHorizon cert), if j < n then
        (2 * Real.exp (n * t) * (cert.α n - cert.β n)) *
          (Real.exp (-2 * ((j : ℝ) + 1) * t) * h (k + j)) else 0 := by
    rw [Finset.mul_sum, ← Finset.sum_filter]
    have hnM : n ≤ potentialHorizon cert := Finset.le_sup (f := id) hn
    have heq : (Finset.range (potentialHorizon cert)).filter (fun j => j < n) = Finset.range n := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [heq]
  simp_rw [Finset.sum_congr rfl hexpand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [potentialCoefficient]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hj : j < n
  · simp only [ite_eq_left hj]
    ring
  · simp [hj]

def potentialBound (cert : Duality.StrictCertificate a t) : ℝ :=
  ∑ j ∈ Finset.range (potentialHorizon cert), |potentialCoefficient cert j| / 2

theorem potentialBound_nonneg (cert : Duality.StrictCertificate a t) : 0 ≤ potentialBound cert := by
  exact Finset.sum_nonneg fun j _ => div_nonneg (abs_nonneg _) (by norm_num)

/-- The correction is bounded by a fixed finite squared-norm window whenever
the genuine normalized objective satisfies |ψ(x)|≤‖x‖²/2. -/
theorem sourcePotential_bound (cert : Duality.StrictCertificate a t) {h b : ℕ → ℝ}
    (hb : ∀ i, 0 ≤ b i) (hh : ∀ i, |h i| ≤ b i / 2) (k : ℕ) :
    |sourcePotential cert h k| ≤ potentialBound cert *
      (∑ j ∈ Finset.range (potentialHorizon cert), b (k + j)) := by
  rw [sourcePotential_eq_coefficients]
  calc
    _ ≤ ∑ j ∈ Finset.range (potentialHorizon cert), |potentialCoefficient cert j * h (k + j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (potentialHorizon cert),
        (|potentialCoefficient cert j| / 2) *
          (∑ i ∈ Finset.range (potentialHorizon cert), b (k + i)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      have hsingle : b (k + j) ≤ ∑ i ∈ Finset.range (potentialHorizon cert), b (k + i) :=
        Finset.single_le_sum (fun i _ => hb (k + i)) hj
      have hh' := (hh (k + j)).trans (by linarith : b (k + j) / 2 ≤
        (∑ i ∈ Finset.range (potentialHorizon cert), b (k + i)) / 2)
      have hmul := mul_le_mul_of_nonneg_left hh' (abs_nonneg (potentialCoefficient cert j))
      nlinarith
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- A discounted dissipative storage whose discounted tail tends to zero is
nonnegative and quantitatively coercive.  No positivity of the storage is
assumed: it follows from the actual tail limit and the one-step inequality. -/
theorem storage_coercive_of_discounted_limit {V b : ℕ → ℝ} {q η : ℝ}
    (hq : 0 < q) (hη : 0 ≤ η) (hb : ∀ k, 0 ≤ b k)
    (hstep : ∀ k, V (k + 1) ≤ q * V k - η * b k)
    (hlim : Filter.Tendsto (fun k : ℕ => (q ^ k)⁻¹ * V k) Filter.atTop (nhds 0)) :
    (∀ k, 0 ≤ V k) ∧ ∀ k, (η / q) * b k ≤ V k := by
  let U := fun k : ℕ => (q ^ k)⁻¹ * V k
  have hmono : Antitone U := by
    apply antitone_nat_of_succ_le
    intro k
    have hs : V (k + 1) ≤ q * V k := by nlinarith [mul_nonneg hη (hb k), hstep k]
    have hp := mul_le_mul_of_nonneg_right hs (pow_pos hq k).le
    dsimp [U]
    simp only [inv_mul_eq_div]
    apply (div_le_div_iff₀ (pow_pos hq (k + 1)) (pow_pos hq k)).mpr
    rw [pow_succ]
    nlinarith
  have hU (k : ℕ) : 0 ≤ U k := by
    apply le_of_tendsto hlim
    filter_upwards [Filter.eventually_ge_atTop k] with n hn
    exact hmono hn
  have hV (k : ℕ) : 0 ≤ V k := by
    have hh := mul_nonneg (pow_pos hq k).le (hU k)
    simpa only [U, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero k (ne_of_gt hq)), one_mul] using hh
  refine ⟨hV, ?_⟩
  intro k
  have hh : η * b k ≤ q * V k := by linarith [hstep k, hV (k + 1)]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hq).mpr
  nlinarith

end
end nesterov.IQC.KYP
