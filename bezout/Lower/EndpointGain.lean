import bezout.Lower.PhysicalCorners

/-!
Article: bezout, Theorem 4.1 (`eq:linear-lower`).
Use: the exact parity-corrected lower bound is already forced by one of
the four physical spectral endpoint pairs. Even horizons use scalar
Cauchy--Schwarz; odd horizons use the sign-unrestricted four-corner bound.
No memory or coefficient-sign restriction is imposed on the history.
-/

namespace bezout.Lower

noncomputable section
open scoped BigOperators

/-- The exact squared parity correction, equal to one at even horizons. -/
def linearCorrectionSq (N : ℕ) : ℝ := if Odd N then oddCorrectionSq N else 1

/-- The article's sharp lower gain `D_N / sqrt N * sigma_N`. -/
def linearGain (I : chebyshev1.SpectralInterval) (N : ℕ) : ℝ :=
  derivativeScale I N / Real.sqrt N * Real.sqrt (linearCorrectionSq N)

/-- The maximum physical energy among the four spectral endpoint pairs. -/
def endpointEnergyMax {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) : ℝ :=
  max (max (physicalKernelSq h I.mu I.mu) (physicalKernelSq h I.mu I.L))
      (max (physicalKernelSq h I.L I.mu) (physicalKernelSq h I.L I.L))

/-- The squared correction is nonnegative on the article's horizon domain. -/
theorem linearCorrectionSq_nonneg {N : ℕ} (hN : 2 ≤ N) : 0 ≤ linearCorrectionSq N := by
  unfold linearCorrectionSq oddCorrectionSq
  split_ifs
  · have hr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hs : 0 ≤ (N : ℝ) - 1 := by linarith
    have ht : 0 ≤ ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) :=
      div_nonneg hs (by positivity)
    linarith
  · norm_num

/-- All factors in the sharp lower gain have their intended nonnegative signs. -/
theorem linearGain_nonneg (I : chebyshev1.SpectralInterval) (N : ℕ) :
    0 ≤ linearGain I N := by
  have he : 0 < I.epsilon N := one_div_pos.mpr (I.den_pos N)
  have hD : 0 < I.delta := I.delta_pos
  unfold linearGain derivativeScale
  positivity

/-- Squaring the normalized gain recovers the original derivative scale. -/
theorem linearGain_sq (I : chebyshev1.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    linearGain I N ^ 2 = derivativeScale I N ^ 2 / (N : ℝ) * linearCorrectionSq N := by
  unfold linearGain
  rw [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg N),
    Real.sq_sqrt (linearCorrectionSq_nonneg hN)]

/-- The odd scaled corner energy is exactly the square of the sharp physical gain. -/
theorem linearGain_sq_odd (I : chebyshev1.SpectralInterval) {N : ℕ}
    (hN : 3 ≤ N) (hodd : Odd N) :
    linearGain I N ^ 2 = (4 * I.epsilon N / I.delta) ^ 2 * oddEnergy N := by
  rw [linearGain_sq I (by omega)]
  simp only [linearCorrectionSq, hodd, ite_true]
  rw [oddEnergy_eq_correction (by omega : 0 < N)]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold derivativeScale
  field_simp
  ring

/-- Each fixed-pair kernel energy is nonnegative. -/
theorem physicalKernelSq_nonneg {N : ℕ} (h : bezout.History N) (x y : ℝ) :
    0 ≤ physicalKernelSq h x y := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The endpoint maximum is nonnegative. -/
theorem endpointEnergyMax_nonneg {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) : 0 ≤ endpointEnergyMax h I :=
  (physicalKernelSq_nonneg h I.mu I.mu).trans
    ((le_max_left _ _).trans (le_max_left _ _))

/-- The physical weighted corner energy cannot exceed the largest corner. -/
theorem physical_four_corner_le_max {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) :
    fourCornerEnergy
      (fun s => (h.response s).eval I.mu) (fun s => (h.response s).eval I.L)
      (fun s => (h.query s).eval I.mu) (fun s => (h.query s).eval I.L) ≤
      endpointEnergyMax h I := by
  have hpp : physicalKernelSq h I.mu I.mu ≤ endpointEnergyMax h I :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hpm : physicalKernelSq h I.mu I.L ≤ endpointEnergyMax h I :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hmp : physicalKernelSq h I.L I.mu ≤ endpointEnergyMax h I :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hmm : physicalKernelSq h I.L I.L ≤ endpointEnergyMax h I :=
    (le_max_right _ _).trans (le_max_right _ _)
  have heq : fourCornerEnergy
      (fun s => (h.response s).eval I.mu) (fun s => (h.response s).eval I.L)
      (fun s => (h.query s).eval I.mu) (fun s => (h.query s).eval I.L) =
      3 / 8 * (physicalKernelSq h I.mu I.mu + physicalKernelSq h I.L I.L) +
        1 / 8 * (physicalKernelSq h I.mu I.L + physicalKernelSq h I.L I.mu) := by
    unfold fourCornerEnergy physicalKernelSq physicalKernel
    simp only [Finset.sum_add_distrib]
  rw [heq]
  linarith

/-- The scalar endpoint identity gives the basic lower energy at every horizon. -/
theorem scalar_endpoint_lower {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 0 < N) :
    derivativeScale I N ^ 2 / (N : ℝ) ≤ physicalKernelSq h I.mu I.mu := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
    (fun _ => (1 : ℝ)) (fun s => physicalKernel h s I.mu I.mu)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hc
  rw [kernel_sum_mu h I he] at hc
  simp only [neg_sq] at hc
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  exact (div_le_iff₀ hp).mpr (by simpa only [physicalKernelSq, mul_comm] using hc)

/-- The exact squared lower gain is forced by the endpoint maximum, in both parities. -/
theorem linearGain_sq_le_endpointEnergyMax {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 2 ≤ N) :
    linearGain I N ^ 2 ≤ endpointEnergyMax h I := by
  by_cases hodd : Odd N
  · have hN3 : 3 ≤ N := by
      have hm := Nat.odd_iff.mp hodd
      omega
    rw [linearGain_sq_odd I hN3 hodd]
    exact (history_physical_four_corner_lower h I he hN3 hodd).trans
      (physical_four_corner_le_max h I)
  · rw [linearGain_sq I hN]
    simp only [linearCorrectionSq, hodd, ite_false, mul_one]
    exact (scalar_endpoint_lower h I he (by omega)).trans
      ((le_max_left _ _).trans (le_max_left _ _))

/-- The exact universal endpoint norm lower bound, with the article's sigma_N. -/
theorem linearGain_le_endpointGain {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 2 ≤ N) :
    linearGain I N ≤ Real.sqrt (endpointEnergyMax h I) := by
  apply (sq_le_sq₀ (linearGain_nonneg I N) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (endpointEnergyMax_nonneg h I)]
  exact linearGain_sq_le_endpointEnergyMax h I he hN

/-- One of the four actual spectral corners realizes the finite maximum. -/
theorem endpointEnergyMax_attained {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) :
    ∃ x y : ℝ, (x = I.mu ∨ x = I.L) ∧ (y = I.mu ∨ y = I.L) ∧
      physicalKernelSq h x y = endpointEnergyMax h I := by
  rcases max_choice
      (max (physicalKernelSq h I.mu I.mu) (physicalKernelSq h I.mu I.L))
      (max (physicalKernelSq h I.L I.mu) (physicalKernelSq h I.L I.L)) with ho | ho
  · rcases max_choice (physicalKernelSq h I.mu I.mu) (physicalKernelSq h I.mu I.L) with hi | hi
    · exact ⟨I.mu, I.mu, Or.inl rfl, Or.inl rfl, (ho.trans hi).symm⟩
    · exact ⟨I.mu, I.L, Or.inl rfl, Or.inr rfl, (ho.trans hi).symm⟩
  · rcases max_choice (physicalKernelSq h I.L I.mu) (physicalKernelSq h I.L I.L) with hi | hi
    · exact ⟨I.L, I.mu, Or.inr rfl, Or.inl rfl, (ho.trans hi).symm⟩
    · exact ⟨I.L, I.L, Or.inr rfl, Or.inr rfl, (ho.trans hi).symm⟩

/-- Every unrestricted Chebyshev-exact history has an actual endpoint pair
whose temporal insertion norm is at least the sharp parity-corrected gain. -/
theorem exists_endpoint_gain_lower {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 2 ≤ N) :
    ∃ x y : ℝ, (x = I.mu ∨ x = I.L) ∧ (y = I.mu ∨ y = I.L) ∧
      linearGain I N ≤ Real.sqrt (physicalKernelSq h x y) := by
  obtain ⟨x, y, hx, hy, heq⟩ := endpointEnergyMax_attained h I
  exact ⟨x, y, hx, hy, heq ▸ linearGain_le_endpointGain h I he hN⟩

/-- The endpoint witness is in the admissible closed spectral interval. -/
theorem exists_spectral_pair_gain_lower {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 2 ≤ N) :
    ∃ x ∈ Set.Icc I.mu I.L, ∃ y ∈ Set.Icc I.mu I.L,
      linearGain I N ≤ Real.sqrt (physicalKernelSq h x y) := by
  obtain ⟨x, y, hx, hy, hg⟩ := exists_endpoint_gain_lower h I he hN
  have hxI : x ∈ Set.Icc I.mu I.L := by
    rcases hx with rfl | rfl <;> exact ⟨by linarith [I.mu_lt_L], by linarith [I.mu_lt_L]⟩
  have hyI : y ∈ Set.Icc I.mu I.L := by
    rcases hy with rfl | rfl <;> exact ⟨by linarith [I.mu_lt_L], by linarith [I.mu_lt_L]⟩
  exact ⟨x, hxI, y, hyI, hg⟩

/-- Any uniform spectral insertion-norm bound for an unrestricted exact
history is at least the article's sharp constant. -/
theorem uniform_spectral_bound_ge_linearGain {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 2 ≤ N)
    (M : ℝ) (hM : ∀ x ∈ Set.Icc I.mu I.L, ∀ y ∈ Set.Icc I.mu I.L,
      Real.sqrt (physicalKernelSq h x y) ≤ M) : linearGain I N ≤ M := by
  obtain ⟨x, hx, y, hy, hg⟩ := exists_spectral_pair_gain_lower h I he hN
  exact hg.trans (hM x hx y hy)

/-- The stronger symmetric weighted physical inequality has the same sharp
constant; this is the form used for symmetric Hilbert--Schmidt budgets. -/
theorem linearGain_sq_le_symmetric_four_corners {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I)
    (hN : 3 ≤ N) (hodd : Odd N) :
    linearGain I N ^ 2 ≤ symmetricCornerEnergy
      (fun s => (h.response s).eval I.mu) (fun s => (h.response s).eval I.L)
      (fun s => (h.query s).eval I.mu) (fun s => (h.query s).eval I.L) := by
  rw [linearGain_sq_odd I hN hodd]
  exact history_physical_symmetric_four_corner_lower h I he hN hodd

end
end bezout.Lower
