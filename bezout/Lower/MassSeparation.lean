import bezout.Lower.MassCertificate

/-!
Article: bezout, Lemma C.1 (`lem:two-masses`).
Use: the signed mass inequality is proved by summing explicit supporting
quadratics and counting the two cones. Its lower bound is attained by equal
pure masses on disjoint supports of sizes `(N+1)/2` and `(N-1)/2`.
This proof is independent of positivity assumptions on the input profiles.
-/

namespace bezout.Lower

noncomputable section
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The two-support expression in the statement of Lemma C.1 is exactly
the cancelled parity-correction energy. -/
theorem mass_value_quotient (N : ℕ) (hN : 3 ≤ N) :
    evenMass N ^ 2 / (((N : ℝ) + 1) / 2) +
      oddMass N ^ 2 / (((N : ℝ) - 1) / 2) = oddEnergy N := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (N : ℝ) + 1 ≠ 0 := by positivity
  have hm : (N : ℝ) - 1 ≠ 0 := by linarith
  unfold evenMass oddMass oddEnergy
  field_simp
  ring

/-- Summation of the pointwise certificate retains the exact integer cone populations. -/
theorem sum_massEnergy_certificate (u v : ι → ℝ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 8 / 5 * a) (hab : a ≤ 5 / 4 * b) :
    2 * a * (∑ i, u i) + 2 * b * (∑ i, v i) -
      ((Finset.univ.filter fun i => 2 * v i ≤ u i).card : ℝ) * a ^ 2 -
      ((Finset.univ.filter fun i => ¬2 * v i ≤ u i).card : ℝ) * b ^ 2 ≤
      ∑ i, massEnergy (u i) (v i) := by
  classical
  have hp (i : ι) : 2 * a * u i + 2 * b * v i -
      (if 2 * v i ≤ u i then a ^ 2 else b ^ 2) ≤ massEnergy (u i) (v i) := by
    split_ifs with h
    · exact massEnergy_certificate_left a b _ _ ha hb hba hab h
    · exact massEnergy_certificate_right a b _ _ ha hb hba hab (le_of_not_ge h)
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ => hp i
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, sub_add_eq_sub_sub] using h

/-- Population arithmetic turns one close pair of rates into a lower bound
whenever the first cone contains at least the larger half of the positions. -/
theorem sum_massEnergy_lower_large_left (u v : ι → ℝ) (k : ℕ)
    (hcard : Fintype.card ι = 2 * k + 1) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 8 / 5 * a) (hab : a ≤ 5 / 4 * b)
    (hle : a ≤ b)
    (hpop : k + 1 ≤ (Finset.univ.filter fun i => 2 * v i ≤ u i).card) :
    2 * a * (∑ i, u i) + 2 * b * (∑ i, v i) -
      (k + 1 : ℕ) * a ^ 2 - (k : ℝ) * b ^ 2 ≤ ∑ i, massEnergy (u i) (v i) := by
  classical
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i => 2 * v i ≤ u i)
  simp only [Finset.card_univ, hcard] at hc
  have hcr : ((Finset.univ.filter fun i => 2 * v i ≤ u i).card : ℝ) +
      ((Finset.univ.filter fun i => ¬2 * v i ≤ u i).card : ℝ) = 2 * k + 1 := by
    exact_mod_cast hc
  have hpr : (k : ℝ) + 1 ≤ ((Finset.univ.filter fun i => 2 * v i ≤ u i).card : ℝ) := by
    exact_mod_cast hpop
  have hs := sum_massEnergy_certificate u v a b ha hb hba hab
  have hm := mul_nonneg (sub_nonneg.mpr hpr)
    (sub_nonneg.mpr (sq_le_sq₀ ha.le hb.le |>.mpr hle))
  push_cast
  nlinarith only [hs, hcr, hm]

/-- The complementary integer-population case uses rates in the opposite order. -/
theorem sum_massEnergy_lower_small_left (u v : ι → ℝ) (k : ℕ)
    (hcard : Fintype.card ι = 2 * k + 1) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 8 / 5 * a) (hab : a ≤ 5 / 4 * b)
    (hle : b ≤ a)
    (hpop : (Finset.univ.filter fun i => 2 * v i ≤ u i).card ≤ k) :
    2 * a * (∑ i, u i) + 2 * b * (∑ i, v i) -
      (k : ℝ) * a ^ 2 - (k + 1 : ℕ) * b ^ 2 ≤ ∑ i, massEnergy (u i) (v i) := by
  classical
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i => 2 * v i ≤ u i)
  simp only [Finset.card_univ, hcard] at hc
  have hcr : ((Finset.univ.filter fun i => 2 * v i ≤ u i).card : ℝ) +
      ((Finset.univ.filter fun i => ¬2 * v i ≤ u i).card : ℝ) = 2 * k + 1 := by
    exact_mod_cast hc
  have hpr : ((Finset.univ.filter fun i => 2 * v i ≤ u i).card : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hpop
  have hs := sum_massEnergy_certificate u v a b ha hb hba hab
  have hm := mul_nonneg (sub_nonneg.mpr hpr)
    (sub_nonneg.mpr (sq_le_sq₀ hb.le ha.le |>.mpr hle))
  push_cast
  nlinarith only [hs, hcr, hm]

/-- The equal pure masses on the larger and smaller supports have exactly
the squared corner energy printed in the article. -/
theorem pure_mass_value (k : ℕ) (hk : 0 < k) :
    evenMass (2 * k + 1) ^ 2 / ((k : ℝ) + 1) +
      oddMass (2 * k + 1) ^ 2 / (k : ℝ) = oddEnergy (2 * k + 1) := by
  have h : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hp : (k : ℝ) + 1 ≠ 0 := by positivity
  unfold evenMass oddMass oddEnergy
  push_cast
  field_simp
  ring

/-- The close rates for the larger-support population case. -/
theorem large_left_rates (k : ℕ) (hk : 1 ≤ k) :
    let a := (k : ℝ) + 1 / (2 * ((k : ℝ) + 1))
    let b := (k : ℝ) + 1
    0 < a ∧ 0 < b ∧ b ≤ 8 / 5 * a ∧ a ≤ 5 / 4 * b ∧ a ≤ b := by
  dsimp
  have hr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : 0 < 2 * ((k : ℝ) + 1) := by positivity
  have hq : 0 ≤ 1 / (2 * ((k : ℝ) + 1)) := by positivity
  have hq' : 1 / (2 * ((k : ℝ) + 1)) ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hab : (k : ℝ) + 1 / (2 * ((k : ℝ) + 1)) ≤ (k : ℝ) + 1 := by linarith
  refine ⟨by positivity, by positivity, ?_, by linarith, hab⟩
  by_cases h1 : k = 1
  · subst k
    norm_num
  · have hk2 : 2 ≤ k := by omega
    have hr2 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    linarith

/-- Substitution of the larger-support rates evaluates the dual bound exactly. -/
theorem large_left_rate_value (k : ℕ) (hk : 0 < k) :
    let a := (k : ℝ) + 1 / (2 * ((k : ℝ) + 1))
    let b := (k : ℝ) + 1
    2 * a * evenMass (2 * k + 1) + 2 * b * oddMass (2 * k + 1) -
      ((k : ℝ) + 1) * a ^ 2 - (k : ℝ) * b ^ 2 = oddEnergy (2 * k + 1) := by
  dsimp
  have hp : (k : ℝ) + 1 ≠ 0 := by positivity
  unfold evenMass oddMass oddEnergy
  push_cast
  field_simp
  ring

/-- The reversed-support rates are also close after the first four odd horizons. -/
theorem small_left_rates (k : ℕ) (hk : 5 ≤ k) :
    let a := (k : ℝ) + 1 + 1 / (2 * (k : ℝ))
    let b := (k : ℝ)
    0 < a ∧ 0 < b ∧ b ≤ 8 / 5 * a ∧ a ≤ 5 / 4 * b ∧ b ≤ a := by
  dsimp
  have hr : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (0 : ℝ) < k := by linarith
  have hq : 0 ≤ 1 / (2 * (k : ℝ)) := by positivity
  have hq' : 1 / (2 * (k : ℝ)) ≤ 1 / 10 := by
    apply (div_le_iff₀ (show 0 < 2 * (k : ℝ) by positivity)).mpr
    linarith
  exact ⟨by positivity, hp, by linarith, by linarith, by linarith⟩

/-- The reversed-support certificate exceeds the target by an explicit
positive rational term. -/
theorem small_left_rate_value (k : ℕ) (hk : 0 < k) :
    let a := (k : ℝ) + 1 + 1 / (2 * (k : ℝ))
    let b := (k : ℝ)
    2 * a * evenMass (2 * k + 1) + 2 * b * oddMass (2 * k + 1) -
      (k : ℝ) * a ^ 2 - ((k : ℝ) + 1) * b ^ 2 =
      oddEnergy (2 * k + 1) + (2 * (k : ℝ) + 1) ^ 2 /
        (4 * (k : ℝ) * ((k : ℝ) + 1)) := by
  dsimp
  have h : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hp : (k : ℝ) + 1 ≠ 0 := by positivity
  unfold evenMass oddMass oddEnergy
  push_cast
  field_simp
  ring

/-- The four small odd horizons use one fixed rate ratio; only scalar
rational arithmetic is needed, independently of the temporal dimension. -/
theorem sum_massEnergy_small_horizon (u v : ι → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hk4 : k ≤ 4) (hcard : Fintype.card ι = 2 * k + 1)
    (hu : ∑ i, u i = evenMass (2 * k + 1))
    (hv : ∑ i, v i = oddMass (2 * k + 1))
    (hpop : (Finset.univ.filter fun i => 2 * v i ≤ u i).card ≤ k) :
    oddEnergy (2 * k + 1) ≤ ∑ i, massEnergy (u i) (v i) := by
  let t : ℝ := ((5 / 4 : ℝ) * evenMass (2 * k + 1) + oddMass (2 * k + 1)) /
    ((25 / 16 : ℝ) * k + (k + 1 : ℕ))
  have ht := sum_massEnergy_lower_small_left u v k hcard ((5 / 4 : ℝ) * t) t
    (by dsimp only [t]; interval_cases k <;> norm_num [evenMass, oddMass])
    (by dsimp only [t]; interval_cases k <;> norm_num [evenMass, oddMass])
    (by dsimp only [t]; interval_cases k <;> norm_num [evenMass, oddMass])
    (by dsimp only [t]; interval_cases k <;> norm_num [evenMass, oddMass])
    (by dsimp only [t]; interval_cases k <;> norm_num [evenMass, oddMass]) hpop
  rw [hu, hv] at ht
  have hvalue : oddEnergy (2 * k + 1) ≤
      2 * ((5 / 4 : ℝ) * t) * evenMass (2 * k + 1) +
        2 * t * oddMass (2 * k + 1) - (k : ℝ) * ((5 / 4 : ℝ) * t) ^ 2 -
          (k + 1 : ℕ) * t ^ 2 := by
    dsimp only [t]
    interval_cases k <;> norm_num [evenMass, oddMass, oddEnergy]
  exact hvalue.trans ht

/-- The signed two-mass inequality for every odd finite population. The
proof uses an explicit pointwise certificate and the integer cone count. -/
theorem signed_mass_separation_bit1 (u v : ι → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hcard : Fintype.card ι = 2 * k + 1)
    (hu : ∑ i, u i = evenMass (2 * k + 1))
    (hv : ∑ i, v i = oddMass (2 * k + 1)) :
    oddEnergy (2 * k + 1) ≤ ∑ i, massEnergy (u i) (v i) := by
  classical
  by_cases hpop : k + 1 ≤ (Finset.univ.filter fun i => 2 * v i ≤ u i).card
  · obtain ⟨ha, hb, hba, hab, hle⟩ := large_left_rates k hk
    have h := sum_massEnergy_lower_large_left u v k hcard _ _ ha hb hba hab hle hpop
    rw [hu, hv] at h
    simpa only [Nat.cast_add, Nat.cast_one,
      large_left_rate_value k (by omega)] using h
  · have hpop' : (Finset.univ.filter fun i => 2 * v i ≤ u i).card ≤ k := by omega
    by_cases hk5 : 5 ≤ k
    · obtain ⟨ha, hb, hba, hab, hle⟩ := small_left_rates k hk5
      have h := sum_massEnergy_lower_small_left u v k hcard _ _ ha hb hba hab hle hpop'
      rw [hu, hv] at h
      simp only [Nat.cast_add, Nat.cast_one, small_left_rate_value k (by omega)] at h
      have hp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hnonneg : 0 ≤ (2 * (k : ℝ) + 1) ^ 2 /
          (4 * (k : ℝ) * ((k : ℝ) + 1)) := by positivity
      linarith
    · exact sum_massEnergy_small_horizon u v k hk (by omega) hcard hu hv hpop'

/-- The signed form of the article's mass inequality, stated in its original
odd-horizon variable and for an arbitrary finite temporal index type. -/
theorem signed_mass_separation (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (hcard : Fintype.card ι = N) (u v : ι → ℝ)
    (hu : ∑ i, u i = evenMass N) (hv : ∑ i, v i = oddMass N) :
    oddEnergy N ≤ ∑ i, massEnergy (u i) (v i) := by
  obtain ⟨k, rfl⟩ := hodd.exists_bit1
  exact signed_mass_separation_bit1 u v k (by omega) hcard hu hv

/-- The nonnegative form is a direct specialization of the signed theorem. -/
theorem nonnegative_mass_separation (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (hcard : Fintype.card ι = N) (u v : ι → ℝ)
    (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i)
    (hu : ∑ i, u i = evenMass N) (hv : ∑ i, v i = oddMass N) :
    oddEnergy N ≤ ∑ i, ((u i) ^ 2 + (v i) ^ 2 + 4 * u i * v i) := by
  simpa only [massEnergy_of_mul_nonneg (mul_nonneg (hu0 _) (hv0 _))] using
    signed_mass_separation N hN hodd hcard u v hu hv

/-- Equal pure masses on any partition of the required sizes attain the
bound. This gives an actual optimizer, not merely a lower value. -/
theorem exists_pure_mass_attainment (k : ℕ) (hk : 1 ≤ k)
    (hcard : Fintype.card ι = 2 * k + 1) :
    ∃ u v : ι → ℝ,
      (∑ i, u i = evenMass (2 * k + 1)) ∧
      (∑ i, v i = oddMass (2 * k + 1)) ∧
      (∀ i, 0 ≤ u i ∧ 0 ≤ v i ∧ u i * v i = 0) ∧
      (∑ i, massEnergy (u i) (v i)) = oddEnergy (2 * k + 1) := by
  classical
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (show k + 1 ≤ (Finset.univ : Finset ι).card by simpa [hcard] using (by omega : k + 1 ≤ 2 * k + 1))
  have hSc : Sᶜ.card = k := by rw [Finset.card_compl, hcard, hS]; omega
  let a := evenMass (2 * k + 1) / ((k : ℝ) + 1)
  let b := oddMass (2 * k + 1) / (k : ℝ)
  let u : ι → ℝ := fun i => if i ∈ S then a else 0
  let v : ι → ℝ := fun i => if i ∈ Sᶜ then b else 0
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ha : 0 ≤ a := by dsimp [a, evenMass]; positivity
  have hb : 0 ≤ b := by
    dsimp [b, oddMass]
    have hr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast
    apply div_nonneg _ hkp.le
    nlinarith
  have hu : (∑ i, u i) = evenMass (2 * k + 1) := by
    simp only [u]
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, hS]
    dsimp [a]
    push_cast
    field_simp
  have hv : (∑ i, v i) = oddMass (2 * k + 1) := by
    simp only [v]
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, hSc]
    dsimp [b]
    field_simp
  have hpure (i : ι) : 0 ≤ u i ∧ 0 ≤ v i ∧ u i * v i = 0 := by
    by_cases hi : i ∈ S
    · simp [u, v, hi, ha]
    · simp [u, v, hi, hb]
  have hnot : (Finset.univ.filter fun i => ¬ i ∈ S) = Sᶜ := by ext i; simp
  have he : (∑ i, massEnergy (u i) (v i)) = (k + 1 : ℕ) * a ^ 2 + (k : ℝ) * b ^ 2 := by
    have heq (i : ι) : massEnergy (u i) (v i) = if i ∈ S then a ^ 2 else b ^ 2 := by
      by_cases hi : i ∈ S <;> simp [massEnergy, u, v, hi]
    simp_rw [heq]
    rw [Finset.sum_ite]
    simp [hnot, hS, hSc]
  refine ⟨u, v, hu, hv, hpure, he.trans ?_⟩
  rw [← pure_mass_value k (by omega)]
  dsimp [a, b]
  push_cast
  field_simp

/-- The signed energy values have the exact attained minimum stated in
Lemma C.1. -/
theorem signed_mass_minimum (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (hcard : Fintype.card ι = N) :
    IsLeast {E : ℝ | ∃ u v : ι → ℝ,
      (∑ i, u i = evenMass N) ∧ (∑ i, v i = oddMass N) ∧
        E = ∑ i, massEnergy (u i) (v i)} (oddEnergy N) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨k, rfl⟩ := hodd.exists_bit1
    obtain ⟨u, v, hu, hv, _, he⟩ := exists_pure_mass_attainment k (by omega) hcard
    exact ⟨u, v, hu, hv, he.symm⟩
  · rintro E ⟨u, v, hu, hv, rfl⟩
    exact signed_mass_separation N hN hodd hcard u v hu hv

/-- The same attained minimum holds for the nonnegative polynomial energy. -/
theorem nonnegative_mass_minimum (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (hcard : Fintype.card ι = N) :
    IsLeast {E : ℝ | ∃ u v : ι → ℝ,
      (∀ i, 0 ≤ u i) ∧ (∀ i, 0 ≤ v i) ∧
      (∑ i, u i = evenMass N) ∧ (∑ i, v i = oddMass N) ∧
        E = ∑ i, ((u i) ^ 2 + (v i) ^ 2 + 4 * u i * v i)} (oddEnergy N) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨k, rfl⟩ := hodd.exists_bit1
    obtain ⟨u, v, hu, hv, hp, he⟩ := exists_pure_mass_attainment k (by omega) hcard
    refine ⟨u, v, fun i => (hp i).1, fun i => (hp i).2.1, hu, hv, ?_⟩
    rw [← he]
    apply Finset.sum_congr rfl
    intro i _
    exact massEnergy_of_mul_nonneg (mul_nonneg (hp i).1 (hp i).2.1)
  · rintro E ⟨u, v, hu0, hv0, hu, hv, rfl⟩
    exact nonnegative_mass_separation N hN hodd hcard u v hu0 hv0 hu hv

end
end bezout.Lower
