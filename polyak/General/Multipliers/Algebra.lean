import polyak.General.Factor
import polyak.Duality.Certificate
import polyak.Waves.Dynamics

/-! Appendix D, Lemma symbols: the actual finite polynomial and the two
charge-cancelling one-sided weights. -/

namespace polyak.General.Multipliers
noncomputable section
open scoped BigOperators

def polynomial (s : Finset ℕ) (lam : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ s, (lam n : ℂ) * (1-z^n)

@[simp] theorem polynomial_one (s : Finset ℕ) (lam : ℕ → ℝ) : polynomial s lam 1 = 0 := by
  simp [polynomial]

theorem polynomial_zero (s : Finset ℕ) (lam : ℕ → ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) : polynomial s lam 0 = (∑ n ∈ s, lam n : ℝ) := by
  simp only [polynomial, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp [Nat.ne_of_gt (hs n hn)]

theorem differentiable_polynomial (s : Finset ℕ) (lam : ℕ → ℝ) :
    Differentiable ℂ (polynomial s lam) := by
  unfold polynomial
  fun_prop

def aSharp (q : Tuning) (u : ℂ) : ℂ :=
  1 - (1 + q.beta - q.x : ℝ) * u + q.beta * u^2
def bSharp (q : Tuning) (u : ℂ) : ℂ :=
  1 - (1 + q.beta - q.y : ℝ) * u + q.beta * u^2

@[simp] theorem aSharp_zero (q : Tuning) : aSharp q 0 = 1 := by simp [aSharp]
@[simp] theorem bSharp_zero (q : Tuning) : bSharp q 0 = 1 := by simp [bSharp]

theorem aSharp_reversed (q : Tuning) {u : ℂ} (hu : u ≠ 0) :
    aSharp q u = u^2 * q.a u⁻¹ := by
  unfold aSharp Tuning.a
  field_simp
theorem bSharp_reversed (q : Tuning) {u : ℂ} (hu : u ≠ 0) :
    bSharp q u = u^2 * q.b u⁻¹ := by
  unfold bSharp Tuning.b
  field_simp

theorem aSharp_ne_zero (q : Tuning) {u : ℂ} (hu : ‖u‖ ≤ 1) : aSharp q u ≠ 0 := by
  by_cases hz : u = 0
  · simp [hz]
  rw [aSharp_reversed q hz]
  apply mul_ne_zero (pow_ne_zero _ hz)
  apply q.a_ne_zero_of_one_le_norm
  rw [norm_inv]
  exact (one_le_inv₀ (norm_pos_iff.mpr hz)).2 hu

theorem bSharp_ne_zero (q : Tuning) {u : ℂ} (hu : ‖u‖ ≤ 1) : bSharp q u ≠ 0 := by
  by_cases hz : u = 0
  · simp [hz]
  rw [bSharp_reversed q hz]
  apply mul_ne_zero (pow_ne_zero _ hz)
  apply q.b_ne_zero_of_one_le_norm
  rw [norm_inv]
  exact (one_le_inv₀ (norm_pos_iff.mpr hz)).2 hu

theorem continuousOn_sharpRatio (q : Tuning) :
    ContinuousOn (fun u => bSharp q u / aSharp q u) (Metric.closedBall 0 1) := by
  apply ContinuousOn.div
  · unfold bSharp; fun_prop
  · unfold aSharp; fun_prop
  · intro u hu
    exact aSharp_ne_zero q (by simpa using hu)

theorem differentiableOn_sharpRatio (q : Tuning) :
    DifferentiableOn ℂ (fun u => bSharp q u / aSharp q u) (Metric.ball 0 1) := by
  apply DifferentiableOn.div
  · unfold bSharp; fun_prop
  · unfold aSharp; fun_prop
  · intro u hu
    exact aSharp_ne_zero q (le_of_lt (by simpa using hu))

theorem sharp_ratio_circle (q : Tuning) {u : ℂ} (hu : ‖u‖ = 1) :
    bSharp q u / aSharp q u =
      ((Complex.normSq (q.b u) / Complex.normSq (q.a u) : ℝ) : ℂ) * (q.a u/q.b u) := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (hu.trans_ne one_ne_zero)
  have hnorm : Complex.normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, hu]; norm_num
  have hinv : u⁻¹ = star u := by rw [Complex.inv_def, hnorm]; simp
  have hac : q.a (star u) = star (q.a u) := by simp [Tuning.a]
  have hbc : q.b (star u) = star (q.b u) := by simp [Tuning.b]
  have ha := q.a_ne_zero_of_one_le_norm hu.ge
  have hb := q.b_ne_zero_of_one_le_norm hu.ge
  rw [aSharp_reversed q hu0, bSharp_reversed q hu0, hinv, hac, hbc]
  push_cast
  rw [show (Complex.normSq (q.b u) : ℂ) = q.b u * star (q.b u) from (Complex.mul_conj _).symm,
    show (Complex.normSq (q.a u) : ℂ) = q.a u * star (q.a u) from (Complex.mul_conj _).symm]
  field_simp

theorem sharp_ratio_re_circle (q : Tuning) {u : ℂ} (hu : ‖u‖ = 1) (M : ℂ) :
    (M*bSharp q u/aSharp q u).re =
      (Complex.normSq (q.b u)/Complex.normSq (q.a u))*(M*q.a u/q.b u).re := by
  have he : M*bSharp q u/aSharp q u =
      ((Complex.normSq (q.b u)/Complex.normSq (q.a u) : ℝ):ℂ)*(M*q.a u/q.b u) := by
    rw [mul_div_assoc, sharp_ratio_circle q hu]
    ring
  rw [he, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem upper_sharp_ratio_circle (q : Tuning) {u : ℂ} (hu : ‖u‖ = 1) :
    aSharp q u / bSharp q u =
      ((Complex.normSq (q.a u) / Complex.normSq (q.b u) : ℝ) : ℂ) * (q.b u/q.a u) := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (hu.trans_ne one_ne_zero)
  have hnorm : Complex.normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, hu]; norm_num
  have hinv : u⁻¹ = star u := by rw [Complex.inv_def, hnorm]; simp
  have hac : q.b (star u) = star (q.b u) := by simp [Tuning.b]
  have hbc : q.a (star u) = star (q.a u) := by simp [Tuning.a]
  have ha := q.b_ne_zero_of_one_le_norm hu.ge
  have hb := q.a_ne_zero_of_one_le_norm hu.ge
  rw [bSharp_reversed q hu0, aSharp_reversed q hu0, hinv, hac, hbc]
  push_cast
  rw [show (Complex.normSq (q.a u) : ℂ) = q.a u * star (q.a u) from (Complex.mul_conj _).symm,
    show (Complex.normSq (q.b u) : ℂ) = q.b u * star (q.b u) from (Complex.mul_conj _).symm]
  field_simp

theorem upper_sharp_ratio_re_circle (q : Tuning) {u : ℂ} (hu : ‖u‖ = 1) (M : ℂ) :
    (M*aSharp q u/bSharp q u).re =
      (Complex.normSq (q.a u)/Complex.normSq (q.b u))*(M*q.b u/q.a u).re := by
  have he : M*aSharp q u/bSharp q u =
      ((Complex.normSq (q.a u)/Complex.normSq (q.b u) : ℝ):ℂ)*(M*q.b u/q.a u) := by
    rw [mul_div_assoc, upper_sharp_ratio_circle q hu]
    ring
  rw [he, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The finite C coefficient vanishes exactly, without any sign hypothesis. -/
theorem lower_cancel_positive (s : Finset ℕ) (lam : ℕ → ℝ) (t : ℝ) :
    (∑ n ∈ s, (lam n * Real.exp (-(n*t)) - 0) * Real.sinh (n*t)) + 0 -
      (∑ n ∈ s, lam n * Real.exp (-(n*t)) * Real.sinh (n*t)) = 0 := by simp

theorem lower_cancel_negative (s : Finset ℕ) (lam : ℕ → ℝ) (t : ℝ) :
    (∑ n ∈ s, (lam n * Real.exp (n*t) - 0) * Real.sinh (n*t)) +
      (-(∑ n ∈ s, lam n * Real.exp (n*t) * Real.sinh (n*t))) - 0 = 0 := by simp

theorem upper_cancel_positive (s : Finset ℕ) (lam : ℕ → ℝ) (t : ℝ) :
    (∑ n ∈ s, (0 - lam n * Real.exp (-(n*t))) * Real.sinh (n*t)) +
      (∑ n ∈ s, lam n * Real.exp (-(n*t)) * Real.sinh (n*t)) - 0 = 0 := by
  simp [Finset.sum_neg_distrib]

theorem upper_cancel_negative (s : Finset ℕ) (lam : ℕ → ℝ) (t : ℝ) :
    (∑ n ∈ s, (0 - lam n * Real.exp (n*t)) * Real.sinh (n*t)) + 0 -
      (-(∑ n ∈ s, lam n * Real.exp (n*t) * Real.sinh (n*t))) = 0 := by
  simp [Finset.sum_neg_distrib]

theorem factor_re_lower (q : Tuning) {z : ℂ} (hz : z ≠ 0) (hb : q.b z ≠ 0)
    (M : ℂ) :
    (((1-q.m z)*(1+star (q.m z)))*M).re =
      -(Complex.normSq (q.b z) / (q.B^2 * Complex.normSq z)) * (M*q.a z/q.b z).re := by
  have he : ((1-q.m z)*(1+star (q.m z)))*M =
      -((Complex.normSq (q.b z) / (q.B^2 * Complex.normSq z) : ℝ) : ℂ) *
        (M*q.a z/q.b z) := by
    rw [q.factor hz]
    push_cast
    rw [show (Complex.normSq (q.b z) : ℂ) = q.b z * star (q.b z) by
      exact (Complex.mul_conj (q.b z)).symm]
    field_simp
  rw [he]
  rw [Complex.mul_re]
  simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    neg_zero, zero_mul, sub_zero]

theorem factor_re_upper (q : Tuning) {z : ℂ} (hz : z ≠ 0) (ha : q.a z ≠ 0)
    (M : ℂ) :
    ((star ((1-q.m z)*(1+star (q.m z))))*M).re =
      -(Complex.normSq (q.a z) / (q.B^2 * Complex.normSq z)) * (M*q.b z/q.a z).re := by
  have he : (star ((1-q.m z)*(1+star (q.m z))))*M =
      -((Complex.normSq (q.a z) / (q.B^2 * Complex.normSq z) : ℝ) : ℂ) *
        (M*q.b z/q.a z) := by
    rw [q.factor hz]
    simp only [star_div₀, star_neg, star_mul, Complex.star_def,
      Complex.conj_ofReal, map_pow]
    push_cast
    rw [show (Complex.normSq (q.a z) : ℂ) = q.a z * star (q.a z) by
      exact (Complex.mul_conj (q.a z)).symm]
    field_simp
    simp only [Complex.conj_conj, Complex.star_def]
    ring
  rw [he]
  rw [Complex.mul_re]
  simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    neg_zero, zero_mul, sub_zero]

theorem factor_sharp (q : Tuning) {u : ℂ} (hu : u ≠ 0) :
    (1-q.m ((star u)⁻¹))*(1+star (q.m ((star u)⁻¹))) =
      -star (aSharp q u)*bSharp q u / ((q.B : ℂ)^2*(Complex.normSq u : ℂ)) := by
  have hus : star u ≠ 0 := star_ne_zero.mpr hu
  have hB : (q.B : ℂ) ≠ 0 := by exact_mod_cast q.B_ne_zero
  rw [show (Complex.normSq u : ℂ) = u*star u from (Complex.mul_conj u).symm]
  unfold Tuning.m aSharp bSharp
  rw [← q.A_add_B, ← q.A_sub_B]
  push_cast
  simp only [star_div₀, star_sub, star_add, star_inv₀, star_mul, star_pow,
    star_one, Complex.star_def, Complex.conj_ofReal]
  simp only [Complex.star_def] at hus
  field_simp [hu, hus, hB]
  simp only [← Complex.star_def, star_star]
  ring

theorem factor_sharp_re_lower (q : Tuning) {u : ℂ} (hu : u ≠ 0)
    (ha : aSharp q u ≠ 0) (M : ℂ) :
    (((1-q.m ((star u)⁻¹))*(1+star (q.m ((star u)⁻¹))))*M).re =
      -(Complex.normSq (aSharp q u)/(q.B^2*Complex.normSq u)) *
        (M*bSharp q u/aSharp q u).re := by
  have he : ((1-q.m ((star u)⁻¹))*(1+star (q.m ((star u)⁻¹))))*M =
      -((Complex.normSq (aSharp q u)/(q.B^2*Complex.normSq u) : ℝ):ℂ)*
        (M*bSharp q u/aSharp q u) := by
    rw [factor_sharp q hu]
    push_cast
    rw [show (Complex.normSq (aSharp q u) : ℂ) = aSharp q u*star (aSharp q u)
      from (Complex.mul_conj _).symm]
    field_simp
  rw [he, Complex.mul_re]
  simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    neg_zero, zero_mul, sub_zero]

theorem factor_sharp_re_upper (q : Tuning) {u : ℂ} (hu : u ≠ 0)
    (hb : bSharp q u ≠ 0) (M : ℂ) :
    ((star ((1-q.m ((star u)⁻¹))*(1+star (q.m ((star u)⁻¹)))))*M).re =
      -(Complex.normSq (bSharp q u)/(q.B^2*Complex.normSq u)) *
        (M*aSharp q u/bSharp q u).re := by
  have he : (star ((1-q.m ((star u)⁻¹))*(1+star (q.m ((star u)⁻¹)))))*M =
      -((Complex.normSq (bSharp q u)/(q.B^2*Complex.normSq u) : ℝ):ℂ)*
        (M*aSharp q u/bSharp q u) := by
    rw [factor_sharp q hu]
    simp only [star_div₀, star_neg, star_mul, Complex.star_def,
      Complex.conj_ofReal, map_pow]
    push_cast
    rw [show (Complex.normSq (bSharp q u) : ℂ) = bSharp q u*star (bSharp q u)
      from (Complex.mul_conj _).symm]
    field_simp
    simp only [← Complex.star_def, star_star]
    ring
  rw [he, Complex.mul_re]
  simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    neg_zero, zero_mul, sub_zero]

theorem lower_positive_term (m : ℂ) (t ω : ℝ) (n : ℕ) :
    Real.exp (-(n*t)) * ((1-Complex.normSq m) *
      (Real.cosh (n*t)-Real.cos (n*ω)) - 2*m.im*Real.sin (n*ω) +
      Real.sinh (n*t)*(1-Complex.normSq m)) =
      (((1-Complex.normSq m : ℝ) : ℂ) - 2*Complex.I*(m.im : ℂ)).re -
        ((((1-Complex.normSq m : ℝ) : ℂ) - 2*Complex.I*(m.im : ℂ)) *
          Waves.z (-t) ω ^ n).re := by
  have he : Real.exp (-(n*t)) * (Real.cosh (n*t)+Real.sinh (n*t)) = 1 := by
    rw [Real.cosh_add_sinh, ← Real.exp_add]; simp
  have hn : (n:ℝ)*(-t) = -(n*t) := by ring
  simp [Complex.mul_re, Complex.mul_im, Waves.z_pow_re, Waves.z_pow_im, hn]
  linear_combination (1-Complex.normSq m)*he

theorem lower_negative_term (m : ℂ) (t ω : ℝ) (n : ℕ) :
    Real.exp (n*t) * ((1-Complex.normSq m) *
      (Real.cosh (n*t)-Real.cos (n*ω)) - 2*m.im*Real.sin (n*ω) -
      Real.sinh (n*t)*(1-Complex.normSq m)) =
      (((1-Complex.normSq m : ℝ) : ℂ) - 2*Complex.I*(m.im : ℂ)).re -
        ((((1-Complex.normSq m : ℝ) : ℂ) - 2*Complex.I*(m.im : ℂ)) *
          Waves.z t ω ^ n).re := by
  have he : Real.exp (n*t) * (Real.cosh (n*t)-Real.sinh (n*t)) = 1 := by
    rw [Real.cosh_sub_sinh, ← Real.exp_add]; simp
  simp [Complex.mul_re, Complex.mul_im, Waves.z_pow_re, Waves.z_pow_im]
  linear_combination (1-Complex.normSq m)*he

theorem polynomial_re (s : Finset ℕ) (lam : ℕ → ℝ) (W z : ℂ) :
    (W * polynomial s lam z).re =
      ∑ n ∈ s, lam n * (W.re-(W*z^n).re) := by
  simp only [polynomial, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have he : W*((lam n : ℂ)*(1-z^n)) = (lam n : ℂ)*(W-W*z^n) := by ring
  rw [he, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re]

theorem lower_positive_symbol (m : C(Spectral.Frequency, ℂ)) (s : Finset ℕ)
    (lam : ℕ → ℝ) (t : ℝ) (c : Spectral.Frequency) :
    Duality.symbol m t s (fun n => lam n*Real.exp (-(n*t))) (fun _ => 0) 0
      (∑ n ∈ s, lam n*Real.exp (-(n*t))*Real.sinh (n*t)) c =
      ((((Duality.g m c : ℝ) : ℂ)-2*Complex.I*((m c).im : ℂ)) *
        polynomial s lam (Waves.z (-t) (Real.arccos c))).re := by
  rw [polynomial_re]
  unfold Duality.symbol
  simp only [zero_mul, add_zero, zero_add, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have h := lower_positive_term (m c) t (Real.arccos c) n
  dsimp [Duality.a, Duality.b, Duality.g]
  convert congrArg (fun v : ℝ => lam n*v) h using 1
  ring

theorem lower_negative_symbol (m : C(Spectral.Frequency, ℂ)) (s : Finset ℕ)
    (lam : ℕ → ℝ) (t : ℝ) (c : Spectral.Frequency) :
    Duality.symbol m t s (fun n => lam n*Real.exp (n*t)) (fun _ => 0)
      (-(∑ n ∈ s, lam n*Real.exp (n*t)*Real.sinh (n*t))) 0 c =
      ((((Duality.g m c : ℝ) : ℂ)-2*Complex.I*((m c).im : ℂ)) *
        polynomial s lam (Waves.z t (Real.arccos c))).re := by
  rw [polynomial_re]
  unfold Duality.symbol
  simp only [zero_mul, add_zero, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have h := lower_negative_term (m c) t (Real.arccos c) n
  dsimp [Duality.a, Duality.b, Duality.g]
  convert congrArg (fun v : ℝ => lam n*v) h using 1
  ring

def conjugateMap (m : C(Spectral.Frequency, ℂ)) : C(Spectral.Frequency, ℂ) where
  toFun c := star (m c)
  continuous_toFun := continuous_star.comp m.continuous

theorem symbol_conjugate (m : C(Spectral.Frequency, ℂ)) (t : ℝ) (s : Finset ℕ)
    (alpha beta : ℕ → ℝ) (gp gm : ℝ) (c : Spectral.Frequency) :
    Duality.symbol (conjugateMap m) t s alpha beta gp gm c =
      Duality.symbol m t s beta alpha gm gp c := by
  unfold Duality.symbol Duality.a Duality.b Duality.g
  simp only [conjugateMap, ContinuousMap.coe_mk, Complex.star_def,
    Complex.normSq_conj, Complex.conj_im]
  rw [add_comm gm gp]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem upper_positive_symbol (m : C(Spectral.Frequency, ℂ)) (s : Finset ℕ)
    (lam : ℕ → ℝ) (t : ℝ) (c : Spectral.Frequency) :
    Duality.symbol m t s (fun _ => 0) (fun n => lam n*Real.exp (-(n*t)))
      (∑ n ∈ s, lam n*Real.exp (-(n*t))*Real.sinh (n*t)) 0 c =
      ((star (((Duality.g m c : ℝ) : ℂ)-2*Complex.I*((m c).im : ℂ))) *
        polynomial s lam (Waves.z (-t) (Real.arccos c))).re := by
  rw [← symbol_conjugate]
  rw [lower_positive_symbol]
  congr 2
  apply Complex.ext <;> simp [Duality.g, conjugateMap, Complex.mul_re, Complex.mul_im]

theorem upper_negative_symbol (m : C(Spectral.Frequency, ℂ)) (s : Finset ℕ)
    (lam : ℕ → ℝ) (t : ℝ) (c : Spectral.Frequency) :
    Duality.symbol m t s (fun _ => 0) (fun n => lam n*Real.exp (n*t))
      0 (-(∑ n ∈ s, lam n*Real.exp (n*t)*Real.sinh (n*t))) c =
      ((star (((Duality.g m c : ℝ) : ℂ)-2*Complex.I*((m c).im : ℂ))) *
        polynomial s lam (Waves.z t (Real.arccos c))).re := by
  rw [← symbol_conjugate]
  rw [lower_negative_symbol]
  congr 2
  apply Complex.ext <;> simp [Duality.g, conjugateMap, Complex.mul_re, Complex.mul_im]

end
end polyak.General.Multipliers
