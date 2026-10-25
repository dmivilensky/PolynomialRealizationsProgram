import polyak.Growth.Quadratic
import Mathlib.Analysis.Subadditive

/-!
Article: Appendix A, Lemma growth envelope.
Use: Fekete's lemma for the exact positive segment envelope.
Proof: take logarithms, establish the uniform lower bound, then exponentiate.
-/

namespace polyak.Growth
noncomputable section
open Set Filter
open scoped Topology

/-- Article: log Γ. Use: convert submultiplicativity to subadditivity. -/
theorem envelope_log_subadditive {A B β : ℝ} (hB : B ≠ 0) :
    Subadditive (fun n => Real.log (envelope A B β n)) := by
  intro p q
  calc
    Real.log (envelope A B β (p+q)) ≤
      Real.log (envelope A B β p * envelope A B β q) :=
      Real.log_le_log (envelope_pos hB _) (envelope_submultiplicative A B β p q)
    _ = _ := Real.log_mul (ne_of_gt (envelope_pos hB _)) (ne_of_gt (envelope_pos hB _))

/-- Article: growth exponent. Use: the lower envelope of logarithmic secant rates. -/
def growthExponent (A B β : ℝ) : ℝ :=
  sInf ((fun n : ℕ => Real.log (envelope A B β n) / n) '' Ici 1)

/-- Article: ρΓ. Use: the genuine free-segment exponential growth rate. -/
def growthRate (A B β : ℝ) : ℝ := Real.exp (growthExponent A B β)

/-- Article: finite lower exponent. Use: the lower bound required by Fekete's lemma. -/
theorem envelope_log_bddBelow {A B β : ℝ} (hB : B ≠ 0) :
    BddBelow (range (fun n : ℕ => Real.log (envelope A B β n) / n)) := by
  obtain ⟨b,hb,hl⟩ := envelope_lower_base (A := A) (β := β) hB
  refine ⟨min (Real.log b) 0, ?_⟩
  rintro _ ⟨n,rfl⟩
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hh := Real.log_le_log (pow_pos hb n) (hl n)
    rw [Real.log_pow] at hh
    exact (min_le_left _ _).trans ((le_div_iff₀ hn').2 (by nlinarith))

/-- Article: Fekete limit. Use: the exact logarithmic limit, with a proved lower bound. -/
theorem tendsto_envelope_log_div {A B β : ℝ} (hB : B ≠ 0) :
    Tendsto (fun n : ℕ => Real.log (envelope A B β n) / n) atTop
      (𝓝 (growthExponent A B β)) := by
  simpa only [Subadditive.lim, growthExponent] using
    (envelope_log_subadditive (A := A) (β := β) hB).tendsto_lim (envelope_log_bddBelow hB)

/-- Article: ρΓ>0. Use: the definition is exponentiation of a finite real exponent. -/
theorem growthRate_pos (A B β : ℝ) : 0 < growthRate A B β := Real.exp_pos _

/-- Article: root limit. Use: the free growth envelope has a genuine limit, not only limsup. -/
theorem tendsto_envelope_root {A B β : ℝ} (hB : B ≠ 0) :
    Tendsto (fun n : ℕ => envelope A B β n ^ ((n : ℝ)⁻¹)) atTop
      (𝓝 (growthRate A B β)) := by
  have hh := (Real.continuous_exp.tendsto _).comp
    (tendsto_envelope_log_div (A := A) (β := β) hB)
  simpa only [Function.comp_def, growthRate, Real.rpow_def_of_pos (envelope_pos hB _),
    div_eq_mul_inv] using hh

/-- Article: infimum formula. Use: the growth exponent is below every positive-horizon rate. -/
theorem growthExponent_le_div {A B β : ℝ} (hB : B ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    growthExponent A B β ≤ Real.log (envelope A B β n) / n := by
  simpa only [Subadditive.lim, growthExponent] using
    (envelope_log_subadditive (A := A) (β := β) hB).lim_le_div (envelope_log_bddBelow hB) hn

/-- Article: Γ(n)≥ρΓⁿ. Use: the normalized envelope never falls below one. -/
theorem growthRate_pow_le_envelope {A B β : ℝ} (hB : B ≠ 0) (n : ℕ) :
    growthRate A B β ^ n ≤ envelope A B β n := by
  by_cases hn : n = 0
  · simp [hn, envelope_zero]
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hh := (le_div_iff₀ hn').mp (growthExponent_le_div (A := A) (β := β) hB hn)
    rw [growthRate, ← Real.exp_nat_mul, ← Real.exp_log (envelope_pos hB n)]
    apply Real.exp_le_exp.mpr
    nlinarith

/-- Article: infimum formula. Use: the rate is the greatest lower bound of all positive roots. -/
theorem growthRate_isGLB {A B β : ℝ} (hB : B ≠ 0) :
    IsGLB ((fun n : ℕ => envelope A B β n ^ ((n : ℝ)⁻¹)) '' Ici 1)
      (growthRate A B β) := by
  constructor
  · rintro _ ⟨n,hn,rfl⟩
    change 1 ≤ n at hn
    change growthRate A B β ≤ envelope A B β n ^ ((n : ℝ)⁻¹)
    rw [growthRate, Real.rpow_def_of_pos (envelope_pos hB n)]
    apply Real.exp_le_exp.mpr
    simpa only [div_eq_mul_inv] using growthExponent_le_div hB (by omega : n ≠ 0)
  · intro b hb
    apply ge_of_tendsto (tendsto_envelope_root (A := A) (β := β) hB)
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hb ⟨n,hn,rfl⟩

/-- Article: infimum formula. Use: exact equality of the source root infimum and the limit. -/
theorem growthRate_eq_inf {A B β : ℝ} (hB : B ≠ 0) :
    growthRate A B β =
      sInf ((fun n : ℕ => envelope A B β n ^ ((n : ℝ)⁻¹)) '' Ici 1) :=
  ((growthRate_isGLB (A := A) (β := β) hB).csInf_eq ⟨_, 1, by simp, rfl⟩).symm

/-- Article: strict exponential majorants. Use: control the subexponential envelope factor. -/
theorem eventually_envelope_le_pow {A B β R : ℝ} (hB : B ≠ 0)
    (hR : growthRate A B β < R) :
    ∀ᶠ n : ℕ in atTop, envelope A B β n ≤ R^n := by
  have hRp : 0 < R := (growthRate_pos A B β).trans hR
  have he : growthExponent A B β < Real.log R := by
    rw [← Real.exp_lt_exp, Real.exp_log hRp]
    exact hR
  filter_upwards [(tendsto_envelope_log_div hB).eventually (gt_mem_nhds he),
    eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hh := (div_lt_iff₀ hn').mp hn
  rw [← Real.exp_log (envelope_pos hB n), ← Real.rpow_natCast, Real.rpow_def_of_pos hRp]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- Article: strict exponential majorants. Use: one constant controls all horizons. -/
theorem exists_envelope_le_mul_pow {A B β R : ℝ} (hB : B ≠ 0)
    (hR : growthRate A B β < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, envelope A B β n ≤ C*R^n := by
  have hRp : 0 < R := (growthRate_pos A B β).trans hR
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_envelope_le_pow hB hR)
  let C : ℝ := 1 + ∑ k ∈ Finset.range N, envelope A B β k / R^k
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ =>
      div_nonneg (envelope_nonneg A B β k) (pow_pos hRp k).le))
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC, fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (by nlinarith [pow_pos hRp n])
  · have hnN : n ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hs : envelope A B β n / R^n ≤ ∑ k ∈ Finset.range N, envelope A B β k / R^k :=
      Finset.single_le_sum (fun k _ => div_nonneg (envelope_nonneg A B β k) (pow_pos hRp k).le) hnN
    apply (div_le_iff₀ (pow_pos hRp n)).mp
    dsimp [C]
    linarith

/-- Article: exponential lower bounds pass to the rate. Use: both quadratic and spectral lower rates. -/
theorem le_growthRate_of_pow_le {A B β b : ℝ} (hB : B ≠ 0) (hb : 0 ≤ b)
    (h : ∀ n : ℕ, b^n ≤ envelope A B β n) : b ≤ growthRate A B β := by
  apply ge_of_tendsto (tendsto_envelope_root (A := A) (β := β) hB)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hh := Real.rpow_le_rpow (pow_nonneg hb n) (h n) (by positivity : 0 ≤ (n : ℝ)⁻¹)
  simpa only [Real.pow_rpow_inv_natCast hb (by omega : n ≠ 0)] using hh

/-- Article: ρΓ≥ρq. Use: exact lower rate for every quadratically stable tuning. -/
theorem quadraticRate_le_growthRate {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β < 1) (hquad : α*L < 2*(1+β)) :
    Dynamics.quadraticRate μ L α β ≤
      growthRate (Dynamics.normalizedA μ L α β) (Dynamics.normalizedB μ L α) β := by
  have hB : Dynamics.normalizedB μ L α ≠ 0 := by
    dsimp [Dynamics.normalizedB]
    positivity
  exact le_growthRate_of_pow_le hB (quadraticRate_pos hμ hL hα hβ hβ1 hquad).le
    (quadraticRate_pow_le_envelope hμ hL hα hβ hβ1 hquad)

/-- Article: feasible spectral rate lower bound. Use: every feasible exponent bounds free growth. -/
theorem exp_le_growthRate {A B β C t : ℝ} (ν : Spectral.Spectrum) (hB : B ≠ 0)
    (h : Waves.MixtureFeasible ν (Waves.multiplierMap A B β t) C t) :
    Real.exp t ≤ growthRate A B β := by
  apply le_growthRate_of_pow_le hB (Real.exp_pos t).le
  intro n
  rw [← Real.exp_nat_mul]
  exact exp_le_envelope ν hB h n

end
end polyak.Growth
