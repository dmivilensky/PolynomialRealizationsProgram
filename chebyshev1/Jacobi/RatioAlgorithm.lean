import chebyshev1.Jacobi.Exactness
import chebyshev1.Perturbations.Duhamel

/-! A ratio recurrence that computes Jacobi method coefficients without continuant growth. -/
namespace chebyshev1.JacobiData
noncomputable section
variable (J : JacobiData) (I : SpectralInterval)

/-- `ratioState s` represents `P_(s-1)(eta) / P_s(eta)` for positive `s`. -/
def ratioState (J : JacobiData) (I : SpectralInterval) : ℕ → ℝ
  | 0 => 0
  | s + 1 => 1 / (I.eta - J.b s - J.aSq s * ratioState J I s)

def ratioDenominator (s : ℕ) : ℝ := I.eta - J.b s - J.aSq s * J.ratioState I s

theorem ratioState_succ (s : ℕ) :
    J.ratioState I (s + 1) = 1 / J.ratioDenominator I s := rfl

theorem ratioState_eq_den_ratio {N : ℕ} (h : J.Admissible I N)
    (s : ℕ) (hs : s + 1 ≤ N) :
    J.ratioState I (s + 1) = J.den I s / J.den I (s + 1) := by
  induction s with
  | zero => simp [ratioState]
  | succ s ih =>
    rw [ratioState, ih (by omega)]
    have hr := J.den_add_two I s
    have hd : I.eta - J.b (s + 1) - J.aSq (s + 1) *
        (J.den I s / J.den I (s + 1)) = J.den I (s + 2) / J.den I (s + 1) := by
      field_simp [J.den_ne I h (show s + 1 ≤ N by omega)]
      nlinarith
    rw [hd, one_div_div]

theorem ratioDenominator_eq {N : ℕ} (h : J.Admissible I N)
    (s : ℕ) (hs : s + 1 ≤ N) :
    J.ratioDenominator I s = J.den I (s + 1) / J.den I s := by
  cases s with
  | zero => simp [ratioDenominator, ratioState]
  | succ s =>
    rw [ratioDenominator, J.ratioState_eq_den_ratio I h s (by omega)]
    have hr := J.den_add_two I s
    field_simp [J.den_ne I h (show s + 1 ≤ N by omega)]
    nlinarith

/-- Every division executed through the admissible horizon has a positive denominator. -/
theorem ratioDenominator_pos {N : ℕ} (h : J.Admissible I N)
    (s : ℕ) (hs : s + 1 ≤ N) : 0 < J.ratioDenominator I s := by
  rw [J.ratioDenominator_eq I h s hs]
  exact div_pos (h _ hs) (h _ (by omega))

theorem ratioState_pos {N : ℕ} (h : J.Admissible I N)
    (s : ℕ) (hs : s + 1 ≤ N) : 0 < J.ratioState I (s + 1) := by
  rw [ratioState_succ]
  exact one_div_pos.mpr (J.ratioDenominator_pos I h s hs)

/-- Coefficients generated from the bounded-size scalar ratio state. -/
def ratioMethod : TwoTerm where
  a := fun s => (I.eta - J.b s) / J.ratioDenominator I s
  b := fun s => -(J.aSq s * J.ratioState I s / J.ratioDenominator I s)
  gamma := fun s => 2 / (I.delta * J.ratioDenominator I s)

theorem ratioMethod_a {N : ℕ} (h : J.Admissible I N)
    (s : ℕ) (hs : s + 1 ≤ N) : (J.ratioMethod I).a s = (J.method I).a s := by
  simp only [ratioMethod]
  rw [J.ratioDenominator_eq I h s hs]
  dsimp [method]
  field_simp [J.den_ne I h (show s ≤ N by omega)]

theorem ratioMethod_b {N : ℕ} (h : J.Admissible I N)
    (s : ℕ) (hs : s + 2 ≤ N) :
    (J.ratioMethod I).b (s + 1) = (J.method I).b (s + 1) := by
  simp only [ratioMethod, method, Nat.add_sub_cancel]
  rw [J.ratioState_eq_den_ratio I h s (by omega),
    J.ratioDenominator_eq I h (s + 1) (by omega)]
  field_simp [J.den_ne I h (show s + 1 ≤ N by omega)]

theorem ratioMethod_gamma {N : ℕ} (h : J.Admissible I N)
    (s : ℕ) (hs : s + 1 ≤ N) :
    (J.ratioMethod I).gamma s = (J.method I).gamma s := by
  simp only [ratioMethod]
  rw [J.ratioDenominator_eq I h s hs]
  dsimp [method]
  field_simp [J.den_ne I h (show s ≤ N by omega)]

/-- Equality of the actual iterates, including horizons zero and one. -/
theorem ratioMethod_quadraticError {d : Type*} [Fintype d] [DecidableEq d]
    {N : ℕ} (h : J.Admissible I N) (H : Matrix d d ℝ) (e0 : d → ℝ)
    (n : ℕ) (hn : n ≤ N) :
    (J.ratioMethod I).quadraticError H e0 n = (J.method I).quadraticError H e0 n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one =>
    rw [TwoTerm.quadraticError, TwoTerm.quadraticError,
      J.ratioMethod_gamma I h 0 (by omega)]
  | more n ih0 ih1 =>
    rw [TwoTerm.quadraticError, TwoTerm.quadraticError,
      ih0 (by omega), ih1 (by omega),
      J.ratioMethod_a I h (n + 1) (by omega),
      J.ratioMethod_b I h n (by omega),
      J.ratioMethod_gamma I h (n + 1) (by omega)]

/-- Ratio execution agrees for an arbitrary gradient oracle, not just on quadratics. -/
theorem ratioMethod_nonlinearError {d : Type*}
    {N : ℕ} (h : J.Admissible I N) (g : (d → ℝ) → d → ℝ) (e0 : d → ℝ)
    (n : ℕ) (hn : n ≤ N) :
    (J.ratioMethod I).nonlinearError g e0 n = (J.method I).nonlinearError g e0 n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one =>
    rw [TwoTerm.nonlinearError, TwoTerm.nonlinearError,
      J.ratioMethod_gamma I h 0 (by omega)]
  | more n ih0 ih1 =>
    rw [TwoTerm.nonlinearError, TwoTerm.nonlinearError,
      ih0 (by omega), ih1 (by omega),
      J.ratioMethod_a I h (n + 1) (by omega),
      J.ratioMethod_b I h n (by omega),
      J.ratioMethod_gamma I h (n + 1) (by omega)]

end
end chebyshev1.JacobiData
