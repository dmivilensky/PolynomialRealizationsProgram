import chebyshev1.Jacobi.Prefix

/-! The prefix recurrence with a scalar ratio state instead of growing Chebyshev values. -/
namespace chebyshev1.Prefix
noncomputable section
variable (I : SpectralInterval)

/-- At index `s`, this state is `T_s(eta) / T_(s+1)(eta)`. -/
def ratioState (I : SpectralInterval) : ℕ → ℝ
  | 0 => 1 / I.eta
  | s + 1 => 1 / (2 * I.eta - ratioState I s)

def ratioDenominator (s : ℕ) : ℝ := 2 * I.eta - ratioState I s

theorem ratioState_eq (s : ℕ) : ratioState I s = I.den s / I.den (s + 1) := by
  induction s with
  | zero => simp [ratioState]
  | succ s ih =>
    rw [ratioState, ih]
    have hd : 2 * I.eta - I.den s / I.den (s + 1) = I.den (s + 2) / I.den (s + 1) := by
      rw [I.den_add_two]
      field_simp [I.den_ne (s + 1)]
    rw [hd, one_div_div]

theorem ratioDenominator_eq (s : ℕ) :
    ratioDenominator I s = I.den (s + 2) / I.den (s + 1) := by
  rw [ratioDenominator, ratioState_eq, I.den_add_two]
  field_simp [I.den_ne (s + 1)]

theorem ratioState_pos (s : ℕ) : 0 < ratioState I s := by
  rw [ratioState_eq]
  exact div_pos (I.den_pos s) (I.den_pos (s + 1))

theorem ratioDenominator_pos (s : ℕ) : 0 < ratioDenominator I s := by
  rw [ratioDenominator_eq]
  exact div_pos (I.den_pos (s + 2)) (I.den_pos (s + 1))

/-- The ratio loop computes momentum and gradient coefficients of the old API. -/
theorem ratio_coefficients (s : ℕ) :
    beta I (s + 1) = ratioState I s / ratioDenominator I s ∧
      gamma I (s + 1) = 4 / (I.delta * ratioDenominator I s) ∧
      ratioState I (s + 1) = 1 / ratioDenominator I s := by
  rw [ratioState_eq, ratioDenominator_eq]
  constructor
  · simp only [beta, Nat.add_sub_cancel]
    field_simp [I.den_ne (s + 1)]
  · constructor
    · simp only [gamma]
      field_simp [I.den_ne (s + 1)]
    · rw [ratioState_eq, one_div_div]

/-- A complete algorithm defined using only ratio updates. -/
def ratioMethod : TwoTerm where
  a := fun s => match s with
    | 0 => 1
    | t + 1 => 2 * I.eta / ratioDenominator I t
  b := fun s => match s with
    | 0 => 0
    | t + 1 => -(ratioState I t / ratioDenominator I t)
  gamma := fun s => match s with
    | 0 => 2 / (I.L + I.mu)
    | t + 1 => 4 / (I.delta * ratioDenominator I t)

theorem ratioMethod_eq : ratioMethod I = jacobiData.method I := by
  have ha : (ratioMethod I).a = (jacobiData.method I).a := by
    funext s
    cases s with
    | zero =>
      have he : I.eta ≠ 0 := (lt_trans zero_lt_one I.eta_gt_one).ne'
      simp [ratioMethod, JacobiData.method, he]
    | succ s =>
      simp only [ratioMethod, jacobi_a_succ, ratioDenominator_eq]
      field_simp [I.den_ne (s + 1)]
  have hb : (ratioMethod I).b = (jacobiData.method I).b := by
    funext s
    cases s with
    | zero => simp [ratioMethod, JacobiData.method, jacobiData]
    | succ s =>
      simp only [ratioMethod, jacobi_b_succ]
      rw [← (ratio_coefficients I s).1]
      rfl
  have hg : (ratioMethod I).gamma = (jacobiData.method I).gamma := by
    funext s
    rw [jacobi_gamma]
    cases s with
    | zero => rfl
    | succ s => exact (ratio_coefficients I s).2.1.symm
  cases hleft : ratioMethod I
  cases hright : jacobiData.method I
  simp only [hleft, hright] at ha hb hg
  cases ha
  cases hb
  cases hg
  rfl

theorem ratio_realization_eq : (ratioMethod I).realization = realization I := by
  rw [ratioMethod_eq]
  exact jacobi_realization I

/-- Equality of terminal executions for every horizon, including the one-step case. -/
theorem ratio_quadraticError_exact {d : Type*} [Fintype d] [DecidableEq d]
    (H : Matrix d d ℝ) (e0 : d → ℝ) (N : ℕ) :
    (ratioMethod I).quadraticError H e0 N = (Polynomial.aeval H (I.residual N)).mulVec e0 := by
  rw [TwoTerm.quadraticError_eq_transfer, ratio_realization_eq,
    operator_exact I N H]

end
end chebyshev1.Prefix
