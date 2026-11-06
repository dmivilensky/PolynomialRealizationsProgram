import chebyshev1.Jacobi.Exactness
import chebyshev1.Perturbations.Duhamel

/-! Reconstruction of Jacobi coordinates from positive fixed-point two-term data. -/
namespace chebyshev1.TwoTerm
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Positive steps and positive momentum, with the separate initial step normalized. -/
structure PositiveFixedPoint (S : TwoTerm) : Prop where
  gamma_pos : ∀ s, 0 < S.gamma s
  a_zero : S.a 0 = 1
  b_zero : S.b 0 = 0
  fixed_point : ∀ s, S.a (s+1) + S.b (s+1) = 1
  momentum_pos : ∀ s, S.b (s+1) < 0

/-- Normalizing values forced by the positive stepsizes. -/
def jacobiScale (S : TwoTerm) (I : SpectralInterval) : ℕ → ℝ
  | 0 => 1
  | s+1 => (2 / I.delta) * S.jacobiScale I s / S.gamma s

theorem jacobiScale_pos (S : TwoTerm) (I : SpectralInterval)
    (h : S.PositiveFixedPoint) (s : ℕ) : 0 < S.jacobiScale I s := by
  induction s with
  | zero => norm_num [jacobiScale]
  | succ s ih =>
    exact div_pos (mul_pos (div_pos (by norm_num) I.delta_pos) ih) (h.gamma_pos s)

/-- The unique recurrence coordinates compatible with the chosen normalization. -/
def jacobiCoordinates (S : TwoTerm) (I : SpectralInterval) : JacobiData where
  b s := I.eta - S.a s * S.jacobiScale I (s+1) / S.jacobiScale I s
  aSq s := if s = 0 then 0 else
    -S.b s * S.jacobiScale I (s+1) / S.jacobiScale I (s-1)

theorem jacobiCoordinates_aSq_pos (S : TwoTerm) (I : SpectralInterval)
    (h : S.PositiveFixedPoint) (s : ℕ) : 0 < (S.jacobiCoordinates I).aSq (s+1) := by
  simp only [jacobiCoordinates, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel]
  exact div_pos (mul_pos (neg_pos.mpr (h.momentum_pos s))
    (S.jacobiScale_pos I h _)) (S.jacobiScale_pos I h _)

theorem jacobiCoordinates_aSq_nonneg (S : TwoTerm) (I : SpectralInterval)
    (h : S.PositiveFixedPoint) (s : ℕ) : 0 ≤ (S.jacobiCoordinates I).aSq s := by
  cases s with
  | zero => simp [jacobiCoordinates]
  | succ s => exact (S.jacobiCoordinates_aSq_pos I h s).le

theorem jacobiCoordinates_den (S : TwoTerm) (I : SpectralInterval)
    (h : S.PositiveFixedPoint) (s : ℕ) :
    (S.jacobiCoordinates I).den I s = S.jacobiScale I s := by
  induction s using Nat.twoStepInduction with
  | zero => simp [jacobiScale]
  | one => simp [jacobiCoordinates, h.a_zero, jacobiScale]
  | more s ih₀ ih₁ =>
    rw [JacobiData.den_add_two, ih₀, ih₁]
    simp only [jacobiCoordinates, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel]
    have h₀ := ne_of_gt (S.jacobiScale_pos I h s)
    have h₁ := ne_of_gt (S.jacobiScale_pos I h (s+1))
    calc
      _ = (S.a (s+1)+S.b (s+1))*S.jacobiScale I (s+2) := by field_simp; ring
      _ = _ := by rw [h.fixed_point]; ring

theorem jacobiCoordinates_admissible (S : TwoTerm) (I : SpectralInterval)
    (h : S.PositiveFixedPoint) (N : ℕ) : (S.jacobiCoordinates I).Admissible I N := by
  intro s _
  rw [S.jacobiCoordinates_den I h]
  exact S.jacobiScale_pos I h s

/-- The reconstruction recovers all three stored coefficient sequences. -/
theorem jacobiCoordinates_method (S : TwoTerm) (I : SpectralInterval)
    (h : S.PositiveFixedPoint) : (S.jacobiCoordinates I).method I = S := by
  have hscale (s : ℕ) := ne_of_gt (S.jacobiScale_pos I h s)
  have hgamma (s : ℕ) := ne_of_gt (h.gamma_pos s)
  have hd := ne_of_gt I.delta_pos
  have hext (x y : TwoTerm) (ha : x.a=y.a) (hb : x.b=y.b) (hg : x.gamma=y.gamma) :
      x=y := by cases x; cases y; simp_all only
  apply hext <;> funext s
  · change (S.jacobiCoordinates I).den I s / (S.jacobiCoordinates I).den I (s+1) *
      (I.eta-(S.jacobiCoordinates I).b s) = _
    simp only [jacobiCoordinates_den _ _ h]
    dsimp only [jacobiCoordinates]
    field_simp [hscale]
    ring
  · change -((S.jacobiCoordinates I).aSq s * (S.jacobiCoordinates I).den I (s-1) /
      (S.jacobiCoordinates I).den I (s+1)) = _
    simp only [jacobiCoordinates_den _ _ h]
    dsimp only [jacobiCoordinates]
    by_cases hs : s=0
    · subst s
      simp [h.b_zero]
    · simp only [hs, ↓reduceIte]
      field_simp [hscale]
  · change (2/I.delta)*(S.jacobiCoordinates I).den I s /
      (S.jacobiCoordinates I).den I (s+1) = _
    simp only [jacobiCoordinates_den _ _ h, jacobiScale]
    field_simp [hscale, hgamma, hd]

/-- In particular, every actual nonlinear execution is preserved by reconstruction. -/
theorem jacobiCoordinates_nonlinearError (S : TwoTerm) (I : SpectralInterval)
    (h : S.PositiveFixedPoint) {d : Type*} [Fintype d] [DecidableEq d]
    (g : (d → ℝ) → d → ℝ) (e0 : d → ℝ) (n : ℕ) :
    ((S.jacobiCoordinates I).method I).nonlinearError g e0 n = S.nonlinearError g e0 n := by
  rw [S.jacobiCoordinates_method I h]

end
end chebyshev1.TwoTerm
