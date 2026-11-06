import chebyshev1.Jacobi.Converse

/-! The converse uses only the coefficients queried at the finite horizon. -/
namespace chebyshev1.TwoTerm
noncomputable section

structure PositiveFixedPointUpTo (S : TwoTerm) (N : ℕ) : Prop where
  gamma_pos : ∀ s < N, 0 < S.gamma s
  a_zero : S.a 0 = 1
  b_zero : S.b 0 = 0
  fixed_point : ∀ s, 0 < s → s < N → S.a s + S.b s = 1
  momentum_pos : ∀ s, 0 < s → s < N → S.b s < 0

/-- Extend unused coefficients by a fixed positive-momentum method. -/
def positiveExtension (S : TwoTerm) (N : ℕ) : TwoTerm where
  a s := if s = 0 then 1 else if s < N then S.a s else 2
  b s := if s = 0 then 0 else if s < N then S.b s else -1
  gamma s := if s < N then S.gamma s else 1

theorem positiveExtension_positive (S : TwoTerm) {N : ℕ}
    (h : S.PositiveFixedPointUpTo N) : (S.positiveExtension N).PositiveFixedPoint := by
  constructor
  · intro s
    by_cases hs : s < N
    · simpa [positiveExtension, hs] using h.gamma_pos s hs
    · simp [positiveExtension, hs]
  · simp [positiveExtension]
  · simp [positiveExtension]
  · intro s
    by_cases hs : s+1 < N
    · simpa [positiveExtension, hs] using h.fixed_point (s+1) (by omega) hs
    · norm_num [positiveExtension, hs]
  · intro s
    by_cases hs : s+1 < N
    · simpa [positiveExtension, hs] using h.momentum_pos (s+1) (by omega) hs
    · simp [positiveExtension, hs]

theorem positiveExtension_coefficients (S : TwoTerm) {N : ℕ}
    (h : S.PositiveFixedPointUpTo N) (s : ℕ) (hs : s < N) :
    (S.positiveExtension N).a s = S.a s ∧
    (S.positiveExtension N).b s = S.b s ∧
    (S.positiveExtension N).gamma s = S.gamma s := by
  by_cases hz : s = 0
  · subst s
    simp [positiveExtension, h.a_zero, h.b_zero, hs]
  · simp [positiveExtension, hs, hz]

/-- The actual nonlinear trajectory depends only on coefficients before its horizon. -/
theorem nonlinearError_eq_of_coefficients_upto (S T : TwoTerm) {N : ℕ}
    (h : ∀ s < N, S.a s = T.a s ∧ S.b s = T.b s ∧ S.gamma s = T.gamma s)
    {d : Type*} (g : (d → ℝ) → d → ℝ) (e0 : d → ℝ) (n : ℕ) (hn : n ≤ N) :
    S.nonlinearError g e0 n = T.nonlinearError g e0 n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rw [nonlinearError, nonlinearError, (h 0 (by omega)).2.2]
  | more n ih0 ih1 =>
    rw [nonlinearError, nonlinearError, ih0 (by omega), ih1 (by omega),
      (h (n+1) (by omega)).1, (h (n+1) (by omega)).2.1, (h (n+1) (by omega)).2.2]

/-- Every finite positive fixed-point method has genuine admissible Jacobi coordinates. -/
theorem exists_finite_jacobi_coordinates (S : TwoTerm) (I : SpectralInterval) {N : ℕ}
    (h : S.PositiveFixedPointUpTo N) :
    ∃ J : JacobiData, (∀ s, 0 ≤ J.aSq s) ∧ J.aSq 0 = 0 ∧
      (∀ s, 0 < s → s < N → 0 < J.aSq s) ∧ J.Admissible I N ∧
      (∀ s < N, (J.method I).a s = S.a s ∧
        (J.method I).b s = S.b s ∧ (J.method I).gamma s = S.gamma s) := by
  let T := S.positiveExtension N
  have hT := S.positiveExtension_positive h
  refine ⟨T.jacobiCoordinates I, T.jacobiCoordinates_aSq_nonneg I hT,
    by simp [jacobiCoordinates], ?_, T.jacobiCoordinates_admissible I hT N, ?_⟩
  · intro s hs _
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
    exact T.jacobiCoordinates_aSq_pos I hT k
  · intro s hs
    rw [T.jacobiCoordinates_method I hT]
    exact S.positiveExtension_coefficients h s hs

end
end chebyshev1.TwoTerm
