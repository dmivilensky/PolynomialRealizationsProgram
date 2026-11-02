import krylov.Asymptotics.RecoveryCompact

/-!
Article: main_krylov, lower bound in thm:limit.
Use: the actual recovery strings also approximate the continuum Christoffel
energy uniformly to first order. The proof controls the genuine right-sampled
mass increments and derives every constant from compact C¹ regularity.
Source: the mean value inequality and discrete Grönwall; no convergence or
quadrature-error certificate is assumed.
-/
namespace krylov.Asymptotics
noncomputable section
open Real Set

/-- The right-endpoint version of the genuine Taylor increment estimate. -/
theorem right_increment_bound_within {f d : ℝ → ℝ} {a b L : ℝ}
    (hab : a ≤ b) (hL : 0 ≤ L)
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (d x) (Icc a b) x)
    (hLip : ∀ x ∈ Icc a b, |d x - d b| ≤ L * |x - b|) :
    |f b - f a - (b - a) * d b| ≤ L * (b - a) ^ 2 := by
  let F : ℝ → ℝ := fun x ↦ f x - f a - (x - a) * d b
  have hF (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivWithinAt F (d x - d b) (Icc a b) x := by
    convert ((hd x hx).sub_const (f a)).sub
      ((((hasDerivAt_id x).sub_const a).mul_const (d b)).hasDerivWithinAt) using 1
    · rfl
    · simp only [one_mul]
  have hbound (x : ℝ) (hx : x ∈ Icc a b) : ‖d x - d b‖ ≤ L * (b - a) := by
    rw [Real.norm_eq_abs]
    apply (hLip x hx).trans
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
    exact mul_le_mul_of_nonneg_left (by linarith [hx.1]) hL
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hF hbound (convex_Icc a b)
    (show a ∈ Icc a b from ⟨le_rfl, hab⟩) (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
  simpa only [F, sub_self, zero_mul, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hab), pow_two, mul_assoc] using h

/-- First-order convergence of the actual recovery Christoffel energies on
every compact type interval, with a constant proved from the true C¹ state. -/
theorem exists_recovery_energy_error_bound {v φ p K : ℝ → ℝ} {Y : ℝ} (hY : 0 < Y)
    (hv : ∀ y ∈ Icc 0 Y, 0 < v y)
    (hcv : ContDiffOn ℝ 1 v (Icc 0 Y))
    (hcφ : ContDiffOn ℝ 1 φ (Icc 0 Y)) (hcp : ContDiffOn ℝ 1 p (Icc 0 Y))
    (hφ₀ : φ 0 = 1) (hp₀ : p 0 = 1) (hK₀ : K 0 = 1)
    (hφ : ∀ y ∈ Icc 0 Y, HasDerivWithinAt φ ((v y)⁻¹ * p y) (Icc 0 Y) y)
    (hp : ∀ y ∈ Icc 0 Y, HasDerivWithinAt p (v y * φ y) (Icc 0 Y) y)
    (hK : ∀ y ∈ Icc 0 Y, HasDerivWithinAt K (v y * φ y ^ 2) (Icc 0 Y) y) :
    ∃ C > (0 : ℝ), ∀ (h : ℝ) (hh : 0 < h), h ≤ 1 → ∀ N : ℕ, ∀ hNY : (N : ℝ) * h ≤ Y,
      ∀ j ≤ N, let S := recoveryString v hh N hNY hv
      |S.K j - K ((j : ℝ) * h)| ≤ C * h := by
  obtain ⟨C, hC, hstate⟩ := exists_recovery_state_error_bound hY hv hcv hcφ hcp hφ₀ hp₀ hφ hp
  let F : Fin 3 → ℝ → ℝ := ![v, φ, (fun y ↦ v y * φ y ^ 2)]
  have hF : ∀ i, ContDiffOn ℝ 1 (F i) (Icc 0 Y) := by
    intro i
    fin_cases i
    · exact hcv
    · exact hcφ
    · exact hcv.mul (hcφ.pow 2)
  obtain ⟨M, hM, hbound⟩ := compact_C1_family_bounds hF
  let A := M * (C * (2 * M + C)) + M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A * Y + 1, by positivity, ?_⟩
  intro h hh hh₁ N hNY j hj
  let S := recoveryString v hh N hNY hv
  have hrec (k : ℕ) (hk : k < N) :
      |S.K (k + 1) - K (((k + 1 : ℕ) : ℝ) * h)| ≤
        (1 + 0 * h) * |S.K k - K ((k : ℝ) * h)| + A * h ^ 2 := by
    let a := (k : ℝ) * h
    let b := ((k : ℝ) + 1) * h
    have ha : a ∈ Icc 0 Y := grid_mem hh.le hNY hk.le
    have hb : b ∈ Icc 0 Y := by
      simpa only [b, Nat.cast_succ] using grid_mem hh.le hNY (Nat.succ_le_of_lt hk)
    have hab : a ≤ b := by dsimp [a, b]; nlinarith
    have hba : b - a = h := by dsimp [a, b]; ring
    have hsub : Icc a b ⊆ Icc 0 Y := fun x hx ↦ ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
    have htaylor := right_increment_bound_within hab hM
      (fun x hx ↦ (hK x (hsub hx)).mono hsub)
      (fun x hx ↦ (hbound 2).2 x (hsub hx) b hb)
    change |K b - K a - (b - a) * (v b * φ b ^ 2)| ≤ M * (b - a) ^ 2 at htaylor
    rw [hba] at htaylor
    have hpair := hstate h hh hh₁ N hNY (k + 1) (Nat.succ_le_of_lt hk)
    have hφerr : |S.φ (k + 1) - φ b| ≤ C * h := by
      have := (norm_fst_le ((S.φ (k + 1), S.p (k + 1)) -
        (φ (((k + 1 : ℕ) : ℝ) * h), p (((k + 1 : ℕ) : ℝ) * h)))).trans hpair
      simpa only [Prod.fst_sub, Real.norm_eq_abs, Nat.cast_add, Nat.cast_one, b, S] using this
    have hφb : |φ b| ≤ M := (hbound 1).1 b hb
    have hvb : |v b| ≤ M := (hbound 0).1 b hb
    have hsum : |S.φ (k + 1) + φ b| ≤ 2 * M + C := by
      calc
        |S.φ (k + 1) + φ b| = |(S.φ (k + 1) - φ b) + 2 * φ b| := by congr 1; ring
        _ ≤ |S.φ (k + 1) - φ b| + |2 * φ b| := abs_add_le _ _
        _ ≤ C * h + 2 * M := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; gcongr
        _ ≤ 2 * M + C := by nlinarith
    have hsquare : |S.φ (k + 1) ^ 2 - φ b ^ 2| ≤ C * (2 * M + C) * h := by
      rw [sq_sub_sq, abs_mul]
      calc
        _ ≤ (2 * M + C) * (C * h) := mul_le_mul hsum hφerr (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hmass : |h * v b * (S.φ (k + 1) ^ 2 - φ b ^ 2)| ≤
        M * (C * (2 * M + C)) * h ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_pos hh]
      calc
        _ ≤ h * M * (C * (2 * M + C) * h) := by gcongr
        _ = _ := by ring
    have hstep := recoveryString_energy_step v hh N hNY hv k
    change S.K (k + 1) = S.K k + h * v b * S.φ (k + 1) ^ 2 at hstep
    simp only [zero_mul, add_zero, one_mul, Nat.cast_add, Nat.cast_one]
    change |S.K (k + 1) - K b| ≤ |S.K k - K a| + A * h ^ 2
    rw [hstep]
    calc
      _ = |(S.K k - K a) + h * v b * (S.φ (k + 1) ^ 2 - φ b ^ 2) -
          (K b - K a - h * (v b * φ b ^ 2))| := by congr 1; ring
      _ ≤ |S.K k - K a| + |h * v b * (S.φ (k + 1) ^ 2 - φ b ^ 2)| +
          |K b - K a - h * (v b * φ b ^ 2)| := by
        calc
          _ ≤ |(S.K k - K a) + h * v b * (S.φ (k + 1) ^ 2 - φ b ^ 2)| +
              |K b - K a - h * (v b * φ b ^ 2)| := abs_sub _ _
          _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ |S.K k - K a| + A * h ^ 2 := by dsimp [A]; nlinarith [hmass, htaylor]
  have hfinal := finite_grid_gronwall hA (by norm_num : (0 : ℝ) ≤ 0) hh.le hNY
    (e := fun k ↦ |S.K k - K ((k : ℝ) * h)|)
    (by simp [hK₀, S]) (fun _ _ ↦ abs_nonneg _) hrec hj
  simp only [zero_mul, exp_zero, mul_one] at hfinal
  exact hfinal.trans (by nlinarith)

end
end krylov.Asymptotics
