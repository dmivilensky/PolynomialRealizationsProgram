import polyak.ModeLocking.Regular.Kernel

/-! The automatic pinning clause after Definition `def:regular`. Its proof
uses only the positive one-dimensional primal kernel, positive lag weights,
and occurrence of every tight residue class in the lag set. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels
open scoped BigOperators

theorem no_zero_column_of_positive_kernel {d : ℕ} (hd : 2 ≤ d)
    (M : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i)
    (hk : ∀ v, M.mulVec v = 0 → ∃ c : ℝ, ∀ i, v i = c * w i) (i : Fin d) :
    ∃ r, M r i ≠ 0 := by
  classical
  by_contra hn
  have hcol : ∀ r, M r i = 0 := by simpa only [not_exists, not_not] using hn
  let j : Fin d := if i = ⟨0, by omega⟩ then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hji : j ≠ i := by
    dsimp [j]
    split_ifs with hi
    · subst i
      intro he
      have hh := congrArg Fin.val he
      norm_num at hh
    · exact Ne.symm hi
  have he : M.mulVec (Pi.single i 1) = 0 := by
    funext r
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using hcol r
  obtain ⟨c, hc⟩ := hk (Pi.single i 1) he
  have hj := hc j
  have hz : c = 0 := by
    have hh : c * w j = 0 := by simpa only [Pi.single_eq_of_ne hji] using hj.symm
    exact (mul_eq_zero.mp hh).resolve_right (hw j).ne'
  have hi := hc i
  simp only [Pi.single_eq_same, hz, zero_mul, one_ne_zero] at hi

theorem lag_zero_of_pinning_zero (Θ : Curve) (N : Finset ℤ) (a : ℤ → ℝ)
    (ha : ∀ n ∈ N, 0 < a n) (ω : Frequency)
    (hP : pinningPolynomial N a ω = 0) : ∀ n ∈ N, Θ.lag n ω = 0 := by
  have hterms : ∀ n ∈ N, a n * (1 - Real.cos ((n : ℝ) * (ω : ℝ))) = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun n hn =>
      mul_nonneg (ha n hn).le (sub_nonneg.mpr (Real.cos_le_one _)))).mp hP
  intro n hn
  have hc : Real.cos ((n : ℝ) * (ω : ℝ)) = 1 := by
    have hh := (mul_eq_zero.mp (hterms n hn)).resolve_left (ha n hn).ne'
    linarith
  have hs : Real.sin ((n : ℝ) * (ω : ℝ)) = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq ((n : ℝ) * (ω : ℝ))]
  rw [Curve.lag_expand, hc, hs]
  ring

namespace RegularData
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem matrix_column_nonzero (hd : 2 ≤ D.d) (i : Fin D.d) :
    ∃ r, D.matrix r i ≠ 0 :=
  no_zero_column_of_positive_kernel hd D.matrix (fun j => (D.primal j : ℝ))
    (fun j => by exact_mod_cast D.primal_pos j) (fun _ hv => D.kernel_unique hv) i

/-- No dual sign or curvature assumption is used: positive pinning on a
support with at least two atoms follows from the primary primal rank data. -/
theorem pinning_pos_of_two_le (hd : 2 ≤ D.d) (i : Fin D.d) :
    0 < pinningPolynomial D.lags D.dual (D.atoms i) := by
  have hn : 0 ≤ pinningPolynomial D.lags D.dual (D.atoms i) :=
    Finset.sum_nonneg (fun n hn => mul_nonneg (D.dual_pos n hn).le
      (sub_nonneg.mpr (Real.cos_le_one _)))
  by_contra hp
  have hP : pinningPolynomial D.lags D.dual (D.atoms i) = 0 := by linarith
  have hz := lag_zero_of_pinning_zero (Geometry.shiftedCurve q s) D.lags D.dual D.dual_pos
    (D.atoms i) hP
  obtain ⟨r, hr⟩ := D.matrix_column_nonzero hd i
  obtain ⟨n, hn, _, _, _, hclass, _⟩ := D.class_pair r
  apply hr
  change (Geometry.shiftedCurve q s).lag (D.reps r) (D.atoms i) = 0
  rw [← hclass, ← lag_mod_grid (Geometry.shiftedCurve q s) (D.atoms_grid i) n]
  exact hz n hn

end RegularData
end polyak.ModeLocking
