import polyak.ModeLocking.Localization.Potential

/-! Exact arithmetic separation of distinct rational-grid frequencies. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels

private theorem grid_refinement {L M : ℕ} (h : L ∣ M) {ω : Frequency}
    (hω : ω ∈ periodicGrid L) : ω ∈ periodicGrid M := by
  obtain ⟨m,rfl⟩ := h
  obtain ⟨hpos,j,hj⟩ := hω
  refine ⟨hpos,(m:ℤ)*j,?_⟩
  push_cast
  nlinarith [congrArg (fun x : ℝ => (m:ℝ)*x) hj]

theorem rational_grid_distance {L M : ℕ} (hL : 0 < L) (hM : 0 < M)
    {x y : Frequency} (hx : x ∈ periodicGrid L) (hy : y ∈ periodicGrid M) (hne : x ≠ y) :
    2*Real.pi/(Nat.lcm L M:ℝ) ≤ |(x:ℝ)-(y:ℝ)| := by
  have hp : 0 < (Nat.lcm L M:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hL.ne' hM.ne')
  obtain ⟨_,j,hj⟩ := grid_refinement (Nat.dvd_lcm_left L M) hx
  obtain ⟨_,k,hk⟩ := grid_refinement (Nat.dvd_lcm_right L M) hy
  have hjk : j-k ≠ 0 := by
    intro he
    have hc : (x:ℝ)=(y:ℝ) := by
      have hcast : (j:ℝ)=(k:ℝ) := by exact_mod_cast sub_eq_zero.mp he
      rw [hcast] at hj
      nlinarith
    exact hne (Subtype.ext hc)
  have ha : (1:ℝ) ≤ |((j-k:ℤ):ℝ)| := by
    have hn : 1 ≤ (j-k).natAbs := Int.natAbs_pos.mpr hjk
    have hh : (1:ℝ) ≤ ((j-k).natAbs:ℝ) := by exact_mod_cast hn
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hh
  have he : (Nat.lcm L M:ℝ)*((x:ℝ)-(y:ℝ)) = ((j-k:ℤ):ℝ)*(2*Real.pi) := by
    push_cast
    nlinarith only [hj,hk]
  have hab := congrArg abs he
  rw [abs_mul,abs_mul,abs_of_pos hp,abs_of_pos (by positivity : 0<2*Real.pi)] at hab
  apply (div_le_iff₀ hp).mpr
  nlinarith [Real.pi_pos]

end polyak.ModeLocking.Localization
