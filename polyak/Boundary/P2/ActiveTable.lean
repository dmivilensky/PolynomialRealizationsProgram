import polyak.Boundary.Active
import polyak.Boundary.P2.Arc

/-! Article: the exact active table on the open rational P2 regime. -/
noncomputable section
namespace polyak.Boundary.P2

theorem signedRaw_inactive_pos {z t : ℝ} (hz : z∈parameterInterval) (h1 : zeta1≤z)
    (ha : z<zetaA) (ht : Real.cosh t=G z) {n : ℕ} (hn : 1≤n)
    {σ : ℝ} (hσ : σ= -1 ∨ σ=1) (hinactive : ¬ThreeActive n σ) :
    0<signedRawLag (spectrum z hz h1) (u z) t (d z/Real.sinh t) n σ := by
  rcases hσ with rfl | rfl
  · have hn1 : n≠1 := by rintro rfl; exact hinactive (Or.inl ⟨rfl,rfl⟩)
    simpa [signedRawLag,sub_eq_add_neg] using lower_strict hz h1 ht n (by omega)
  · have hn2 : n≠2 := by rintro rfl; exact hinactive (Or.inr ⟨Or.inl rfl,rfl⟩)
    have hn3 : n≠3 := by rintro rfl; exact hinactive (Or.inr ⟨Or.inr rfl,rfl⟩)
    by_cases hn5 : n=5
    · subst n
      simpa [signedRawLag] using upper5_strict_before hz h1 ha ht
    · simpa [signedRawLag] using upper_strict hz h1 ht n hn hn2 hn3 hn5

theorem signedRaw_active_iff {z t : ℝ} (hz : z∈parameterInterval) (h1 : zeta1≤z)
    (ha : z<zetaA) (ht : Real.cosh t=G z) {n : ℕ} (hn : 1≤n)
    {σ : ℝ} (hσ : σ= -1 ∨ σ=1) :
    signedRawLag (spectrum z hz h1) (u z) t (d z/Real.sinh t) n σ=0 ↔ ThreeActive n σ := by
  constructor
  · intro he
    by_contra hna
    exact (signedRaw_inactive_pos hz h1 ha ht hn hσ hna).ne' he
  · intro hactive
    obtain ⟨hl,hu2,hu3⟩ := active_constraints hz h1 ht
    rcases hactive with ⟨rfl,rfl⟩ | ⟨hn23,rfl⟩
    · simpa [signedRawLag,sub_eq_add_neg] using hl
    · rcases hn23 with rfl | rfl
      · simpa [signedRawLag] using hu2
      · simpa [signedRawLag] using hu3

end polyak.Boundary.P2
