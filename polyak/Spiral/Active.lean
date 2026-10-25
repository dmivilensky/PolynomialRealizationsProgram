import polyak.Boundary.Active
import polyak.Spiral.Feasibility

/-! Article: the exact active table of the noncritical special spiral. -/
noncomputable section
namespace polyak.Spiral
open Boundary

theorem signedRaw_inactive_pos {t : ℝ} (ht : t≠0) {n : ℕ} (hn : 1≤n)
    {σ : ℝ} (hσ : σ= -1 ∨ σ=1) (hinactive : ¬ThreeActive n σ) :
    0<signedRawLag (spectrum t) (twist t) t (valueConstant t) n σ := by
  rcases hσ with rfl | rfl
  · have hn1 : n≠1 := by rintro rfl; exact hinactive (Or.inl ⟨rfl,rfl⟩)
    simpa [signedRawLag,sub_eq_add_neg] using mean_lower_pos ht n (by omega)
  · have hn2 : n≠2 := by rintro rfl; exact hinactive (Or.inr ⟨Or.inl rfl,rfl⟩)
    have hn3 : n≠3 := by rintro rfl; exact hinactive (Or.inr ⟨Or.inr rfl,rfl⟩)
    by_cases hn1 : n=1
    · subst n
      simpa [signedRawLag] using mean_upper_one_pos t
    · simpa [signedRawLag] using mean_upper_pos ht n (by omega)

theorem signedRaw_active_iff {t : ℝ} (ht : t≠0) {n : ℕ} (hn : 1≤n)
    {σ : ℝ} (hσ : σ= -1 ∨ σ=1) :
    signedRawLag (spectrum t) (twist t) t (valueConstant t) n σ=0 ↔ ThreeActive n σ := by
  constructor
  · intro he
    by_contra hna
    exact (signedRaw_inactive_pos ht hn hσ hna).ne' he
  · intro hactive
    rcases hactive with ⟨rfl,rfl⟩ | ⟨hn23,rfl⟩
    · simpa [signedRawLag,sub_eq_add_neg] using lower_one_zero t
    · rcases hn23 with rfl | rfl
      · simpa [signedRawLag] using upper_two_zero t
      · simpa [signedRawLag] using upper_three_zero t

end polyak.Spiral
