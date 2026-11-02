import jacobi.Oscillation.CosineGap
import Mathlib.Order.Fin.Basic

/-!
Article: jacobi, Proposition B.1.
Positive consecutive angular gaps and positive extreme endpoint distances
imply the complete index-weighted node separation scale. The argument
uses monotonicity of angle_i-d*i/N, so no summation or ordering of
arbitrarily selected roots is hidden in the conversion.
Use: sums all actual consecutive Jacobi gaps without changing the source zero enumeration.
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set

/-- Subtracting a uniform linear index slope makes any genuinely separated finite angle list monotone.
Use: sums all actual consecutive Jacobi gaps without changing the source zero enumeration.
Article: jacobi, Proposition B.1.
Proof: check the difference at every finite successor and use the community finite monotonicity theorem. -/
theorem subtract_index_monotone {n : ℕ} {f : Fin n → ℝ} {d N : ℝ}
    (hgap : ∀ k : ℕ,∀ hk : k+1<n,d/N≤f ⟨k+1,hk⟩-f ⟨k,by omega⟩) :
    Monotone (fun i : Fin n => f i-d*(i.val:ℝ)/N) := by
  -- The finite successor criterion sums the actual gaps after subtracting the exact linear index slope.
  cases n with
  | zero => intro i; exact i.elim0
  | succ n =>
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have h := hgap i.val (by omega)
    change d/N≤f i.succ-f i.castSucc at h
    simp only [Fin.val_castSucc,Fin.val_succ,Nat.cast_add,Nat.cast_one]
    have he : d*((i.val:ℝ)+1)/N=d*(i.val:ℝ)/N+d/N := by ring
    rw [he]
    linarith

/-- Uniform true endpoint distances and consecutive angular gaps give all full-index endpoint distances and pairwise angular separations.
Use: converts the genuine finite Jacobi geometry to the sum- and difference-of-indices scale in Proposition B.1 (c).
Article: jacobi, Proposition B.1.
Proof: the corrected list f_i-d*i/N is monotone. Compare each index
with the first and last original indices for its two endpoint bounds,
and compare any two original indices for their full angular difference. -/
theorem nodal_geometry {n : ℕ} (hn : 0<n) {f : Fin n → ℝ} {d N : ℝ}
    (hfirst : d/N≤f ⟨0,hn⟩) (hlast : d/N≤Real.pi-f ⟨n-1,by omega⟩)
    (hgap : ∀ k : ℕ,∀ hk : k+1<n,d/N≤f ⟨k+1,hk⟩-f ⟨k,by omega⟩) :
    (∀ i : Fin n,d*(i.val+1:ℝ)/N≤f i ∧ d*((n-i.val:ℕ):ℝ)/N≤Real.pi-f i) ∧
      ∀ i j : Fin n,i≤j → d*((j.val-i.val:ℕ):ℝ)/N≤f j-f i := by
  -- Finite monotonicity telescopes exactly the source's original ordered indices.
  have hm := subtract_index_monotone hgap
  constructor
  · intro i
    have hi0 := hm (show (⟨0,hn⟩ : Fin n)≤ i from Nat.zero_le _)
    have hil := hm (show i≤(⟨n-1,by omega⟩ : Fin n) by exact show i.val≤n-1 by omega)
    simp only [Nat.cast_zero,mul_zero,zero_div,sub_zero] at hi0
    change f i-d*(i.val:ℝ)/N≤f ⟨n-1,by omega⟩-d*((n-1:ℕ):ℝ)/N at hil
    have hn0 : 1≤n := hn
    rw [Nat.cast_sub hn0,Nat.cast_one] at hil
    have hiN : i.val≤n := i.isLt.le
    rw [Nat.cast_sub hiN]
    constructor
    · have he : d*(i.val+1:ℝ)/N=d*(i.val:ℝ)/N+d/N := by ring
      rw [he]
      linarith
    · have he : d*((n:ℝ)-i.val)/N=d*((n:ℝ)-1)/N-d*(i.val:ℝ)/N+d/N := by ring
      rw [he]
      linarith
  · intro i j hij
    have hh := hm hij
    have hnij : i.val≤j.val := hij
    rw [Nat.cast_sub hnij]
    have he : d*((j.val:ℝ)-i.val)/N=d*(j.val:ℝ)/N-d*(i.val:ℝ)/N := by ring
    rw [he]
    linarith

end
end jacobi.Oscillation
