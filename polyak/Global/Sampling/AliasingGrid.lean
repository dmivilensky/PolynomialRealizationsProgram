import polyak.Global.Circle.Basic
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.PSeries

/-! Actual equally spaced points of the original circle and the exact
orthogonality identity, for arbitrary composite periods. -/
noncomputable section
namespace polyak.Global.Sampling
open Set Complex

def samplePoint (L : ℕ) (j : Fin L) : Circle:=Circle.ofReal (2*Real.pi*j.val/L)

def sampleAverage (h : C(Circle,ℂ)) (L : ℕ) (n : ℤ) : ℂ :=
  (L:ℂ)⁻¹*∑j : Fin L,h (samplePoint L j)*fourier n (samplePoint L j)

theorem fourier_samplePoint {L : ℕ} [NeZero L] (hL : 0<L) (m : ℤ) (j : Fin L) :
    fourier m (samplePoint L j)=
      ZMod.stdAddChar ((m:ZMod L)*(j.val:ZMod L)) := by
  have : NeZero L:=⟨hL.ne'⟩
  change fourier m ((2*Real.pi*j.val/L:ℝ):Circle)=_
  rw [fourier_coe_apply]
  have he : (m:ZMod L)*(j.val:ZMod L)=((m*(j.val:ℤ):ℤ):ZMod L):=by push_cast; rfl
  rw [he,ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp [show (L:ℂ)≠0 by exact_mod_cast hL.ne',Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

theorem sum_fourier_samplePoint {L : ℕ} (hL : 0<L) (m : ℤ) :
    (∑j : Fin L,fourier m (samplePoint L j))=
      if (L:ℤ)∣m then (L:ℂ) else 0 := by
  have : NeZero L:=⟨hL.ne'⟩
  have he : (∑j : Fin L,fourier m (samplePoint L j))=
      ∑j : ZMod L,ZMod.stdAddChar ((m:ZMod L)*j) := by
    apply Fintype.sum_equiv (ZMod.finEquiv L).toEquiv
    intro j
    rw [fourier_samplePoint hL]
    cases L with
    | zero => omega
    | succ L =>
      congr 1
      congr 1
      exact Fin.natCast_eq_mk j.isLt
  rw [he]
  by_cases hm : (m:ZMod L)=0
  · have hd : (L:ℤ)∣m:= (ZMod.intCast_zmod_eq_zero_iff_dvd m L).mp hm
    simp only [hm,zero_mul,AddChar.map_zero_eq_one,Finset.sum_const,Finset.card_univ,ZMod.card,
      nsmul_eq_mul,mul_one,ite_eq_left hd]
  · have hd : ¬(L:ℤ)∣m:=fun hh=>hm ((ZMod.intCast_zmod_eq_zero_iff_dvd m L).mpr hh)
    rw [ite_eq_right hd]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar L hm)

theorem average_fourier_samplePoint {L : ℕ} (hL : 0<L) (m : ℤ) :
    (L:ℂ)⁻¹*(∑j : Fin L,fourier m (samplePoint L j))=
      if (L:ℤ)∣m then 1 else 0 := by
  rw [sum_fourier_samplePoint hL]
  split_ifs
  · exact inv_mul_cancel₀ (by exact_mod_cast hL.ne')
  · simp only [mul_zero]

theorem sampleAverage_periodic (h : C(Circle,ℂ)) {L : ℕ} (hL : 0<L) (n m : ℤ) :
    sampleAverage h L (n+m*L)=sampleAverage h L n := by
  have : NeZero L:=⟨hL.ne'⟩
  unfold sampleAverage
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [fourier_add]
  have he : fourier (m*L) (samplePoint L j)=1 := by
    rw [fourier_samplePoint hL]
    simp only [Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,mul_zero,zero_mul,AddChar.map_zero_eq_one]
  rw [he,mul_one]

end polyak.Global.Sampling
