import polyak.FareyPlateau.Domain.Source
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-! Positivity of the actual trigonometric denominator.  The finite
Bezout identity is the integer certificate of gcd-one support; zero
weights are explicitly excluded from that identity. -/
noncomputable section
namespace polyak.FareyPlateau.Symbols
open Set
open scoped BigOperators
variable {I : Type*} [Fintype I]

def denominator (n : I→ℤ) (w : I→ℝ) (ω : ℝ) : ℝ :=
  ∑i,w i*(1-Real.cos ((n i:ℝ)*ω))

def SupportBezout (n : I→ℤ) (w : I→ℝ) : Prop :=
  ∃z : I→ℤ, (∀i,w i=0 → z i=0) ∧ ∑i,z i*n i=1

theorem denominator_nonneg (n : I→ℤ) (w : I→ℝ)
    (hw : ∀i,0≤w i) (ω : ℝ) : 0≤denominator n w ω := by
  exact Finset.sum_nonneg (fun i _=>mul_nonneg (hw i) (by linarith [Real.cos_le_one ((n i:ℝ)*ω)]))

theorem denominator_pos (n : I→ℤ) (w : I→ℝ)
    (hw : ∀i,0≤w i) (hbez : SupportBezout n w) {ω : ℝ}
    (hω : ω∈Ioc (0:ℝ) Real.pi) : 0<denominator n w ω := by
  rcases hbez with ⟨z,hz,hzsum⟩
  by_contra hbad
  have he : denominator n w ω=0 := le_antisymm (le_of_not_gt hbad) (denominator_nonneg n w hw ω)
  have hzero (i) : w i*(1-Real.cos ((n i:ℝ)*ω))=0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun j _=>
      mul_nonneg (hw j) (by linarith [Real.cos_le_one ((n j:ℝ)*ω)]))).mp he i
    exact Finset.mem_univ i
  have hm (i) : ∃m : ℤ, (z i:ℝ)*((n i:ℝ)*ω)=(z i:ℝ)*((m:ℝ)*(2*Real.pi)) := by
    by_cases hzi : z i=0
    · exact ⟨0,by simp [hzi]⟩
    have hwi : w i≠0 := fun h=>hzi (hz i h)
    have hcos : Real.cos ((n i:ℝ)*ω)=1 := by
      have hterm := (mul_eq_zero.mp (hzero i)).resolve_left hwi
      linarith
    obtain ⟨m,hm⟩ := (Real.cos_eq_one_iff _).mp hcos
    exact ⟨m,by rw [hm]⟩
  choose m hm using hm
  have hs : (∑i,(z i:ℝ)*(n i:ℝ))=1 := by exact_mod_cast hzsum
  have hmul : ω=((∑i,z i*m i:ℤ):ℝ)*(2*Real.pi) := by
    calc
      ω=(∑i,(z i:ℝ)*(n i:ℝ))*ω := by rw [hs]; ring
      _=∑i,(z i:ℝ)*((n i:ℝ)*ω) := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      _=∑i,(z i:ℝ)*((m i:ℝ)*(2*Real.pi)) := Finset.sum_congr rfl (fun i _=>hm i)
      _=_ := by push_cast; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
  have hM : 1≤∑i,z i*m i := by
    by_contra hh
    have hh : ∑i,z i*m i≤0 := by omega
    have hh' : ((∑i,z i*m i:ℤ):ℝ)≤0 := by exact_mod_cast hh
    have hx := mul_nonpos_of_nonpos_of_nonneg hh' (by positivity : 0≤2*Real.pi)
    linarith [hω.1]
  have hM' : (1:ℝ)≤((∑i,z i*m i:ℤ):ℝ) := by exact_mod_cast hM
  have hx := mul_le_mul_of_nonneg_right hM' (by positivity : 0≤2*Real.pi)
  linarith [hω.2,Real.pi_pos]

end polyak.FareyPlateau.Symbols
