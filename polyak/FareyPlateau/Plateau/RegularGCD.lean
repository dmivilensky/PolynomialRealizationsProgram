import polyak.ModeLocking.Regular.Endpoints
import Mathlib.Algebra.GCDMonoid.Finset

/-! A strict regular certificate cannot have a nonprimitive common lag
divisor: its first common Fourier zero would violate strictness or pinning. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels ModeLocking Set
open scoped BigOperators

theorem regular_lags_gcd_one {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L) :
    D.lags.gcd id=1 := by
  classical
  let g : ℤ := D.lags.gcd id
  have hnon : D.lags.Nonempty := by
    by_contra hn
    have he : D.lags=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hh := D.dual_sum
    simp only [he,Finset.sum_empty] at hh
    norm_num at hh
  have hg0 : g≠0 := by
    intro he
    obtain ⟨n,hn⟩ := hnon
    have hd : g∣n := Finset.gcd_dvd hn
    rw [he,zero_dvd_iff] at hd
    exact D.lags_nonzero n hn hd
  have hgn : 0≤g := Finset.Int.finsetGcd_nonneg
  by_contra hg1
  have hg2 : 2≤g := by change g≠1 at hg1; omega
  have hgr : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  let x : ℝ := 2*Real.pi/g
  have hxp : 0<x := by dsimp [x]; positivity
  have hxπ : x≤Real.pi := by
    dsimp [x]
    apply (div_le_iff₀ hgr).mpr
    have hh : (2:ℝ)≤g := by exact_mod_cast hg2
    nlinarith [Real.pi_pos]
  have hphase (n:ℤ) (hn:n∈D.lags) : ∃m:ℤ,(n:ℝ)*x=(m:ℝ)*(2*Real.pi) := by
    obtain ⟨m,hm⟩ := (show g∣n from Finset.gcd_dvd hn)
    refine ⟨m,?_⟩
    rw [hm]
    push_cast
    dsimp [x]
    field_simp
  have hP : pinningPolynomial D.lags D.dual x=0 := by
    unfold pinningPolynomial
    apply Finset.sum_eq_zero
    intro n hn
    obtain ⟨m,hm⟩ := hphase n hn
    rw [hm,Real.cos_int_mul_two_pi]
    ring
  have hT : finiteSymbol q s D.lags D.dual x=0 := by
    unfold finiteSymbol
    apply Finset.sum_eq_zero
    intro n hn
    obtain ⟨m,hm⟩ := hphase n hn
    unfold lagExtension Geometry.extendedLag
    rw [hm,Real.cos_int_mul_two_pi_sub]
    ring
  by_cases hsupport : ∃i,D.atoms i=⟨x,hxp.le,hxπ⟩
  · obtain ⟨i,hi⟩ := hsupport
    have hp := D.pinning_pos i
    rw [hi] at hp
    change 0<pinningPolynomial D.lags D.dual x at hp
    rw [hP] at hp
    exact lt_irrefl _ hp
  · have hn : ∀i,x≠(D.atoms i:ℝ) := by
      intro i he
      apply hsupport
      exact ⟨i,Subtype.ext he.symm⟩
    have ht := D.dual_strict x hxp hxπ hn
    rw [hT] at ht
    exact lt_irrefl _ ht

end polyak.FareyPlateau
