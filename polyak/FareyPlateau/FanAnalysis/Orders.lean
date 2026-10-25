import Mathlib.Data.Int.CharZero
import polyak.FareyPlateau.FanAnalysis.GridArithmetic
import polyak.FareyPlateau.FanAnalysis.Cutoff

/-! Every congruent order gives the actual fan of the article, and both
signed families have unbounded orders. Companion denominators are reduced
exactly and have the source lower bound. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Filter
open scoped Topology

def orderFan (j k L ε : ℤ) (hk : 3 ≤ k) (hL : k < L)
    (hε : ε=1 ∨ ε= -1) (hmod : j*L ≡ ε [ZMOD k]) : Fan.Data where
  j := j
  k := k
  L := L
  J := (j*L-ε)/k
  sign := ε
  period_ge := hk
  order_gt := hL
  sign_unit := hε
  incidence := by
    have hd : k ∣ j*L-ε := by simpa only [neg_sub] using dvd_neg.mpr hmod.dvd
    have he := Int.ediv_mul_cancel hd
    linear_combination he

@[simp] theorem orderFan_J (j k L ε : ℤ) (hk : 3 ≤ k) (hL : k < L)
    (hε : ε=1 ∨ ε= -1) (hmod : j*L ≡ ε [ZMOD k]) :
    (orderFan j k L ε hk hL hε hmod).J=(j*L-ε)/k := rfl

theorem unbounded_orders {j k b ε : ℤ} (hk : 3 ≤ k) (hb : b*j ≡ 1 [ZMOD k])
    (hε : ε=1 ∨ ε= -1) (B : ℤ) :
    ∃P : Fan.Data,P.j=j ∧ P.k=k ∧ P.sign=ε ∧ B<P.L := by
  let m := max B k+|b|+1
  let L := ε*b+k*m
  have hm : 0 < m := by dsimp [m]; have := le_max_right B k; have := abs_nonneg b; omega
  have hLb : max B k<L := by
    have hsign : -|b| ≤ ε*b := by
      rcases hε with rfl|rfl
      · simpa only [one_mul] using neg_abs_le b
      · simpa only [neg_one_mul] using neg_le_neg (le_abs_self b)
    have hmul := mul_le_mul_of_nonneg_right hk hm.le
    dsimp [L,m] at *
    linarith
  have hmod : j*L ≡ ε [ZMOD k] := by
    obtain ⟨z,hz⟩ := hb.dvd
    apply Int.modEq_iff_dvd.mpr
    refine ⟨ε*z-j*m,?_⟩
    dsimp [L]
    linear_combination ε*hz
  exact ⟨orderFan j k L ε hk ((le_max_right B k).trans_lt hLb) hε hmod,rfl,rfl,rfl,
    (le_max_left B k).trans_lt hLb⟩

theorem exists_fan_delta {j k : ℕ} (hk : 3 ≤ k) (b ε : ℤ)
    (hb : b*(j:ℤ) ≡ 1 [ZMOD (k:ℤ)]) (hε : ε=1 ∨ ε= -1)
    {p : ℝ→Prop} (hp : ∀ᶠ δ in 𝓝[≠] 0,p δ) :
    ∃P : Fan.Data,P.j=j ∧ P.k=k ∧ P.sign=ε ∧ p P.delta := by
  obtain ⟨L₀,hL₀⟩ := large_order_small_delta hk hp
  obtain ⟨P,hj,hkP,hs,hPL⟩ := unbounded_orders (by exact_mod_cast hk) hb hε (L₀:ℤ)
  exact ⟨P,hj,hkP,hs,hL₀ P hkP hPL.le⟩

namespace Companion
variable (P : Fan.Data)

def divisor : ℕ := Int.gcd (P.J+P.sign) P.L
def numerator : ℤ := (P.J+P.sign)/(divisor P:ℤ)
def denominator : ℤ := P.L/(divisor P:ℤ)

theorem divisor_pos : 0 < divisor P := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hh := Int.gcd_eq_zero_iff.mp hzero
  have := P.period_ge
  have := P.order_gt
  omega

theorem divisor_dvd_numerator : (divisor P:ℤ) ∣ P.J+P.sign := Int.gcd_dvd_left _ _
theorem divisor_dvd_order : (divisor P:ℤ) ∣ P.L := Int.gcd_dvd_right _ _

theorem denominator_pos : 0 < denominator P := by
  have hL : 0 < P.L := by have := P.period_ge; have := P.order_gt; omega
  have hg : (0:ℤ) < divisor P := by exact_mod_cast divisor_pos P
  have he := Int.ediv_mul_cancel (divisor_dvd_order P)
  change denominator P*(divisor P:ℤ)=P.L at he
  exact pos_of_mul_pos_left (he.symm ▸ hL) hg.le

theorem fraction_eq : (numerator P:ℝ)/(denominator P:ℝ)=(P.J+P.sign:ℤ)/ (P.L:ℝ) := by
  have hn : (numerator P:ℝ)=(P.J+P.sign:ℤ)/(divisor P:ℝ) := by
    rw [numerator,Int.cast_div_charZero (divisor_dvd_numerator P),Int.cast_natCast]
  have hd : (denominator P:ℝ)=(P.L:ℝ)/(divisor P:ℝ) := by
    rw [denominator,Int.cast_div_charZero (divisor_dvd_order P),Int.cast_natCast]
  rw [hn,hd]
  have hg : (divisor P:ℝ) ≠ 0 := by exact_mod_cast (divisor_pos P).ne'
  have hL : (P.L:ℝ) ≠ 0 := by exact_mod_cast (show P.L≠0 by have := P.period_ge; have := P.order_gt; omega)
  field_simp

theorem coprime : IsCoprime (numerator P) (denominator P) :=
  Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_ediv_gcd_ediv_gcd (divisor_pos P))

theorem far_reduced : P.far=2*Real.pi*(numerator P:ℝ)/(denominator P:ℝ) := by
  have hh := fraction_eq P
  unfold Fan.Data.far
  calc
    _ = 2*Real.pi*((P.J+P.sign:ℤ)/(P.L:ℝ)) := by push_cast; ring
    _ = 2*Real.pi*((numerator P:ℝ)/(denominator P:ℝ)) := by rw [hh]
    _ = _ := by ring

theorem divisor_le : (divisor P:ℤ) ≤ P.k-1 :=
  Int.le_of_dvd (by have := P.period_ge; omega) P.companion_gcd_dvd

theorem denominator_lower : (P.L:ℝ)/((P.k:ℝ)-1) ≤ (denominator P:ℝ) := by
  have hg : (0:ℝ) < divisor P := by exact_mod_cast divisor_pos P
  have hk : 0 < (P.k:ℝ)-1 := by
    have hr : (3:ℝ) ≤ P.k := by exact_mod_cast P.period_ge
    linarith
  have hL : 0 ≤ (P.L:ℝ) := by exact_mod_cast (show 0≤P.L by have := P.period_ge; have := P.order_gt; omega)
  rw [denominator,Int.cast_div_charZero (divisor_dvd_order P),Int.cast_natCast]
  exact div_le_div_of_nonneg_left hL hg (by exact_mod_cast divisor_le P)

end Companion
end polyak.FareyPlateau.FanAnalysis
