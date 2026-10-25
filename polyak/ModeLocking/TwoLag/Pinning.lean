import polyak.ModeLocking.Regular.Definitions
import polyak.Levels.Program.Pinning

/-! Literal positive six-lag pinning weights for an exact two-lag point. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General Levels

/-- Precisely the six lags displayed in Theorem `exact`. -/
def pinLags (K L : ℕ) : Finset ℤ :=
  {1,1+(L : ℤ),1-(L : ℤ),-(K : ℤ),-(K : ℤ)+(L : ℤ),-(K : ℤ)-(L : ℤ)}

def pinWeight (K : ℕ) (a b ε : ℝ) (n : ℤ) : ℝ :=
  if n=1 then a-2*ε else if n=-(K : ℤ) then b-2*ε else ε

theorem pinLags_nonzero {K L : ℕ} (hK : 2≤K) (hL : K+2≤L) :
    ∀ n ∈ pinLags K L, n≠0 := by
  intro n hn
  simp only [pinLags, Finset.mem_insert, Finset.mem_singleton] at hn
  omega

theorem pinLags_card {K L : ℕ} (hK : 2≤K) (hL : K+2≤L) :
    (pinLags K L).card=6 := by
  simp (disch := (simp only [Finset.mem_insert, Finset.mem_singleton]; omega))
    only [pinLags, Finset.card_insert_of_notMem, Finset.card_singleton]

theorem pinWeight_positive (K : ℕ)
    {a b ε : ℝ} (hε : 0<ε) (ha : 2*ε<a) (hb : 2*ε<b) :
    ∀ n, 0<pinWeight K a b ε n := by
  intro n
  unfold pinWeight
  split_ifs <;> linarith

/-- Weighted sum, usable for lags, derivatives, class sums, or moments. -/
theorem pinWeight_sum {K L : ℕ} (hK : 2≤K) (hL : K+2≤L)
    (a b ε : ℝ) (f : ℤ→ℝ) :
    (∑ n ∈ pinLags K L, pinWeight K a b ε n*f n) =
      a*f 1+b*f (-(K : ℤ))+ε*(
        f (1+(L : ℤ))+f (1-(L : ℤ))-2*f 1+
        f (-(K : ℤ)+(L : ℤ))+f (-(K : ℤ)-(L : ℤ))-2*f (-(K : ℤ))) := by
  have hK' : (2 : ℤ)≤K := by exact_mod_cast hK
  have hL' : (K : ℤ)+2≤L := by exact_mod_cast hL
  simp (disch := (simp only [Finset.mem_insert, Finset.mem_singleton]; omega))
    only [pinLags, Finset.sum_insert, Finset.sum_singleton]
  simp only [pinWeight,
    show (1 : ℤ) ≠ -(K : ℤ) by omega,
    show (1+(L : ℤ)) ≠ 1 by omega,
    show (1+(L : ℤ)) ≠ -(K : ℤ) by omega,
    show (1-(L : ℤ)) ≠ 1 by omega,
    show (1-(L : ℤ)) ≠ -(K : ℤ) by omega,
    show -(K : ℤ) ≠ 1 by omega,
    show (-(K : ℤ)+(L : ℤ)) ≠ 1 by omega,
    show (-(K : ℤ)+(L : ℤ)) ≠ -(K : ℤ) by omega,
    show (-(K : ℤ)-(L : ℤ)) ≠ 1 by omega,
    show (-(K : ℤ)-(L : ℤ)) ≠ -(K : ℤ) by omega,
    ite_false, ite_true]
  ring


theorem pinWeight_normalized {K L : ℕ} (hK : 2≤K) (hL : K+2≤L)
    {a b ε : ℝ} (hab : a+b=1) :
    (∑ n ∈ pinLags K L, pinWeight K a b ε n)=1 := by
  have h := pinWeight_sum hK hL a b ε (fun _=>1)
  simpa only [mul_one, show (1 : ℝ)+1-2+1+1-2=0 by norm_num,
    mul_zero, add_zero, hab] using h

/-- The grid values are preserved exactly, for the original shifted curve. -/
theorem pinning_grid_value {K L : ℕ} (hK : 2≤K) (hL : K+2≤L)
    (q : Tuning) (s a b ε : ℝ) (ω : Frequency) (hω : ω∈periodicGrid L) :
    finiteSymbol q s (pinLags K L) (pinWeight K a b ε) ω =
      a*(Geometry.shiftedCurve q s).lag 1 ω+
        b*(Geometry.shiftedCurve q s).lag (-(K : ℤ)) ω := by
  rw [finiteSymbol_actual, pinWeight_sum hK hL]
  have hp (r : ℤ) : (Geometry.shiftedCurve q s).lag (r+(L : ℤ)) ω =
      (Geometry.shiftedCurve q s).lag r ω := by
    simpa using lag_add_mul_grid (Geometry.shiftedCurve q s) hω r 1
  have hm (r : ℤ) : (Geometry.shiftedCurve q s).lag (r-(L : ℤ)) ω =
      (Geometry.shiftedCurve q s).lag r ω := by
    simpa [sub_eq_add_neg] using lag_add_mul_grid (Geometry.shiftedCurve q s) hω r (-1)
  rw [hp 1, hm 1, hp (-(K : ℤ)), hm (-(K : ℤ))]
  ring

/-- Each symmetric pair of lifts cancels its change to the first jet. -/
theorem symmetric_grid_jet {θ : ℝ→ℝ} {θ' : ℝ} {L : ℕ} {ω : Frequency}
    (hθ : HasDerivAt θ θ' (ω : ℝ)) (hω : ω∈periodicGrid L) (r : ℤ) :
    deriv (Geometry.extendedLag θ (r+(L : ℤ))) ω+
      deriv (Geometry.extendedLag θ (r-(L : ℤ))) ω-
      2*deriv (Geometry.extendedLag θ r) ω=0 := by
  have hp := pinning_derivative hθ hω r 1
  have hm := pinning_derivative hθ hω r (-1)
  simp only [one_mul, neg_one_mul, Int.cast_one, Int.cast_neg] at hp hm
  change deriv (Geometry.extendedLag θ (r+(L : ℤ))) ω=_ at hp
  change deriv (Geometry.extendedLag θ (r-(L : ℤ))) ω=_ at hm
  rw [hp, hm]
  unfold Geometry.extendedLag
  ring


theorem pinning_endpoint_moment {K L : ℕ} (hK : 2≤K) (hL : K+2≤L)
    (a b ε τ : ℝ) :
    (∑ n ∈ pinLags K L, pinWeight K a b ε n*(n : ℝ)*((n : ℝ)+2*τ)) =
      a*(1+2*τ)+b*(K : ℝ)*((K : ℝ)-2*τ)+4*ε*(L : ℝ)^2 := by
  simp_rw [mul_assoc]
  rw [pinWeight_sum hK hL]
  push_cast
  ring

theorem pinLags_classes {K L : ℕ} (hK : 2≤K) (hL : K+2≤L)
    {n : ℤ} (hn : n∈pinLags K L) :
    n%(L : ℤ)=1 ∨ n%(L : ℤ)=(L : ℤ)-K := by
  have hLpos : (0 : ℤ)<L := by omega
  have h1 : (1 : ℤ)%(L : ℤ)=1 := Int.emod_eq_of_lt (by omega) (by omega)
  have hKmod : (-(K : ℤ))%(L : ℤ)=(L : ℤ)-K := by
    have he : -(K : ℤ)=((L : ℤ)-K)-(L : ℤ) := by ring
    conv_lhs => rw [he, Int.sub_emod]
    rw [Int.emod_self, sub_zero, Int.emod_emod,
      Int.emod_eq_of_lt (by omega) (by omega)]
  simp only [pinLags, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl|rfl|rfl|rfl|rfl|rfl
  · exact Or.inl h1
  · left; simp [h1]
  · left; simp [h1]
  · exact Or.inr hKmod
  · right; simp [hKmod]
  · right; simp [hKmod]

/-- Both active classes contain distinct lifts, with the exact source lags. -/
theorem pinLags_class_pairs {K L : ℕ} (hK : 2≤K) (hL : K+2≤L)
    {r : ℤ} (hr : r=1 ∨ r=(L : ℤ)-K) :
    ∃ n₁∈pinLags K L, ∃ n₂∈pinLags K L,
      n₁≠n₂ ∧ n₁%(L : ℤ)=r ∧ n₂%(L : ℤ)=r := by
  have hclass (n : ℤ) (hn : n∈pinLags K L) := pinLags_classes hK hL hn
  rcases hr with rfl|rfl
  · refine ⟨1, by simp [pinLags], 1+(L : ℤ), by simp [pinLags], by omega, ?_, ?_⟩
    · exact Int.emod_eq_of_lt (by omega) (by omega)
    · simpa [Int.add_emod] using (Int.emod_eq_of_lt (by omega : (0 : ℤ)≤1) (by omega : (1 : ℤ)<L))
  · refine ⟨-(K : ℤ), by simp [pinLags], -(K : ℤ)+(L : ℤ), by simp [pinLags], by omega, ?_, ?_⟩
    · exact (hclass _ (by simp [pinLags])).resolve_left (by
        intro he
        have hm := Int.emod_eq_of_lt (show (0 : ℤ)≤(L : ℤ)-K by omega)
          (show (L : ℤ)-K<L by omega)
        have hadd := Int.add_emod (-(K : ℤ)) (L : ℤ) (L : ℤ)
        have heq : -(K : ℤ)+(L : ℤ)=(L : ℤ)-K := by ring
        rw [heq, hm] at hadd
        simp only [Int.emod_self, add_zero, Int.emod_emod] at hadd
        omega)
    · apply (hclass _ (by simp [pinLags])).resolve_left
      rw [show -(K : ℤ)+(L : ℤ)=(L : ℤ)-K by ring,
        Int.emod_eq_of_lt (by omega) (by omega)]
      omega


theorem pinningPolynomial_positive {K L : ℕ} {a b ε : ℝ}
    (hε : 0<ε) (ha : 2*ε<a) (hb : 2*ε<b)
    {x : ℝ} (hx : 0<x ∧ x<Real.pi) :
    0<pinningPolynomial (pinLags K L) (pinWeight K a b ε) x := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hc : Real.cos x<1 := by
    nlinarith [Real.sin_sq_add_cos_sq x, sq_pos_of_pos hs, Real.cos_le_one x]
  have hmem : (1 : ℤ)∈pinLags K L := by simp [pinLags]
  have hl := Finset.single_le_sum (s := pinLags K L)
    (f := fun n : ℤ=>pinWeight K a b ε n*(1-Real.cos ((n : ℝ)*x)))
    (fun n _=>mul_nonneg (pinWeight_positive K hε ha hb n).le
      (sub_nonneg.mpr (Real.cos_le_one _))) hmem
  have hp : 0<pinWeight K a b ε 1*(1-Real.cos ((1 : ℤ)*x)) := by
    apply mul_pos (pinWeight_positive K hε ha hb 1)
    simpa using sub_pos.mpr hc
  exact lt_of_lt_of_le hp hl

end polyak.ModeLocking.TwoLag
