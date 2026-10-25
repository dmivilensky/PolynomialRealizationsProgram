import polyak.GapEdges.Junction.AdjacentCoordinates

/-! Full junction curvature criterion for the genuine adjacent symbol.
It covers every nonresonant lag cell, not only the first two fixed lags. -/
noncomputable section
namespace polyak.GapEdges.Junction
open General Levels ModeLocking Set

theorem junction_actual_adjacent_second {q : Tuning} {k : ℕ}
    (A : FareyPlateau.Edge.AdjacentData q 1 k) (hk : 4≤k) {a t₂ : ℝ}
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*(Real.pi/k))) t₂) :
    deriv^[2] A.function (2*Real.pi/k)=
      Real.sin (Real.pi/k)*deriv^[2] (Geometry.shiftedAngle q 0) (2*Real.pi/k)-
        (1/2:ℝ)*Real.cos (Real.pi/k)*(k:ℝ)^2*A.mix*(1-A.mix) := by
  have hh := A.second
  rw [adjacent_frequency_one A] at hh
  rw [show deriv^[2] (TwoLag.phase q A.edgeShift) (2*Real.pi/k)=
    deriv^[2] (Geometry.shiftedAngle q 0) (2*Real.pi/k) from
      (junction_adjacent_phase A hk hXi).deriv.deriv_eq] at hh
  exact hh

theorem adjacent_half_period_ne {q : Tuning} {k : ℕ}
    (A : FareyPlateau.Edge.AdjacentData q 1 k) {g : ℝ}
    (hs : (A.lower:ℝ)+A.mix*k=1-2*g) : g≠(k:ℝ)/2 := by
  intro he
  have hk : (0:ℝ)<k := by exact_mod_cast (show 0<k by have := A.period_ge; omega)
  have hlow := A.lower_class
  rw [adjacent_inverse_one A] at hlow
  have hdiv := Int.emod_add_mul_ediv A.lower (k:ℤ)
  rw [hlow] at hdiv
  have hdivR : (1:ℝ)+(k:ℝ)*(A.lower/(k:ℤ):ℤ)=(A.lower:ℝ) := by exact_mod_cast hdiv
  rw [he] at hs
  have hleft : (A.lower/(k:ℤ):ℤ)< -1 := by
    by_contra hh
    have hz : (-1:ℝ)≤(A.lower/(k:ℤ):ℤ) := by exact_mod_cast (le_of_not_gt hh)
    have hp := mul_pos hk A.mix_pos
    nlinarith
  have hright : -2<(A.lower/(k:ℤ):ℤ) := by
    by_contra hh
    have hz : ((A.lower/(k:ℤ):ℤ):ℝ)≤ -2 := by exact_mod_cast (le_of_not_gt hh)
    have hp := mul_pos hk (sub_pos.mpr A.mix_lt)
    nlinarith
  omega

theorem junction_adjacent_small_formula {q : Tuning} {k : ℕ}
    (A : FareyPlateau.Edge.AdjacentData q 1 k) (hk : 4≤k) {a t₂ : ℝ}
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*(Real.pi/k))) t₂)
    (hg : 0<junctionG a (Real.cos (2*(Real.pi/k))) t₂ (Real.pi/k))
    (hkg : junctionG a (Real.cos (2*(Real.pi/k))) t₂ (Real.pi/k)<(k:ℝ)/2) :
    deriv^[2] A.function (2*Real.pi/k)=
      Real.sin (Real.pi/k)*deriv^[2] (Geometry.shiftedAngle q 0) (2*Real.pi/k)-
        ((k:ℝ)-2*junctionG a (Real.cos (2*(Real.pi/k))) t₂ (Real.pi/k))*
          junctionG a (Real.cos (2*(Real.pi/k))) t₂ (Real.pi/k)*Real.cos (Real.pi/k) := by
  have hm := (adjacent_lower_in_first_strip A hg hkg (junction_adjacent_slope A hk hXi)).2
  rw [junction_actual_adjacent_second A hk hXi,hm]
  have hkn : (k:ℝ)≠0 := by exact_mod_cast (show k≠0 by omega)
  field_simp
  ring

theorem junction_adjacent_large_positive {q : Tuning} {k : ℕ}
    (A : FareyPlateau.Edge.AdjacentData q 1 k) (hk : 4≤k) {a t₂ : ℝ}
    (hd : t₂<Real.cos (2*(Real.pi/k)))
    (ha : junctionLower (Real.cos (2*(Real.pi/k))) t₂<a)
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*(Real.pi/k))) t₂)
    (hg : (k:ℝ)/2<junctionG a (Real.cos (2*(Real.pi/k))) t₂ (Real.pi/k)) :
    0<deriv^[2] A.function (2*Real.pi/k) := by
  have hc := junction_half_angle hk
  have hkr : (4:ℝ)≤k := by exact_mod_cast hk
  have ht0 : 0≤Real.cos (2*(Real.pi/k)) := by
    rw [show 2*(Real.pi/k)=2*Real.pi/k by ring]
    exact (junction_trig_bounds hkr).1
  have ht1 : Real.cos (2*(Real.pi/k))<1 := by
    rw [show 2*(Real.pi/k)=2*Real.pi/k by ring]
    exact (junction_trig_bounds hkr).2.1
  have hap : 0<a := lt_trans (show 0<junctionLower (Real.cos (2*(Real.pi/k))) t₂ from
    div_pos (by norm_num) (mul_pos (by linarith) (by linarith))) ha
  have hp := junction_phase_curvature_gt q hc ht0 hd hap hXi
  apply adjacent_curvature_tail_positive (u:=Real.sin (Real.pi/k))
    (v:=deriv^[2] (Geometry.shiftedAngle q 0) (2*Real.pi/k)) (t:=A.mix) hkr hg
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hc.1,Real.pi_pos],hc.2⟩)
    (by simpa only [show 2*Real.pi/k=2*(Real.pi/k) by ring] using hp)
  rw [junction_actual_adjacent_second A hk hXi]
  ring

theorem junction_adjacent_negative_iff {q : Tuning} {k : ℕ}
    (A : FareyPlateau.Edge.AdjacentData q 1 k) (hk : 4≤k) {a t₂ : ℝ}
    (hd : t₂<Real.cos (2*(Real.pi/k)))
    (ha : junctionLower (Real.cos (2*(Real.pi/k))) t₂<a)
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*(Real.pi/k))) t₂) :
    deriv^[2] A.function (2*Real.pi/k)<0 ↔
      a∈Ioo (junctionLower (Real.cos (2*(Real.pi/k))) t₂)
        (junctionUpper k (Real.cos (2*(Real.pi/k))) t₂ (Real.sin (Real.pi/k))) := by
  have hc := junction_half_angle hk
  have hkr : (4:ℝ)≤k := by exact_mod_cast hk
  have ht0 : 0≤Real.cos (2*(Real.pi/k)) := by
    rw [show 2*(Real.pi/k)=2*Real.pi/k by ring]
    exact (junction_trig_bounds hkr).1
  have ht1 : Real.cos (2*(Real.pi/k))<1 := by
    rw [show 2*(Real.pi/k)=2*Real.pi/k by ring]
    exact (junction_trig_bounds hkr).2.1
  have hs := Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2,Real.pi_pos])
  have hap : 0<a := lt_trans (show 0<junctionLower (Real.cos (2*(Real.pi/k))) t₂ from
    div_pos (by norm_num) (mul_pos (by linarith) (by linarith))) ha
  have hg : 0<junctionG a (Real.cos (2*(Real.pi/k))) t₂ (Real.pi/k) := by
    unfold junctionG
    positivity
  by_cases hsmall : junctionG a (Real.cos (2*(Real.pi/k))) t₂ (Real.pi/k)<(k:ℝ)/2
  · rw [junction_adjacent_small_formula A hk hXi hg hsmall,
      show 2*Real.pi/k=2*(Real.pi/k) by ring]
    exact junction_small_curvature_negative_iff q hc hd ha hXi
  · have hne := adjacent_half_period_ne A (junction_adjacent_slope A hk hXi)
    have hlarge : (k:ℝ)/2<junctionG a (Real.cos (2*(Real.pi/k))) t₂ (Real.pi/k) :=
      lt_of_le_of_ne (le_of_not_gt hsmall) (Ne.symm hne)
    have hp := junction_adjacent_large_positive A hk hd ha hXi hlarge
    constructor
    · intro hn
      linarith
    · intro hi
      have hb := (junction_interval_g_bounds hkr ht0 ht1 hd hs hi.1 hi.2).2
      exact (hsmall hb).elim

end polyak.GapEdges.Junction
