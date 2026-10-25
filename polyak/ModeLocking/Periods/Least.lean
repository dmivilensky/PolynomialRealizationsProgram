import polyak.ModeLocking.Periods.Minimal

/-! The nominal regular period is exactly the common support denominator:
all feasible periods are its multiples, and fan periods exist iff coprime. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels Set

theorem periodicGrid_gcd {A B : ℕ} {ω : Frequency}
    (hA : ω ∈ periodicGrid A) (hB : ω ∈ periodicGrid B) :
    ω ∈ periodicGrid (Nat.gcd A B) := by
  obtain ⟨hpos,j,hj⟩ := hA
  obtain ⟨_,k,hk⟩ := hB
  refine ⟨hpos,Nat.gcdA A B*j+Nat.gcdB A B*k,?_⟩
  have hb : (Nat.gcd A B:ℝ) = (A:ℝ)*(Nat.gcdA A B:ℝ) +
      (B:ℝ)*(Nat.gcdB A B:ℝ) := by exact_mod_cast Nat.gcd_eq_gcd_ab A B
  push_cast
  rw [hb]
  linear_combination (Nat.gcdA A B:ℝ)*hj + (Nat.gcdB A B:ℝ)*hk

private theorem grid_refinement {A B : ℕ} (h : A∣B) {ω : Frequency}
    (hω : ω ∈ periodicGrid A) : ω ∈ periodicGrid B := by
  obtain ⟨m,rfl⟩ := h
  obtain ⟨hpos,j,hj⟩ := hω
  refine ⟨hpos,(m:ℤ)*j,?_⟩
  push_cast
  linear_combination (m:ℝ)*hj

namespace RegularData
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem support_period_iff_dvd (k : ℕ) :
    (∀ i, D.atoms i ∈ periodicGrid k) ↔ L∣k := by
  constructor
  · intro hk
    have hpos : 0<L := by have hh := D.period_ge; omega
    have hg := D.common_divisor_period_eq (Nat.gcd_pos_of_pos_left k hpos)
      (Nat.gcd_dvd_left L k) (fun i => periodicGrid_gcd (D.atoms_grid i) (hk i))
    have hd := Nat.gcd_dvd_right L k
    rwa [hg] at hd
  · intro hk i
    exact grid_refinement hk (D.atoms_grid i)

theorem least_common_support_denominator :
    IsLeast {k : ℕ | 0<k ∧ ∀ i, D.atoms i ∈ periodicGrid k} L := by
  have hpos : 0<L := by have hh := D.period_ge; omega
  refine ⟨⟨hpos,D.atoms_grid⟩,?_⟩
  intro k hk
  exact Nat.le_of_dvd hk.1 ((D.support_period_iff_dvd k).mp hk.2)

include D in
theorem periodic_iff_dvd (k : ℕ) : PeriodicFP (Geometry.shiftedCurve q s) k ↔ L∣k := by
  rw [D.periodic_iff_support,D.support_period_iff_dvd]

include D in
theorem fan_periodic_iff_coprime (K : ℕ) :
    (∃ p : ℕ, 2≤p ∧ PeriodicFP (Geometry.shiftedCurve q s) (p*K+1)) ↔ L.Coprime K := by
  simp_rw [D.periodic_iff_dvd]
  exact Periods.exists_fan_period_iff (by have hh := D.period_ge; omega)

include D in
theorem fan_periods_arbitrarily_large (K B : ℕ) (hc : L.Coprime K) :
    ∃ p : ℕ, B≤p ∧ 2≤p ∧ PeriodicFP (Geometry.shiftedCurve q s) (p*K+1) := by
  obtain ⟨p,hB,hp,hd⟩ := Periods.arbitrarily_large_fan_periods
    (by have hh := D.period_ge; omega : 0<L) hc B
  exact ⟨p,hB,hp,(D.periodic_iff_dvd _).mpr hd⟩

end RegularData
end polyak.ModeLocking
