import polyak.ModeLocking.Periods.Support
import polyak.ModeLocking.Periods.Arithmetic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! R1 and the pinning rank rule out every proper common support period.
The nominal period is therefore the least common denominator. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels MeasureTheory Set
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem rep_of_tight {r : ℤ} (hr : 0<r) (hrL : r<L)
    (ht : (∑ i, (D.primal i:ℝ)*(Geometry.shiftedCurve q s).lag r (D.atoms i))=0) :
    ∃ i, D.reps i=r := by
  by_contra hn
  have hh := D.inactive r hr hrL (by simpa only [not_exists,ne_comm] using hn)
  linarith

theorem reps_eq_of_smaller_period {g : ℕ} (hg : ∀ i, D.atoms i ∈ periodicGrid g)
    (i j : Fin D.d) (hdiv : (g:ℤ) ∣ D.reps i-D.reps j) : D.reps i=D.reps j := by
  obtain ⟨m,hm⟩ := hdiv
  have he : D.reps i=D.reps j+m*g := by nlinarith only [hm]
  have hinj := (Matrix.linearIndependent_cols_of_det_ne_zero D.pinning_det).injective
  have hij : i=j := by
    apply hinj
    funext z
    change Real.sin ((D.reps i:ℝ)*(D.atoms z:ℝ)-Geometry.shiftedCurve q s (D.atoms z)) =
      Real.sin ((D.reps j:ℝ)*(D.atoms z:ℝ)-Geometry.shiftedCurve q s (D.atoms z))
    rw [he]
    exact sin_lag_add_mul_grid (hg z) (D.reps j) m _
  exact congrArg D.reps hij

private theorem lag_zero_of_dvd {g : ℕ} {ω : Frequency} (hω : ω ∈ periodicGrid g)
    {n : ℤ} (hn : (g:ℤ) ∣ n) : (Geometry.shiftedCurve q s).lag n ω=0 := by
  rw [lag_mod_grid (Geometry.shiftedCurve q s) hω n,Int.emod_eq_zero_of_dvd hn,Curve.lag_zero]

/-- The zero orbit already forces a hypothetical proper period to have index two. -/
theorem smaller_period_index_two {g : ℕ} (hgpos : 0<g) (hgL : g∣L) (hglt : g<L)
    (hg : ∀ i, D.atoms i ∈ periodicGrid g) : L=2*g := by
  have hgL' : (g:ℤ) ∣ (L:ℤ) := by exact_mod_cast hgL
  have hglt' : (g:ℤ)<L := by exact_mod_cast hglt
  have hgp : (0:ℤ)<g := by exact_mod_cast hgpos
  have hfirst : (∑ i,(D.primal i:ℝ)*(Geometry.shiftedCurve q s).lag (g:ℤ) (D.atoms i))=0 := by
    simp only [lag_zero_of_dvd (q := q) (s := s) (hg _) (dvd_refl _),mul_zero,Finset.sum_const_zero]
  have hlast : (∑ i,(D.primal i:ℝ)*(Geometry.shiftedCurve q s).lag ((L:ℤ)-g) (D.atoms i))=0 := by
    simp only [lag_zero_of_dvd (q := q) (s := s) (hg _) (dvd_sub hgL' (dvd_refl _)),
      mul_zero,Finset.sum_const_zero]
  obtain ⟨i,hi⟩ := D.rep_of_tight hgp hglt' hfirst
  obtain ⟨j,hj⟩ := D.rep_of_tight (by omega : 0<(L:ℤ)-g) (by omega) hlast
  have hd : (g:ℤ)∣D.reps i-D.reps j := by
    rw [hi,hj]
    exact dvd_sub (dvd_refl _) (dvd_sub hgL' (dvd_refl _))
  have he := D.reps_eq_of_smaller_period hg i j hd
  rw [hi,hj] at he
  omega

/-- At index two every nonzero tight class is the single zero-orbit class. -/
theorem reps_eq_half_period {g : ℕ} (hgpos : 0<g) (hL : L=2*g)
    (hg : ∀ i, D.atoms i ∈ periodicGrid g) (i : Fin D.d) : D.reps i=g := by
  have hgp : (0:ℤ)<g := by exact_mod_cast hgpos
  have hsize : (L:ℤ)=2*(g:ℤ) := by exact_mod_cast hL
  by_contra hn
  let r : ℤ := if D.reps i < g then D.reps i+g else D.reps i-g
  have hr : 0<r ∧ r<L := by
    dsimp [r]
    split_ifs with h
    · have hi := D.reps_pos i
      omega
    · have hi := D.reps_lt i
      omega
  have hdiv : (g:ℤ) ∣ r-D.reps i := by
    dsimp [r]
    split_ifs
    · convert dvd_refl (g:ℤ) using 1
      ring
    · convert dvd_neg.mpr (dvd_refl (g:ℤ)) using 1
      ring
  have hequal (z : Fin D.d) : (Geometry.shiftedCurve q s).lag r (D.atoms z) =
      (Geometry.shiftedCurve q s).lag (D.reps i) (D.atoms z) := by
    obtain ⟨m,hm⟩ := hdiv
    have he : r=D.reps i+m*g := by nlinarith only [hm]
    rw [he]
    exact lag_add_mul_grid _ (hg z) _ _
  have ht : (∑ z,(D.primal z:ℝ)*(Geometry.shiftedCurve q s).lag r (D.atoms z))=0 := by
    simp only [hequal]
    exact D.tight i
  obtain ⟨j,hj⟩ := D.rep_of_tight hr.1 hr.2 ht
  have he := D.reps_eq_of_smaller_period hg j i (by simpa only [hj] using hdiv)
  rw [hj] at he
  dsimp [r] at he
  split_ifs at he <;> omega

/-- R1--R3 force the nominal period to be the least support denominator. -/
theorem common_divisor_period_eq {g : ℕ} (hgpos : 0<g) (hgL : g∣L)
    (hg : ∀ i, D.atoms i ∈ periodicGrid g) : g=L := by
  have hLpos : 0<L := by have hh := D.period_ge; omega
  have hle : g≤L := Nat.le_of_dvd hLpos hgL
  by_contra hn
  have hlt : g<L := lt_of_le_of_ne hle hn
  have hL := D.smaller_period_index_two hgpos hgL hlt hg
  have hreps := D.reps_eq_half_period hgpos hL hg
  have hgL' : (g:ℤ)∣(L:ℤ) := by exact_mod_cast hgL
  have hlags (n : ℤ) (hn : n∈D.lags) : (g:ℤ)∣n := by
    have hmod : (g:ℤ)∣n%(L:ℤ) := by
      rcases D.classes n hn with hz | ⟨i,hi⟩
      · rw [hz]
        exact dvd_zero _
      · rw [hi,hreps i]
    have he := Int.emod_add_ediv_mul n (L:ℤ)
    rw [← he]
    exact dvd_add hmod (dvd_mul_of_dvd_right hgL' _)
  let i : Fin D.d := ⟨0,D.d_pos⟩
  have hPzero : pinningPolynomial D.lags D.dual (D.atoms i)=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    obtain ⟨m,hm⟩ := hlags n hn
    have hc := cos_lag_add_mul_grid (hg i) 0 m 0
    have he : n=0+m*g := by nlinarith only [hm]
    rw [← he] at hc
    simp only [Int.cast_zero,zero_mul,sub_zero,Real.cos_zero] at hc
    rw [hc]
    ring
  have hp := D.pinning_pos i
  rw [hPzero] at hp
  exact lt_irrefl _ hp

end polyak.ModeLocking.RegularData
