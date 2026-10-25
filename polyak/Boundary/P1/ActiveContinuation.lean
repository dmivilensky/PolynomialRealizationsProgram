import polyak.Boundary.P1.ActiveFinite

/-! Article: every original P1 lag, and the exact active set of its open regime. -/
noncomputable section
namespace polyak.Boundary.P1
open Spectral

theorem rawSlack_tail_pos {z u t : ℝ} (a : Frequency) (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤(a : ℝ) ∧ (a : ℝ)≤0) (hu : 0≤u)
    (hgz : z/2≤1-(a : ℝ)^2-u^2) (h0 : quartic z u a=0) (ht : Real.cosh t=1/z)
    (n : ℕ) (hn : 13≤n) (σ : ℝ) (hσ : σ= -1 ∨ σ=1) :
    0<rawSlack u (1/z) (chargeNumerator z u a) n σ a := by
  let C := chargeNumerator z u a/Real.sinh t
  have hgap := minimizer_gap hz hz1 ha hu hgz h0 ht
  have hbudget : meanG (spectrum a) u+2*u^2≤4 := by
    rw [meanG_spectrum]
    nlinarith [sq_nonneg (a : ℝ)]
  have htail := tail_at_thirteen hz hz1 ht (by simpa [meanG_spectrum] using hgap)
    hbudget n hn
  have hs : (-σ)=1 ∨ (-σ)= -1 := by rcases hσ with rfl | rfl <;> norm_num
  have hraw := raw_lag_tail (spectrum a) u C t n (by omega) (-σ) hs
  have he := raw_spectrum a u t (chargeNumerator z u a) (exponent_ne_zero hz hz1 ht)
    n (by omega) σ
  rw [ht] at he
  change (meanG (spectrum a) u-|C|)*Real.cosh (n*t)-(meanG (spectrum a) u+2*u^2)≤_ at hraw
  rw [← meanG_spectrum a u] at htail
  change meanG (spectrum a) u+2*u^2<(meanG (spectrum a) u-|C|)*Real.cosh (n*t) at htail
  change meanA (spectrum a) u t n+σ*meanB (spectrum a) u n-
    σ*C*Real.sinh (n*t)=_ at he
  nlinarith only [htail,hraw,he]

/-- Every inactive source slack is strictly positive throughout the open P1 regime. -/
theorem continuation_inactive_pos {z t : ℝ} (hz : z∈Set.Ioo (0 : ℝ) zW)
    (ht : Real.cosh t=1/z) (n : ℕ) (hn : 1≤n) (σ : ℝ) (hσ : σ= -1 ∨ σ=1)
    (ha : ¬ActivePair n σ) :
    0<rawSlack (branchU z (continuation z 0)) (1/z)
      (chargeNumerator z (branchU z (continuation z 0)) (branchAtom z (continuation z 1)))
      n σ (branchAtom z (continuation z 1)) := by
  have hz1 : z≤3/4 := by linarith [hz.2,zW_bounds.2]
  have hD : z∈continuationDomain := ⟨hz.1.le,(hz.2.trans zW_bounds.2).le⟩
  have hZ := continuation_source hD
  have hcore := continuation_core hD
  have hb := continuation_physical ⟨hz.1,hz.2.le⟩
  let a := physicalAtom hz.1 hz1 hb
  have ha' : -z/2<(a : ℝ) ∧ (a : ℝ)≤0 :=
    ⟨continuation_atom_lower_strict hz,hb.atom_nonpos⟩
  by_cases hN : n≤12
  · exact rawSlack_pos_of_scaled hz.1 (contactD_pos hz.1.le hz1 a)
      (hcore.u_pos hz.1 hz1 hZ) (by
        have h := hcore.atom_abs_lt hz.1
        exact (sq_lt_one_iff_abs_lt_one _).mpr h)
      (regularSystem_contacts hZ).1 n hn σ
      (scaledSlack_inactive_prefix_pos hz.1 hz1 ha' n hn hN σ hσ ha)
  · exact rawSlack_tail_pos a hz.1 hz1 ⟨hb.atom_lower,hb.atom_nonpos⟩ hb.u_nonneg
      hb.gap_lower (regularSystem_contacts hZ).1 ht n (by omega) σ hσ

/-- The two displayed source equalities are the only active signed lags on the open arc. -/
theorem continuation_active_iff {z t : ℝ} (hz : z∈Set.Ioo (0 : ℝ) zW)
    (ht : Real.cosh t=1/z) (n : ℕ) (hn : 1≤n) (σ : ℝ) (hσ : σ= -1 ∨ σ=1) :
    rawSlack (branchU z (continuation z 0)) (1/z)
      (chargeNumerator z (branchU z (continuation z 0)) (branchAtom z (continuation z 1)))
      n σ (branchAtom z (continuation z 1))=0 ↔ ActivePair n σ := by
  constructor
  · intro he
    by_contra ha
    exact (continuation_inactive_pos hz ht n hn σ hσ ha).ne' he
  · intro ha
    have hz1 : z≤3/4 := by linarith [hz.2,zW_bounds.2]
    have hb := continuation_physical ⟨hz.1,hz.2.le⟩
    let a := physicalAtom hz.1 hz1 hb
    have hcoef : contactD z a*z^(n-1)≠0 :=
      mul_ne_zero (contactD_pos hz.1.le hz1 a).ne' (pow_ne_zero _ hz.1.ne')
    have he := scaledSlack_source hz.1.ne' (contactD_pos hz.1.le hz1 a).ne'
      (regularSystem_contacts (continuation_source ⟨hz.1.le,(hz.2.trans zW_bounds.2).le⟩)).1 n hn σ
    rcases ha with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [scaledSlack_one_lower,mul_zero] at he
      exact (mul_eq_zero.mp he).resolve_left hcoef
    · rw [scaledSlack_three_upper,mul_zero] at he
      exact (mul_eq_zero.mp he).resolve_left hcoef

end polyak.Boundary.P1
