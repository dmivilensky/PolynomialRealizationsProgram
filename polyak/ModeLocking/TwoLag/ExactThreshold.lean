import polyak.ModeLocking.TwoLag.ExactRegular
import polyak.ModeLocking.TwoLag.DecouplingCertificate
import polyak.ModeLocking.Regular.Threshold

/-! Exact two-lag points identify all three thresholds, including the
smaller relaxation with only the two original lags. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag.ExactData
open General Levels Set
variable {q : Tuning} {s : ℝ} {K L : ℕ} (D : ExactData q s K L)

include D in
theorem pairLags_nonzero : pairLags K⊆nonzeroLags := by
  have hK := D.K_ge
  intro n hn
  simp only [pairLags,mem_insert_iff,mem_singleton_iff] at hn
  rcases hn with rfl|rfl <;> simp only [nonzeroLags,mem_ofPred_eq] <;> omega

include D in
theorem sigma_eq : Threshold.sigma q=s := by
  obtain ⟨R,_,_⟩ := D.exists_regularData
  exact R.sigma_eq

include D in
theorem sigmaPeriodic_eq : Threshold.sigmaPeriodic q L=s := by
  obtain ⟨R,_,_⟩ := D.exists_regularData
  exact R.sigmaPeriodic_eq

theorem pair_negative_below {t : ℝ} (ht : t<s) (ω : Frequency) (hω0 : 0<(ω : ℝ)) :
    (Geometry.shiftedCurve q t).lag 1 ω+(D.b/D.a)*(Geometry.shiftedCurve q t).lag (-(K : ℤ)) ω<0 := by
  have ha := D.a_pos
  have hb := D.b_pos
  have hweighted : D.a*(Geometry.shiftedCurve q t).lag 1 ω+
      D.b*(Geometry.shiftedCurve q t).lag (-(K : ℤ)) ω<0 := by
    rcases eq_or_lt_of_le ω.property.2 with hpi|hpi
    · have hω : ω=frequencyPi := Subtype.ext hpi
      rw [hω]
      have h1 : (Geometry.shiftedCurve q t).lag 1 frequencyPi=-2 := by rw [Curve.lag_at_pi];norm_num
      rw [h1]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hb.le
        ((Geometry.shiftedCurve q t).lag_at_pi_nonpos (-(K : ℤ)))]
    have hω : ω∈Threshold.interiorCarrier := ⟨hω0,hpi⟩
    let n : Fin 2→ℤ := ![1,-(K : ℤ)]
    let a : Fin 2→ℝ := ![D.a,D.b]
    have heval (v : ℝ) : Localization.symbol q v n a 0 ω=
        D.a*(Geometry.shiftedCurve q v).lag 1 ω+D.b*(Geometry.shiftedCurve q v).lag (-(K : ℤ)) ω := by
      simp [Localization.symbol,n,a,Fin.sum_univ_two]
    have hsource : Localization.symbol q s n a 0 ω≤0 := by
      rw [heval,←extension_actual]
      exact D.nonpos ω ω.property
    have hosc : 0<Localization.oscillation n a ω := by
      have hs := Real.sin_pos_of_pos_of_lt_pi hω0 hpi
      have hc : Real.cos (ω : ℝ)<1 := by
        nlinarith [Real.sin_sq_add_cos_sq (ω : ℝ),sq_pos_of_pos hs,Real.cos_le_one (ω : ℝ)]
      have hn := mul_nonneg hb.le (sub_nonneg.mpr (Real.cos_le_one ((-(K : ℤ) : ℝ)*(ω : ℝ))))
      have hp := mul_pos ha (sub_pos.mpr hc)
      simp only [Localization.oscillation,n,a,Fin.sum_univ_two,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_fin_one,Int.cast_one,one_mul]
      simp only [Int.cast_neg,Int.cast_natCast] at hn ⊢
      nlinarith [hn,hp]
    have hid := Localization.shift_identity q t s n a 0 ω hω
    have hfrac : Localization.symbol q t n a 0 ω/Real.sin (Geometry.shiftedCurve q t ω)<0 := by
      rw [hid,add_zero]
      exact add_neg_of_nonpos_of_neg (div_nonpos_of_nonpos_of_nonneg hsource
        (Localization.phase_sin_pos q s ω hω).le) (mul_neg_of_neg_of_pos (sub_neg.mpr ht) hosc)
    have hneg := (div_lt_iff₀ (Localization.phase_sin_pos q t ω hω)).mp hfrac
    simpa only [zero_mul,heval] using hneg
  have he : (Geometry.shiftedCurve q t).lag 1 ω+(D.b/D.a)*(Geometry.shiftedCurve q t).lag (-(K : ℤ)) ω=
      (D.a*(Geometry.shiftedCurve q t).lag 1 ω+D.b*(Geometry.shiftedCurve q t).lag (-(K : ℤ)) ω)/D.a := by
    field_simp
  rw [he]
  exact div_neg_of_neg_of_pos hweighted ha

include D in
theorem sigmaPair_eq : Threshold.sigmaOn q (pairLags K)=s := by
  apply le_antisymm
  · rw [←D.sigma_eq]
    exact Threshold.sigmaOn_le_sigma q (pairLags K) D.pairLags_nonzero
  · by_contra hn
    have ht : Threshold.sigmaOn q (pairLags K)<s := lt_of_not_ge hn
    exact no_solution_of_pair_strict (by have hK:=D.K_ge;omega : 1≤K)
      (div_nonneg D.b_pos.le D.a_pos.le) (D.pair_negative_below ht)
      (Threshold.sigmaOn_feasible q (pairLags K) D.pairLags_nonzero)

end polyak.ModeLocking.TwoLag.ExactData
