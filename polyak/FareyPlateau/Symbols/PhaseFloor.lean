import polyak.FareyPlateau.Symbols.Polynomial
import Mathlib.Analysis.Analytic.Polynomial

/-! The source phase floor is analytic across both endpoints after exact
polynomial cancellation, and agrees with the original sine quotient. -/
noncomputable section
namespace polyak.FareyPlateau.Symbols
open Polynomial Set
open scoped BigOperators
variable {I : Type*} [Fintype I]

theorem normalizedDenominator_pos (n : I→ℤ) (w : I→ℝ)
    (hn : ∀i,n i≠0) (hw : ∀i,0≤w i) (hsum : ∑i,w i=1)
    (hbez : SupportBezout n w) {c : ℝ} (hc : c∈Icc (-1:ℝ) 1) :
    0<(normalizedDenominator n w).eval c := by
  by_cases hc1 : c=1
  · rw [hc1,normalizedDenominator_one]
    have hp : 0<∑i,w i := by rw [hsum]; norm_num
    obtain ⟨i,_,hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _=>hw i)).mp hp
    apply Finset.sum_pos'
    · intro j _; exact mul_nonneg (hw j) (sq_nonneg _)
    · exact ⟨i,Finset.mem_univ _,mul_pos hi (sq_pos_of_ne_zero (by exact_mod_cast hn i))⟩
  · let ω := Real.arccos c
    have hω : ω∈Ioc (0:ℝ) Real.pi :=
      ⟨Real.arccos_pos.mpr (lt_of_le_of_ne hc.2 hc1),Real.arccos_le_pi _⟩
    have hcos : Real.cos ω=c := Real.cos_arccos hc.1 hc.2
    have hp := denominator_pos n w hw hbez hω
    rw [←normalizedDenominator_cos n w ω,hcos] at hp
    exact pos_of_mul_pos_right hp (sub_nonneg.mpr hc.2)

theorem analyticAt_psi (n : I→ℤ) (w : I→ℝ)
    (hn : ∀i,n i≠0) (hw : ∀i,0≤w i) (hsum : ∑i,w i=1)
    (hbez : SupportBezout n w) {c : ℝ} (hc : c∈Icc (-1:ℝ) 1) :
    AnalyticAt ℝ (psi n w) c := by
  have hP : AnalyticAt ℝ (fun c=>(normalizedDenominator n w).eval c) c :=
    AnalyticOnNhd.eval_polynomial _ c (mem_univ _)
  have hQ : AnalyticAt ℝ (fun c=>(sinePolynomial n w).eval c) c :=
    AnalyticOnNhd.eval_polynomial _ c (mem_univ _)
  exact ((analyticAt_const.add analyticAt_id).mul hQ).div hP
    (normalizedDenominator_pos n w hn hw hsum hbez hc).ne'

theorem continuousOn_psi (n : I→ℤ) (w : I→ℝ)
    (hn : ∀i,n i≠0) (hw : ∀i,0≤w i) (hsum : ∑i,w i=1)
    (hbez : SupportBezout n w) : ContinuousOn (psi n w) (Icc (-1:ℝ) 1) :=
  fun _c hc=>(analyticAt_psi n w hn hw hsum hbez hc).continuousAt.continuousWithinAt

theorem psi_cos (n : I→ℤ) (w : I→ℝ)
    (hn : ∀i,n i≠0) (hw : ∀i,0≤w i) (hsum : ∑i,w i=1)
    (hbez : SupportBezout n w) {ω : ℝ} (hω : ω∈Ioo (0:ℝ) Real.pi) :
    psi n w (Real.cos ω)=
      Real.sin ω*(∑i,w i*Real.sin ((n i:ℝ)*ω))/denominator n w ω := by
  have hc : Real.cos ω∈Icc (-1:ℝ) 1 := ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  have hnorm := normalizedDenominator_pos n w hn hw hsum hbez hc
  have hcos : Real.cos ω<1 := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0:ℝ)≤0 by rfl) hω.2.le hω.1
    simpa only [Real.cos_zero] using hh
  unfold psi
  rw [←normalizedDenominator_cos,←sinePolynomial_cos]
  have hs : Real.sin ω*((sinePolynomial n w).eval (Real.cos ω)*Real.sin ω)=
      (1-(Real.cos ω)^2)*(sinePolynomial n w).eval (Real.cos ω) := by
    linear_combination (sinePolynomial n w).eval (Real.cos ω)*(Real.sin_sq_add_cos_sq ω)
  rw [hs]
  field_simp [hnorm.ne',show 1-Real.cos ω≠0 by linarith]
  ring

end polyak.FareyPlateau.Symbols
