import polyak.Levels.Program.Alternative
import polyak.General.AngleComparison

/-! Arbitrary-curve monotonicity from the exact alternative. -/
noncomputable section
open scoped BigOperators
namespace polyak.Levels

def CertificateSymbol.rephase {Θ : Curve} {𝒩 : Set ℤ} (S : CertificateSymbol Θ 𝒩)
    (Ψ : Curve) : CertificateSymbol Ψ 𝒩 where
  lags := S.lags
  lags_subset := S.lags_subset
  weight := S.weight
  weight_nonneg := S.weight_nonneg
  gamma := S.gamma
  gamma_nonneg := S.gamma_nonneg

def CertificateSymbol.realPart {Θ : Curve} {𝒩 : Set ℤ} (S : CertificateSymbol Θ 𝒩)
    (ω : Frequency) : ℝ := S.gamma+(∑n∈S.lags,S.weight n*(1-Real.cos ((n:ℝ)*(ω:ℝ))))

def CertificateSymbol.imagPart {Θ : Curve} {𝒩 : Set ℤ} (S : CertificateSymbol Θ 𝒩)
    (ω : Frequency) : ℝ := -(∑n∈S.lags,S.weight n*Real.sin ((n:ℝ)*(ω:ℝ)))

theorem CertificateSymbol.gamma_le_realPart {Θ : Curve} {𝒩 : Set ℤ}
    (S : CertificateSymbol Θ 𝒩) (ω : Frequency) : S.gamma≤S.realPart ω := by
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg (fun n hn => mul_nonneg (S.weight_nonneg n hn)
    (sub_nonneg.mpr (Real.cos_le_one _)))

theorem CertificateSymbol.eval_eq_parts {Θ : Curve} {𝒩 : Set ℤ}
    (S : CertificateSymbol Θ 𝒩) (ω : Frequency) :
    S.eval ω=S.realPart ω*Real.cos (Θ ω)+S.imagPart ω*Real.sin (Θ ω) := by
  have he (n:ℤ) : S.weight n*Θ.lag n ω=
      (S.weight n*(1-Real.cos ((n:ℝ)*(ω:ℝ))))*Real.cos (Θ ω)-
      (S.weight n*Real.sin ((n:ℝ)*(ω:ℝ)))*Real.sin (Θ ω) := by
    rw [Θ.lag_expand]
    ring
  unfold eval realPart imagPart
  simp_rw [he]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.sum_mul]
  dsimp [Curve.minimizer]
  ring

theorem rotated_negative_mono {P Q a b : ℝ} (hP : 0<P) (ha : 0<a)
    (hb : b≤Real.pi) (hab : a≤b) (hneg : P*Real.cos a+Q*Real.sin a<0) :
    P*Real.cos b+Q*Real.sin b<0 := by
  by_cases heq : a=b
  · simpa only [← heq] using hneg
  have hab' : a<b := lt_of_le_of_ne hab heq
  by_cases hbp : b=Real.pi
  · simp only [hbp,Real.cos_pi,Real.sin_pi,mul_neg,mul_one,mul_zero,add_zero]
    exact neg_neg_of_pos hP
  have hblt : b<Real.pi := lt_of_le_of_ne hb hbp
  have halt : a<Real.pi := hab'.trans hblt
  have hsa := Real.sin_pos_of_pos_of_lt_pi ha halt
  have hsb := Real.sin_pos_of_pos_of_lt_pi (ha.trans hab') hblt
  have hcot := (General.cot_strictAnti ⟨ha.trans hab',hblt⟩ ⟨ha,halt⟩).mpr hab'
  have he (t:ℝ) (hs:Real.sin t≠0) :
      P*(Real.cos t/Real.sin t)+Q=(P*Real.cos t+Q*Real.sin t)/Real.sin t := by
    field_simp
  have hna : P*(Real.cos a/Real.sin a)+Q<0 := by
    rw [he a (ne_of_gt hsa)]
    exact div_neg_of_neg_of_pos hneg hsa
  have hnb : P*(Real.cos b/Real.sin b)+Q<0 := by
    have hc := mul_le_mul_of_nonneg_left hcot.le hP.le
    linarith
  rw [he b (ne_of_gt hsb)] at hnb
  have hn := (div_lt_iff₀ hsb).mp hnb
  simpa only [zero_mul] using hn

theorem strictSymbol_of_pointwise_negative {Θ : Curve} {𝒩 : Set ℤ}
    (S : CertificateSymbol Θ 𝒩) (h : ∀ω,S.eval ω<0) : Nonempty (StrictSymbol Θ 𝒩) := by
  obtain ⟨ω,_,hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty S.continuous_eval.continuousOn
  refine ⟨S,-S.eval ω,neg_pos.mpr (h ω),?_⟩
  intro η
  rw [neg_neg]
  exact hmax (Set.mem_univ η)

theorem StrictSymbol.rephase_up {Θ Ψ : Curve} {𝒩 : Set ℤ} (S : StrictSymbol Θ 𝒩)
    (horder : ∀ω,Θ ω≤Ψ ω) : Nonempty (StrictSymbol Ψ 𝒩) := by
  apply strictSymbol_of_pointwise_negative (S.symbol.rephase Ψ)
  intro ω
  have hneg : S.symbol.eval ω<0 := lt_of_le_of_lt (S.strict ω) (neg_neg_of_pos S.epsilon_pos)
  rw [S.symbol.eval_eq_parts] at hneg
  rw [(S.symbol.rephase Ψ).eval_eq_parts]
  exact rotated_negative_mono (lt_of_lt_of_le S.gamma_pos (S.symbol.gamma_le_realPart ω))
    (Θ.pos ω) (Ψ.le_pi ω) (horder ω) hneg

theorem fpOn_mono {Θ Ψ : Curve} (𝒩 : Set ℤ) (horder : ∀ω,Ψ ω≤Θ ω)
    (h : FPOn Θ 𝒩) : FPOn Ψ 𝒩 := by
  by_contra hnot
  obtain ⟨S⟩ := (infeasible_iff_strictSymbol Ψ 𝒩).mp hnot
  obtain ⟨S'⟩ := S.rephase_up horder
  exact S'.not_fpOn h

theorem fp_mono {Θ Ψ : Curve} (horder : ∀ω : Frequency,0<(ω:ℝ)→(ω:ℝ)<Real.pi→Ψ ω≤Θ ω)
    (h : FP Θ) : FP Ψ := by
  apply fpOn_mono nonzeroLags (h:=h)
  intro ω
  rcases eq_or_lt_of_le ω.property.1 with h0|h0
  · have he : ω=frequencyZero := Subtype.ext h0.symm
    rw [he,Θ.at_zero,Ψ.at_zero]
  rcases eq_or_lt_of_le ω.property.2 with hp|hp
  · have he : ω=frequencyPi := Subtype.ext hp
    rw [he,Θ.at_pi,Ψ.at_pi]
  exact horder ω h0 hp

end polyak.Levels
