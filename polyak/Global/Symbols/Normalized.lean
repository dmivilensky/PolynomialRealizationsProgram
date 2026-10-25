import polyak.Global.Symbols.Compactness

/-! Honest normalization of the finite separation symbols. Their omitted
coefficients are zero and their minimizer mass is preserved exactly. -/
noncomputable section
namespace polyak.Global.Symbols
open Levels Filter Set Topology
open scoped BigOperators

def total {Θ : Curve} {𝒩 : Set ℤ} (S : CertificateSymbol Θ 𝒩) : ℝ :=
  (∑n∈S.lags,S.weight n)+S.gamma

def normalizedWeight {Θ : Curve} {𝒩 : Set ℤ} (S : CertificateSymbol Θ 𝒩) (n : ℤ) : ℝ :=
  if n∈S.lags then S.weight n/total S else 0

def finiteCoefficient {Θ : Curve} {𝒩 : Set ℤ} (S : CertificateSymbol Θ 𝒩) (n : ℤ) : ℝ :=
  if n∈S.lags then S.weight n else 0

theorem normalizedWeight_eq_finiteCoefficient {Θ : Curve} {𝒩 : Set ℤ}
    (S : CertificateSymbol Θ 𝒩) (hNorm : total S=1) (n : ℤ) :
    normalizedWeight S n=finiteCoefficient S n := by
  unfold normalizedWeight finiteCoefficient
  rw [hNorm]
  simp only [div_one]

theorem normalizedWeight_off {Θ : Curve} {𝒩 : Set ℤ} (S : CertificateSymbol Θ 𝒩)
    (n : ℤ) (hn : n∉S.lags) : normalizedWeight S n=0 := by simp only [normalizedWeight,ite_eq_right hn]

theorem normalizedWeight_tsum {Θ : Curve} {𝒩 : Set ℤ} (S : CertificateSymbol Θ 𝒩) :
    (∑'n,normalizedWeight S n)=(∑n∈S.lags,S.weight n)/total S := by
  rw [tsum_eq_sum (normalizedWeight_off S)]
  simp only [normalizedWeight,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  rw [ite_eq_left hn]

def normalizeWeights {Θ : Curve} {𝒩 : Set ℤ} (S : CertificateSymbol Θ 𝒩)
    (hpos : 0<total S) : Weights 𝒩 where
  weight := normalizedWeight S
  nonneg n := by
    by_cases hn : n∈S.lags
    · exact (by simpa only [normalizedWeight,ite_eq_left hn] using div_nonneg (S.weight_nonneg n hn) hpos.le)
    · rw [normalizedWeight_off S n hn]
  outside n hn := normalizedWeight_off S n (fun h=>hn (S.lags_subset n h))
  summable := summable_of_ne_finset_zero (normalizedWeight_off S)
  mass_le_one := by
    rw [normalizedWeight_tsum]
    apply (div_le_one hpos).mpr
    unfold total
    linarith [S.gamma_nonneg]

theorem normalizeWeights_gamma {Θ : Curve} {𝒩 : Set ℤ} (S : CertificateSymbol Θ 𝒩)
    (hpos : 0<total S) : (normalizeWeights S hpos).gamma=S.gamma/total S := by
  change 1-(∑'n,normalizedWeight S n)=S.gamma/total S
  rw [normalizedWeight_tsum]
  apply (eq_div_iff hpos.ne').mpr
  field_simp
  unfold total
  ring

theorem normalizeWeights_eval {Θ : Curve} {𝒩 : Set ℤ} (S : CertificateSymbol Θ 𝒩)
    (hpos : 0<total S) (ω : Frequency) :
    (normalizeWeights S hpos).eval Θ ω=S.eval ω/total S := by
  unfold Weights.eval Weights.series
  rw [normalizeWeights_gamma]
  have hout (n : ℤ) (hn : n∉S.lags) :
      (normalizeWeights S hpos).weight n*Θ.lag n ω=0 := by
    change normalizedWeight S n*Θ.lag n ω=0
    rw [normalizedWeight_off S n hn,zero_mul]
  rw [tsum_eq_sum hout]
  change (∑n∈S.lags,normalizedWeight S n*Θ.lag n ω)+S.gamma/total S*Θ.minimizer ω=_
  have he : (∑n∈S.lags,normalizedWeight S n*Θ.lag n ω)=
      (∑n∈S.lags,S.weight n*Θ.lag n ω)/total S := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [normalizedWeight,ite_eq_left hn]
    ring
  rw [he]
  unfold CertificateSymbol.eval
  ring

theorem strict_total_pos {Θ : Curve} {𝒩 : Set ℤ} (S : StrictSymbol Θ 𝒩) :
    0<total S.symbol := by
  have hs : 0≤∑n∈S.symbol.lags,S.symbol.weight n :=
    Finset.sum_nonneg S.symbol.weight_nonneg
  unfold total
  linarith [S.gamma_pos]

def normalizeStrict {Θ : Curve} {𝒩 : Set ℤ} (S : StrictSymbol Θ 𝒩) : Weights 𝒩 :=
  normalizeWeights S.symbol (strict_total_pos S)

theorem normalizeStrict_nonpos {Θ : Curve} {𝒩 : Set ℤ} (S : StrictSymbol Θ 𝒩) (ω : Frequency) :
    (normalizeStrict S).eval Θ ω≤0 := by
  rw [normalizeStrict,normalizeWeights_eval]
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith [S.strict ω,S.epsilon_pos]
  · exact (strict_total_pos S).le

end polyak.Global.Symbols
