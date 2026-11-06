import nesterov.Duality.Certificate
import polyak.General.IQC.CertificateFourier
import polyak.General.IQC.HalfLineCertificate
import polyak.General.IQC.CertificateCoordinates
import polyak.General.IQC.CertificateNorm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
Transport of the already proved interpolation IQC to division-free certificates.
The two-channel time form depends only on the nonnegative weights and their
single cancellation identity. We realize those same weights as an auxiliary
constant-multiplier certificate, then reuse the complete Polyak Fourier proof.
The auxiliary multiplier has no role in the stationary method or its spectrum.
-/
namespace nesterov.IQC
noncomputable section
open scoped BigOperators
open Spectral
variable {a : SymbolPair} {t : ℝ}

/-- Diagonal coefficient of the article's Hermitian IQC. -/
def diagonal (cert : Duality.StrictCertificate a t) (c : Frequency) : ℝ :=
  (∑ n ∈ cert.lags,(cert.α n+cert.β n)*
    (Real.cosh (n*t)-Real.cos (n*Real.arccos c)))+cert.γplus+cert.γminus

theorem diagonal_nonneg (cert : Duality.StrictCertificate a t) (c : Frequency) :
    0≤diagonal cert c := by
  apply add_nonneg _ cert.γminus_nonneg
  apply add_nonneg _ cert.γplus_nonneg
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (add_nonneg (cert.α_nonneg n hn) (cert.β_nonneg n hn))
    (sub_nonneg.mpr ((Real.cos_le_one _).trans (Real.one_le_cosh _)))

theorem positive_weight (cert : Duality.StrictCertificate a t) :
    0<cert.γplus+cert.γminus ∨ ∃ n∈cert.lags,0<cert.α n+cert.β n := by
  by_contra! h
  have hg : cert.γplus=0 ∧ cert.γminus=0 := by
    constructor <;> linarith [cert.γplus_nonneg,cert.γminus_nonneg]
  have hw (n : ℕ) (hn : n∈cert.lags) : cert.α n=0 ∧ cert.β n=0 := by
    have hh:=h.2 n hn
    constructor <;> linarith [cert.α_nonneg n hn,cert.β_nonneg n hn]
  let c : Frequency:=⟨0,by constructor <;> norm_num⟩
  have hs:=cert.strict c
  have hz : Duality.symbol a t cert.lags cert.α cert.β cert.γplus cert.γminus c=0 := by
    unfold Duality.symbol
    rw [hg.1,hg.2]
    simp only [zero_mul,add_zero]
    apply Finset.sum_eq_zero
    intro n hn
    rw [(hw n hn).1,(hw n hn).2]
    ring
  rw [hz] at hs
  linarith [cert.ε_pos]

/-- A strict certificate forces a uniformly positive diagonal, including t=0. -/
theorem exists_diagonal_lower (cert : Duality.StrictCertificate a t) :
    ∃ d : ℝ,0<d ∧ ∀ c : Frequency,d≤diagonal cert c := by
  by_cases ht : t=0
  · subst t
    have hg : 0<cert.γplus+cert.γminus := by
      by_contra! hn
      have hz : cert.γplus+cert.γminus=0 :=
        le_antisymm hn (add_nonneg cert.γplus_nonneg cert.γminus_nonneg)
      let c : Frequency:=⟨1,by constructor <;> norm_num⟩
      have hs:=cert.strict c
      have he : Duality.symbol a 0 cert.lags cert.α cert.β cert.γplus cert.γminus c=0 := by
        simp [Duality.symbol,lagA,lagB,c,hz]
      rw [he] at hs
      linarith [cert.ε_pos]
    refine ⟨cert.γplus+cert.γminus,hg,fun c=>?_⟩
    have hs : 0≤∑ n∈cert.lags,(cert.α n+cert.β n)*
        (Real.cosh (n*(0:ℝ))-Real.cos (n*Real.arccos c)) := by
      apply Finset.sum_nonneg
      intro n hn
      exact mul_nonneg (add_nonneg (cert.α_nonneg n hn) (cert.β_nonneg n hn))
        (sub_nonneg.mpr ((Real.cos_le_one _).trans (Real.one_le_cosh _)))
    dsimp [diagonal]
    linarith
  · rcases positive_weight cert with hg|⟨n,hn,hw⟩
    · refine ⟨cert.γplus+cert.γminus,hg,fun c=>?_⟩
      have hs : 0≤∑ n∈cert.lags,(cert.α n+cert.β n)*
          (Real.cosh (n*t)-Real.cos (n*Real.arccos c)) := by
        apply Finset.sum_nonneg
        intro n hn
        exact mul_nonneg (add_nonneg (cert.α_nonneg n hn) (cert.β_nonneg n hn))
          (sub_nonneg.mpr ((Real.cos_le_one _).trans (Real.one_le_cosh _)))
      dsimp [diagonal]
      linarith
    · have hn0 : (n:ℝ)≠0 := by exact_mod_cast (by have := cert.positive_lag n hn; omega : n≠0)
      have hcosh : 0<Real.cosh (n*t)-1 :=
        sub_pos.mpr (Real.one_lt_cosh.mpr (mul_ne_zero hn0 ht))
      let d:=(cert.α n+cert.β n)*(Real.cosh (n*t)-1)
      refine ⟨d,mul_pos hw hcosh,fun c=>?_⟩
      have hsingle : (cert.α n+cert.β n)*(Real.cosh (n*t)-Real.cos (n*Real.arccos c))≤
          ∑ j∈cert.lags,(cert.α j+cert.β j)*(Real.cosh (j*t)-Real.cos (j*Real.arccos c)) :=
        Finset.single_le_sum (fun j hj=>mul_nonneg
          (add_nonneg (cert.α_nonneg j hj) (cert.β_nonneg j hj))
          (sub_nonneg.mpr ((Real.cos_le_one (j*Real.arccos c)).trans (Real.one_le_cosh (j*t))))) hn
      have hc:=mul_le_mul_of_nonneg_left
        (sub_le_sub_left (Real.cos_le_one (n*Real.arccos c)) (Real.cosh (n*t))) hw.le
      dsimp [d,diagonal]
      linarith [cert.γplus_nonneg,cert.γminus_nonneg]

/-- The auxiliary constant multiplier used only to transport the weight form. -/
def auxiliaryMultiplier : C(Frequency,ℂ):=ContinuousMap.const _ 2

theorem auxiliary_symbol (cert : Duality.StrictCertificate a t) (c : Frequency) :
    polyak.Duality.symbol auxiliaryMultiplier t cert.lags cert.α cert.β cert.γplus cert.γminus c=
      -3*diagonal cert c := by
  have hn : Complex.normSq (2:ℂ)=4 := by norm_num [Complex.normSq_apply]
  have hi : (2:ℂ).im=0 := by norm_num
  simp only [polyak.Duality.symbol,polyak.Duality.a,polyak.Duality.b,polyak.Duality.g,
    auxiliaryMultiplier,ContinuousMap.const_apply,hn,hi,mul_zero,zero_mul,sub_zero,add_zero]
  norm_num only
  unfold diagonal
  rw [mul_add,mul_add,Finset.mul_sum]
  have he (n : ℕ) : cert.α n*(-3*(Real.cosh (n*t)-Real.cos (n*Real.arccos c)))+
      cert.β n*(-3*(Real.cosh (n*t)-Real.cos (n*Real.arccos c)))=
      -3*((cert.α n+cert.β n)*(Real.cosh (n*t)-Real.cos (n*Real.arccos c))) := by ring
  simp only [he]
  ring

/-- Same lags, same multipliers, same cancellation; only the auxiliary negative
margin changes. All inherited time and Fourier forms therefore remain literal. -/
def transported (cert : Duality.StrictCertificate a t) :
    polyak.Duality.StrictCertificate auxiliaryMultiplier t := by
  let d:=Classical.choose (exists_diagonal_lower cert)
  have hd:= (Classical.choose_spec (exists_diagonal_lower cert)).1
  have hbound:= (Classical.choose_spec (exists_diagonal_lower cert)).2
  exact {
    lags:=cert.lags
    positive_lag:=cert.positive_lag
    α:=cert.α
    β:=cert.β
    α_nonneg:=cert.α_nonneg
    β_nonneg:=cert.β_nonneg
    γplus:=cert.γplus
    γminus:=cert.γminus
    γplus_nonneg:=cert.γplus_nonneg
    γminus_nonneg:=cert.γminus_nonneg
    ε:=3*d
    ε_pos:=mul_pos (by norm_num) hd
    cancel:=cert.cancel
    strict:=fun c=>by rw [auxiliary_symbol]; nlinarith [hbound c] }

end
end nesterov.IQC
