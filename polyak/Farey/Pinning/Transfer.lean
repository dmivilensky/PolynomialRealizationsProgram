import polyak.Farey.Pinning.Basic
import polyak.Global.Sampling.AnalyticBranch

/-! Moving weights between pinning classes keeps all grid values and
changes slopes by precisely the two pinning differences. -/
noncomputable section
namespace polyak.Farey.Pinning
open Levels

def tiltedSymbol (K p:ℕ) (θ F:ℝ→ℝ) (a b x:ℝ) : ℝ:=
  F x+a*differenceD K p θ x+b*differenceE K p θ x

theorem tiltedSymbol_grid (K p:ℕ) {ω:Frequency} (hω:ω∈periodicGrid (period K p))
    (θ F:ℝ→ℝ) (a b:ℝ) : tiltedSymbol K p θ F a b ω=F ω := by
  simp only [tiltedSymbol,differenceD_grid K p hω,differenceE_grid K p hω,mul_zero,add_zero]

theorem hasDerivAt_tiltedSymbol (K p:ℕ) {ω:Frequency} (hω:ω∈periodicGrid (period K p))
    {θ F:ℝ→ℝ} {dθ dF a b:ℝ} (hθ:HasDerivAt θ dθ (ω:ℝ)) (hF:HasDerivAt F dF (ω:ℝ)) :
    HasDerivAt (tiltedSymbol K p θ F a b)
      (dF-a*(period K p:ℝ)*Real.sin ((ω:ℝ)-θ ω)-
        b*(period K p:ℝ)*Real.sin ((K:ℝ)*(ω:ℝ)+θ ω)) (ω:ℝ) := by
  have hh:=(hF.add ((hasDerivAt_differenceD K p hω hθ).const_mul a)).add
    ((hasDerivAt_differenceE K p hω hθ).const_mul b)
  convert hh using 1
  · rfl
  · ring

theorem transfer_nonnegative_weights {w1 wK a b:ℝ}
    (ha:0≤a) (ha1:a≤w1) (hb:0≤b) (hbK:b≤wK) :
    0≤w1-a ∧ 0≤a ∧ 0≤wK-b ∧ 0≤b :=
  ⟨sub_nonneg.mpr ha1,ha,sub_nonneg.mpr hbK,hb⟩

theorem transfer_identity (K p:ℕ) (θ:ℝ→ℝ) (w1 wK a b γ x:ℝ) :
    (w1-a)*realLag θ 1 x+a*realLag θ (-((p:ℤ)*K)) x+
      (wK-b)*realLag θ (-(K:ℤ)) x+b*realLag θ (((p:ℤ)-1)*K+1) x+γ*Real.cos (θ x)=
      tiltedSymbol K p θ
        (fun x=>w1*realLag θ 1 x+wK*realLag θ (-(K:ℤ)) x+γ*Real.cos (θ x)) a b x := by
  unfold tiltedSymbol differenceD differenceE
  ring

theorem pinning_lemma (K p:ℕ) {ω:Frequency} (hω:ω∈periodicGrid (period K p))
    {θ:ℝ→ℝ} {d:ℝ} (hd:HasDerivAt θ d (ω:ℝ)) :
    differenceD K p θ ω=0 ∧ differenceE K p θ ω=0 ∧
      deriv (differenceD K p θ) ω= -(period K p:ℝ)*Real.sin ((ω:ℝ)-θ ω) ∧
      deriv (differenceE K p θ) ω= -(period K p:ℝ)*Real.sin ((K:ℝ)*(ω:ℝ)+θ ω) :=
  ⟨differenceD_grid K p hω θ,differenceE_grid K p hω θ,
    (hasDerivAt_differenceD K p hω hd).deriv,(hasDerivAt_differenceE K p hω hd).deriv⟩

theorem pinning_at_tuning (q:General.Tuning) (K p:ℕ) {ω:Frequency}
    (hω:ω∈periodicGrid (period K p)) :
    differenceD K p (Global.Sampling.phaseBranch q 0) ω=0 ∧
      differenceE K p (Global.Sampling.phaseBranch q 0) ω=0 ∧
      deriv (differenceD K p (Global.Sampling.phaseBranch q 0)) ω=
        -(period K p:ℝ)*Real.sin ((ω:ℝ)-q.angle ω) ∧
      deriv (differenceE K p (Global.Sampling.phaseBranch q 0)) ω=
        -(period K p:ℝ)*Real.sin ((K:ℝ)*(ω:ℝ)+q.angle ω) := by
  have hh:=pinning_lemma K p hω
    ((Global.Sampling.analyticAt_phaseBranch q 0 ω.property).differentiableAt.hasDerivAt)
  simpa only [Global.Sampling.phaseBranch_actual q 0 ω.property,←Geometry.shiftedCurve_apply,Geometry.shiftedCurve_zero,tuningCurve_apply] using hh

end polyak.Farey.Pinning
