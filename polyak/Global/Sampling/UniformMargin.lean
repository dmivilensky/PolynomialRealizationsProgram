import polyak.Global.Sampling.SmallScale
import polyak.Global.Kernels.Oscillation

/-! The actual source kernel and the exact quadratic cutoff give a single
positive smoothed margin over all nonzero integer lags. -/
noncomputable section
namespace polyak.Global.Sampling
open Kernels

theorem uniform_margin_from_smoothing {c0 M R : ℝ}
    (hc0:0<c0) (hM:0≤M) (hR:0≤R) (μ:ℤ→ℝ) (out:ℝ→ℤ→ℝ) (minOut:ℝ→ℝ)
    (hμ:∀n,0≤μ n)
    (hstrict:∀n∈lowLagSet (lagCutoff (gainConstant*c0) (6*M*mPhi) (8*M^2*mPhi+R)),0<μ n)
    (hsmooth:∀ε,0<ε→ε<Real.pi→∀n:ℤ,
      kernelHat ε n*μ n+(1-kernelHat ε n)*c0-oscillation ε M 0-
        3*oscillation ε M n-R*ε^2≤out ε n)
    (hmin:∀ε,0<ε→ε<Real.pi→c0-oscillation ε M 0-R*ε^2/2≤minOut ε) :
    ∃ε δ:ℝ,0<ε ∧ ε<Real.pi ∧ 0<δ ∧ 0<minOut ε ∧ ∀n:ℤ,n≠0→δ≤out ε n := by
  have hmPhi:=mPhi_pos
  let N:=lagCutoff (gainConstant*c0) (6*M*mPhi) (8*M^2*mPhi+R)
  obtain ⟨ε,a,hε,hpi,ha,hcut,hhigh,hsmall,hlo⟩:=
    exists_small_sampling_scale gainConstant_pos hc0 μ hstrict
  have hDfine (n:ℤ) : oscillation ε M n≤2*M*mPhi*ε^2*(|(n:ℝ)|+M) := by
    have hh:=oscillation_bound hε.le hM (n:ℝ)
    have hm:=mul_le_mul_of_nonneg_left (min_le_left (2*mPhi*ε^2*(|(n:ℝ)|+M)) ε) hM
    nlinarith only [hh,hm]
  have hDcoarse (n:ℤ) : oscillation ε M n≤M*ε :=
    (oscillation_bound hε.le hM n).trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hM)
  have hlow (n:ℤ) (hn:n≠0) (habs:|(n:ℝ)|<(N:ℝ)) :
      a≤μ n ∧ 1/2≤kernelHat ε n ∧ oscillation ε M 0+3*oscillation ε M n+R*ε^2≤a/4 := by
    have hnset : n∈lowLagSet N:=⟨hn,habs⟩
    obtain ⟨h1,h2,h3⟩:=hlo n hnset
    refine ⟨h1,h2,?_⟩
    have hD0:=hDfine 0
    have hDn:=hDfine n
    simp only [Int.cast_zero,abs_zero,zero_add] at hD0
    have hprod : 6*M*mPhi*ε^2*|(n:ℝ)|≤6*M*mPhi*ε^2*(N:ℝ) :=
      mul_le_mul_of_nonneg_left habs.le (by positivity)
    change (8*M^2*mPhi+6*M*mPhi*(N:ℝ)+R)*ε^2≤a/4 at h3
    nlinarith only [hD0,hDn,hprod,h3]
  obtain ⟨δ,hδ,hbound⟩:=three_range_margin gainConstant_pos hc0 mPhi_pos.le hR hε ha
    (fun n=>kernelHat ε n) μ (out ε) (fun n=>oscillation ε M n)
    (fun n=>kernelHat_mem ε n) (fun n=>kernelHat_gain ε n) hμ
    (by simpa only [Int.cast_zero] using hsmooth ε hε hpi) hDfine hDcoarse hhigh (by simpa only [Int.cast_zero] using hlow)
  refine ⟨ε,δ,hε,hpi,hδ,?_,hbound⟩
  have hD0:=hDfine 0
  simp only [Int.cast_zero,abs_zero,zero_add] at hD0
  have hmin0:=hmin ε hε hpi
  nlinarith only [hmin0,hD0,hsmall,hc0]

end polyak.Global.Sampling
