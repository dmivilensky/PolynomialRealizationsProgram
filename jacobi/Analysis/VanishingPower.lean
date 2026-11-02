import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
Article: jacobi, Proposition A.1.
Source: differentiability of the complex logarithm at one.
Use: nesterov_landweber_joint_limit proves local uniform disappearance of the actual Landweber factor with its growing source exponent.
-/
namespace jacobi.Analysis
noncomputable section
open Complex Filter
open scoped Topology

/-- A vanishing complex increment remains negligible after a variable natural power if the exponent times the increment vanishes.
Use: nesterov_landweber_joint_limit proves local uniform disappearance of the actual Landweber factor with its growing source exponent.
Article: jacobi, Proposition A.1.
Source: the elementary logarithmic limit log(1-u)=-u+o(u).
Proof: use the continuous removable differential slope of log at one. The exponent times the logarithm tends to zero, and exponentiation recovers the original natural power once 1-u is nonzero. -/
theorem vanishing_power {ι : Type*} {l : Filter ι} {u : ι → ℂ} {d : ι → ℕ}
    (hu : Tendsto u l (𝓝 0))
    (hdu : Tendsto (fun i => (d i:ℂ)*u i) l (𝓝 0)) :
    Tendsto (fun i => (1-u i)^(d i)) l (𝓝 1) := by
  -- The removable slope includes u=0, so no exclusion of the complex origin is needed.
  have hb : Tendsto (fun i => 1-u i) l (𝓝 (1:ℂ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hu
  have hs := (continuousAt_dslope_same.mpr
    (Complex.differentiableAt_log (by simp : (1:ℂ)∈slitPlane))).tendsto.comp hb
  have hlog : Tendsto (fun i => (d i:ℂ)*log (1-u i)) l (𝓝 0) := by
    have h := hdu.neg.mul hs
    simp only [neg_zero,zero_mul] at h
    convert h using 1
    funext i
    have hi := sub_smul_dslope Complex.log (1:ℂ) (1-u i)
    simp only [sub_sub_cancel_left,log_one,sub_zero,smul_eq_mul] at hi
    dsimp only [Function.comp_def]
    linear_combination -(d i:ℂ)*hi
  have h := Complex.continuous_exp.continuousAt.tendsto.comp hlog
  simp only [exp_zero] at h
  apply h.congr'
  filter_upwards [hb.eventually_ne one_ne_zero] with i hi
  dsimp only [Function.comp_def]
  rw [Complex.exp_nat_mul,Complex.exp_log hi]

end
end jacobi.Analysis
