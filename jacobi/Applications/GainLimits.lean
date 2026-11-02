import jacobi.Applications.EndpointLimit
import jacobi.Applications.NesterovGain
import jacobi.Applications.UniformBlockGain

/-!
Article: jacobi, Theorem 5.1.
Nonnegative genuine gains are recovered from their normalized squares.
Exact finite gain identities give the canonical leading constants and
the claimed ratio, independently of any numerical experiment.
Use: BlockComparison combines the canonical upper gain with the full-fibre
endpoint lower bound to obtain the optimal source constant.
-/
namespace jacobi.Applications
noncomputable section
open Filter Real
open scoped Topology
set_option maxHeartbeats 1000000

/-- Normalizing a nonnegative gain by the square root of the cubic horizon is exactly the square root of its normalized squared gain.
Use: gain_limit_of_square recovers the genuine nonnegative gain from its actual finite squared identity.
Article: jacobi, Theorem 5.1.
Source: the nonnegative real square root and positive real powers.
Proof: the cubic square root is the cube of the nonnegative square root; its value equals the real 3/2 power. Then use the exact square-root quotient identity. -/
theorem gain_normalization {g x:ℝ} (hg:0≤g) (hx:0≤x) :
    g/x^((3:ℝ)/2)=sqrt (g^2/x^3) := by
  rw [sqrt_div (sq_nonneg _),sqrt_sq hg]
  congr 1
  rw [rpow_div_two_eq_sqrt _ hx,rpow_ofNat]
  have h: sqrt (x^3)^2=(sqrt x^3)^2:=by
    rw [sq_sqrt (pow_nonneg hx _),← pow_mul,show 3*2=2*3 by omega,pow_mul,sq_sqrt hx]
  exact (sq_eq_sq₀ (pow_nonneg (sqrt_nonneg _) _) (sqrt_nonneg _)).mp h.symm

/-- A genuine nonnegative gain inherits its sharp leading constant from the limit of its actual normalized square.
Use: applies to both actual Nesterov and canonical block gains, with the original application count.
Article: jacobi, Theorem 5.1.
Proof: the exact real normalization identity turns the sequence into the continuous square root of its normalized squared gain. -/
theorem gain_limit_of_square {g x:ℕ→ℝ} {c:ℝ} (hg:∀n,0≤g n) (hx:∀n,0≤x n)
    (h:Tendsto (fun n=>g n^2/x n^3) atTop (𝓝 c)) :
    Tendsto (fun n=>g n/x n^((3:ℝ)/2)) atTop (𝓝 (sqrt c)) := by
  simpa only [gain_normalization (hg _) (hx _)] using h.sqrt

/-- The original b=1 Nesterov full spectral gain has leading coefficient 1/sqrt(30).
Use: canonical_block_gain_ratio compares genuine methods with the same application count.
Article: jacobi, Theorem 5.1.
Proof: the original full gain equals its endpoint gain, whose general-momentum limit at b=1 is already proved for the actual realization. Take the nonnegative square root. -/
theorem nesterov_gain_limit :
    Tendsto (fun k:ℕ=>unitSpectralGain (nesterovMethod 1) k/(k:ℝ)^((3:ℝ)/2))
      atTop (𝓝 (1/sqrt 30)) := by
  have h:=endpoint_gain_limit (b:=1) (by norm_num)
  norm_num at h
  simp only [← nesterov_gain_eq_endpoint] at h
  have hn (k:ℕ):0≤unitSpectralGain (nesterovMethod 1) k:=
    (sqrt_nonneg _).trans (unitSpectralGain_ge _ _ ⟨le_rfl,by norm_num⟩ ⟨le_rfl,by norm_num⟩)
  have he:sqrt (1/30:ℝ)=1/sqrt 30:=by rw [sqrt_div (by norm_num),sqrt_one]
  rw [← he]
  exact gain_limit_of_square hn (fun _=>Nat.cast_nonneg _) h

end
end jacobi.Applications
