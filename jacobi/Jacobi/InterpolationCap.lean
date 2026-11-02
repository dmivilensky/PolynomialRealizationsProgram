import jacobi.Jacobi.Interpolation
import jacobi.Jacobi.CoarseAngularError

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Every actual first-half interpolation segment stays inside the angular
region of the proved support derivative envelope. The sharper cap follows
from the already proved uniform phase error, before affine correction.
The physical angular coordinate exists on every original segment.
Use: firstHalf_interpolation_cap leaves the fixed margin needed to apply the support angular derivative envelope after the genuine affine correction.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Bessel jacobi.Oscillation
open scoped Topology

/-- Both original first-half angle lists eventually lie below two thirds of pi, uniformly over their full growing index range.
Use: firstHalf_interpolation_cap leaves the fixed margin needed to apply the support angular derivative envelope after the genuine affine correction.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the model phase is at most pi*N/2 plus a fixed constant. The proved actual angle error is at most A/N, uniformly even at the first index. A single original frequency threshold makes their sum at most 2*pi/3. -/
theorem firstHalf_sharp_cap {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∀ᶠn:ℕ in atTop,∀k:ℕ,2*k<n→
      modelAngle a b n k≤2*π/3 ∧ finiteAngleAt a b ha hb n k≤2*π/3 := by
  -- The threshold depends only on the two fixed parameters, not on the growing index.
  obtain ⟨A,hA,herror⟩ := firstHalf_angle_coarse ha hb
  let S : ℝ := |a|+|b|+2
  have hS : 0<S := by dsimp [S]; positivity
  have hlarge := (frequency_tendsto a b).eventually
    (eventually_ge_atTop (6*(π*S+A)/π+1))
  filter_upwards [herror,hlarge] with n hn hN
  intro k hk
  have hfreq := hn.1
  have hkr : (1:ℝ)≤k+1 := by linarith [Nat.cast_nonneg k (α:=ℝ)]
  have herr : A/(frequency a b n*(k+1:ℝ))≤A/frequency a b n := by
    apply (div_le_div_iff₀ (by positivity : 0<frequency a b n*(k+1:ℝ)) hfreq).mpr
    nlinarith [mul_nonneg (mul_pos hA hfreq).le (sub_nonneg.mpr hkr)]
  have hdist := (abs_le.mp (hn.2 k hk)).2.trans herr
  have hphase := firstHalf_phase_upper a b hk
  have hm : modelAngle a b n k≤π/2+π*S/frequency a b n := by
    change phaseGrid a k/frequency a b n≤_
    apply (div_le_iff₀ hfreq).mpr
    have he : (π/2+π*S/frequency a b n)*frequency a b n=π*frequency a b n/2+π*S := by field_simp
    rw [he]
    exact hphase
  have hNpi : 6*(π*S+A)≤π*frequency a b n := by
    have hh := mul_le_mul_of_nonneg_right hN pi_pos.le
    field_simp [pi_ne_zero] at hh
    nlinarith only [hh,pi_pos]
  have hcombined : (π*S+A)/frequency a b n≤π/6 :=
    (div_le_iff₀ hfreq).mpr (by linarith)
  have hmodel : π*S/frequency a b n≤π/6 :=
    (div_le_div_of_nonneg_right (by linarith : π*S≤π*S+A) hfreq.le).trans hcombined
  exact ⟨by linarith,by rw [add_div] at hcombined; linarith⟩

/-- All physical angles over the actual first-half node interpolation segments lie below the original support derivative cap.
Use: supportPolynomial_segment_bounds can apply the proved original complex wave and derivative estimates on every point of the full source segment.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the sharper original angle cap gives cosine at least -1/2 at both nodes. The true affine scale tends to one and its shift to zero, so the inverse affine coordinate is at least -2/3 at both endpoints and throughout their joining interval. Strict cosine monotonicity then excludes angles at or above 3*pi/4. -/
theorem firstHalf_interpolation_cap {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∀ᶠn:ℕ in atTop,0<modelScale a b n ∧ ∀k:ℕ,2*k<n→∀theta:ℝ,
      theta∈Icc 0 π→modelScale a b n*cos theta+modelShift a b n∈
        uIcc (modelNode a b n k) (cos (finiteAngleAt a b ha hb n k))→theta<3*π/4 := by
  -- The affine correction is controlled before using inverse-cosine monotonicity.
  have hscale := (modelScale_tendsto a b).eventually (Ioi_mem_nhds (by norm_num : (7/8:ℝ)<1))
  have hshift := (modelShift_tendsto a b).abs.eventually (Iio_mem_nhds (by norm_num : |(0:ℝ)|<1/16))
  filter_upwards [firstHalf_sharp_cap ha hb,hscale,hshift] with n hn hsc hsh
  have hs : 0<modelScale a b n := by linarith
  refine ⟨hs,?_⟩
  intro k hk theta ht hx
  have hkn : k<n := by omega
  have hcos (x:ℝ) (hx:0≤x) (hxcap:x≤2*π/3) : -(1/2:ℝ)≤cos x := by
    have h := cos_le_cos_of_nonneg_of_le_pi hx (show 2*π/3≤π by linarith [pi_pos]) hxcap
    rw [show 2*π/3=π-π/3 by ring,cos_pi_sub,cos_pi_div_three] at h
    exact h
  have hmc := hcos _ (modelAngle_endpoint_bounds ha hb hkn).1.1.le (hn k hk).1
  have hac := hcos _ (finiteAngleAt_interval ha hb hkn).1.le (hn k hk).2
  have hactual : -(2/3:ℝ)≤(cos (finiteAngleAt a b ha hb n k)-modelShift a b n)/modelScale a b n := by
    apply (le_div_iff₀ hs).mpr
    nlinarith [(abs_lt.mp hsh).2]
  have hmodel : -(2/3:ℝ)≤(modelNode a b n k-modelShift a b n)/modelScale a b n := by
    unfold modelNode
    rw [add_sub_cancel_right,mul_div_cancel_left₀ _ hs.ne']
    linarith
  have hlower : -(2/3:ℝ)≤cos theta := by
    let l (x:ℝ) := (x-modelShift a b n)/modelScale a b n
    have he (x:ℝ) : l x=(1/modelScale a b n)*x-modelShift a b n/modelScale a b n := by dsimp [l]; ring
    have hm : l (modelNode a b n k)∈Icc (-(2/3:ℝ)) (max (l (modelNode a b n k)) (l (cos (finiteAngleAt a b ha hb n k)))) :=
      ⟨hmodel,le_max_left _ _⟩
    have ha' : l (cos (finiteAngleAt a b ha hb n k))∈Icc (-(2/3:ℝ)) (max (l (modelNode a b n k)) (l (cos (finiteAngleAt a b ha hb n k)))) :=
      ⟨hactual,le_max_right _ _⟩
    simp only [he] at hm ha'
    have hh := (affine_interval_bounds hm ha' hx).1
    have hcoord : (1/modelScale a b n)*(modelScale a b n*cos theta+modelShift a b n)-
        modelShift a b n/modelScale a b n=cos theta := by field_simp [hs.ne']; ring
    have hh' : -(2/3:ℝ)≤(1/modelScale a b n)*(modelScale a b n*cos theta+modelShift a b n)-
        modelShift a b n/modelScale a b n := by simpa only [sub_eq_add_neg] using hh
    rwa [hcoord] at hh'
  by_contra hcap
  have hmono := cos_le_cos_of_nonneg_of_le_pi (show 0≤3*π/4 by positivity) ht.2 (le_of_not_gt hcap)
  rw [show 3*π/4=π-π/4 by ring,cos_pi_sub,cos_pi_div_four] at hmono
  nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg (2:ℝ)]

end
end jacobi.Jacobi
