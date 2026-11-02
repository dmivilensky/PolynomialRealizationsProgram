import jacobi.Jacobi.ZeroTransfer
import jacobi.Jacobi.AnalyticStability
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
The actual scaled Jacobi family is eventually injective on one complex
disk around each genuine simple Bessel zero. That disk eventually
contains exactly one complex zero, and the zero is real.
Source: a quantitative mean-value argument, the community Weierstrass
derivative theorem and the genuine real sign-change transfer.
Use: gives genuine local uniqueness of all complex finite Jacobi zeros, rather than only their real approximations.
-/
namespace jacobi.Jacobi
noncomputable section
open Complex Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A complex function whose derivative stays closer to a fixed nonzero scalar than that scalar's norm is injective on the convex domain.
Use: gives genuine local uniqueness of all complex finite Jacobi zeros, rather than only their real approximations.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: subtract the fixed linear map. Its derivative norm is bounded
by C, so the mean value theorem bounds its increments by C times distance.
Two equal original values would instead make that increment have the
larger slope norm(d), forcing the two input points to coincide. -/
theorem injective_on_of_deriv_close {f dF : ℂ → ℂ} {S : Set ℂ} {d : ℂ} {C : ℝ}
    (hS : Convex ℝ S) (hf : ∀ z∈S,HasDerivAt f (dF z) z)
    (hbound : ∀ z∈S,‖dF z-d‖≤C) (hC : C<‖d‖) : InjOn f S := by
  -- Apply the mean value theorem to the genuine residual from the fixed linear comparison.
  intro x hx y hy heq
  have h := hS.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => ((hf z hz).sub ((hasDerivAt_id z).const_mul d)).hasDerivWithinAt)
    (by simpa only [mul_one] using hbound) hx hy
  change ‖(f y-d*y)-(f x-d*x)‖≤C*‖y-x‖ at h
  have he : (f y-d*y)-(f x-d*x)= -d*(y-x) := by rw [heq]; ring
  rw [he,norm_mul,norm_neg] at h
  have hz : ‖y-x‖=0 := by nlinarith [norm_nonneg (y-x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

/-- Near every actual simple complex Bessel zero, the genuine scaled Jacobi functions are eventually injective on one fixed closed disk.
Use: proves complex uniqueness of the finite zero selected by real Mehler--Heine transfer.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: the true limiting derivative is nonzero and continuous, hence
close to its central value on one closed disk. The proved compact-uniform
derivative limit makes every finite derivative close there too. Their
combined error is below half the central slope norm, so the quantitative
mean-value injectivity theorem applies. -/
theorem scaled_injective_near_zero {a b z : ℂ} (ha : -1<a.re)
    (hz : jacobi.Bessel.normalized a z=0) :
    ∃ r:ℝ,0<r ∧ ∀ᶠ n:ℕ in atTop,
      InjOn (fun w : ℂ => normalized a b n (1-w/(2*(n:ℂ)^2))) (Metric.closedBall z r) := by
  -- The central slope is that of the same actual entire Bessel function.
  let d := deriv (jacobi.Bessel.normalized a) z
  have hd : 0<‖d‖ := norm_pos_iff.mpr (jacobi.Bessel.normalized_zero_simple ha hz)
  have hD := (jacobi.Bessel.normalized_analytic a z).deriv.continuousAt
  have hN : ∀ᶠ w in 𝓝 z,‖deriv (jacobi.Bessel.normalized a) w-d‖<‖d‖/4 := by
    have h := (hD.sub_const d).norm.eventually (Iio_mem_nhds (show ‖d-d‖<‖d‖/4 by
      rw [sub_self,norm_zero]
      positivity))
    exact h
  obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hN
  refine ⟨r,hr,?_⟩
  have hU := mehler_heine_deriv_uniform (b := b) ha (isCompact_closedBall z r)
  have herror := (Metric.tendstoUniformlyOn_iff.mp hU) (‖d‖/4) (by positivity)
  filter_upwards [herror] with n hn
  apply injective_on_of_deriv_close
    (dF := deriv (fun v : ℂ => normalized a b n (1-v/(2*(n:ℂ)^2))))
    (d := d) (C := ‖d‖/2) (convex_closedBall z r) ?_ ?_ (by linarith)
  · intro w _
    have harg : DifferentiableAt ℂ (fun v : ℂ => 1-v/(2*(n:ℂ)^2)) w := by fun_prop
    have hcomp := (normalized_analytic a b n (1-w/(2*(n:ℂ)^2))).differentiableAt.comp w harg
    exact hcomp.hasDerivAt
  · intro w hw
    have he : ‖deriv (fun v : ℂ => normalized a b n (1-v/(2*(n:ℂ)^2))) w-
        deriv (jacobi.Bessel.normalized a) w‖<‖d‖/4 := by
      simpa only [dist_eq_norm,norm_sub_rev] using hn w hw
    have ht := norm_add_le
      (deriv (fun v : ℂ => normalized a b n (1-v/(2*(n:ℂ)^2))) w-
        deriv (jacobi.Bessel.normalized a) w)
      (deriv (jacobi.Bessel.normalized a) w-d)
    rw [sub_add_sub_cancel] at ht
    have hb : ‖deriv (jacobi.Bessel.normalized a) w-d‖<‖d‖/4 := hball hw
    linarith

/-- Each actual real Bessel spectral zero has a fixed complex disk eventually containing exactly one genuine scaled Jacobi zero, which is real.
Use: the full local existence-and-uniqueness statement behind the ordered finite-edge zero transfer.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: the fixed disk is eventually an injectivity domain. Real
Mehler--Heine transfer supplies a genuine real finite zero within half
its radius. Any other complex zero in the disk has the same finite
function value and therefore coincides with that real zero. -/
theorem scaled_zero_locally_unique {a b x : ℝ} (ha : -1<a)
    (hx : jacobi.Bessel.normalized (a:ℂ) (x:ℂ)=0) :
    ∃ r:ℝ,0<r ∧ ∀ᶠ n:ℕ in atTop,∃ u:ℝ,|(u-x)|<r ∧
      normalized (a:ℂ) (b:ℂ) n (1-(u:ℂ)/(2*(n:ℂ)^2))=0 ∧
      ∀ z∈Metric.closedBall (x:ℂ) r,
        normalized (a:ℂ) (b:ℂ) n (1-z/(2*(n:ℂ)^2))=0 → z=(u:ℂ) := by
  -- The existence proof supplies realness; injectivity excludes every additional complex zero.
  obtain ⟨r,hr,hinj⟩ := scaled_injective_near_zero (b := (b:ℂ)) (by simpa using ha) hx
  have hex := scaled_zero_approximation (b := b) ha hx (show 0<r/2 by positivity)
  refine ⟨r,hr,?_⟩
  filter_upwards [hinj,hex] with n hnI hnE
  obtain ⟨u,hu,hzero⟩ := hnE
  have hfinite : normalized (a:ℂ) (b:ℂ) n (1-(u:ℂ)/(2*(n:ℂ)^2))=0 := by
    have he : ((1-u/(2*(n:ℝ)^2):ℝ):ℂ)=1-(u:ℂ)/(2*(n:ℂ)^2) := by push_cast; rfl
    rwa [he] at hzero
  have hmem : (u:ℂ)∈Metric.closedBall (x:ℂ) r := by
    rw [Metric.mem_closedBall,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    linarith
  refine ⟨u,by linarith,hfinite,?_⟩
  intro z hz hz0
  exact hnI hz hmem (hz0.trans hfinite.symm)

end
end jacobi.Jacobi
