import jacobi.Complex.FinitePoleRegularization

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: the classical residue theorem for finitely many simple poles.
Use: the parity residue passage applies this theorem separately to Delta_sigma and Delta_tau, so coincident zeros cause no duplicate-pole issue.
-/
namespace jacobi.Complex
noncomputable section
open _root_.Complex Set Filter Metric
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The normalized circle integral of an analytic quotient with precisely the listed simple denominator zeros is the finite sum of its genuine residues.
Use: the parity residue passage applies this theorem separately to Delta_sigma and Delta_tau, so coincident zeros cause no duplicate-pole issue.
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: the residue theorem for simple poles, derived here from Cauchy's integral formula.
Proof: subtract the actual principal parts and use their analytic removable extensions on the whole disk. Cauchy--Goursat annihilates the regularized integral, and Cauchy's formula integrates each principal part exactly. -/
theorem finite_simple_residues {g h : ℂ → ℂ} (S : Finset ℂ) {c : ℂ} {R : ℝ}
    (hR : 0<R) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hh : AnalyticOnNhd ℂ h (closedBall c R))
    (hinside : ∀ p∈S,p∈ball c R)
    (hzeros : ∀ z∈closedBall c R,h z=0 ↔ z∈S)
    (hsimple : ∀ p∈S,deriv h p≠0) :
    (2*(Real.pi:ℂ)*Complex.I)⁻¹ • (∮ z in C(c,R),g z/h z)=
      ∑ p∈S,g p/deriv h p := by
  classical
  -- The finite regularization is analytic at every original denominator zero, with the genuine residue coefficient.
  have hreg : DifferentiableOn ℂ (finitePoleRegularization g h S) (closedBall c R) := by
    intro z hz
    exact (finitePoleRegularization_analytic S (hg z hz) (hh z hz)
      (fun hp => ⟨(hzeros z hz).mpr hp,hsimple z hp⟩)
      (fun hp h0 => hp ((hzeros z hz).mp h0))).differentiableAt.differentiableWithinAt
  have hzero := (hreg.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hR.le
  have hboundary (z : ℂ) (hz : z∈sphere c R) : z∉S := by
    intro hp
    have hi := Metric.mem_ball.mp (hinside z hp)
    have he := Metric.mem_sphere.mp hz
    linarith
  have hden (z : ℂ) (hz : z∈sphere c R) : h z≠0 := by
    intro h0
    exact hboundary z hz ((hzeros z (sphere_subset_closedBall hz)).mp h0)
  have hquot : CircleIntegrable (fun z => g z/h z) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact ((hg z (sphere_subset_closedBall hz)).continuousAt.div
      (hh z (sphere_subset_closedBall hz)).continuousAt (hden z hz)).continuousWithinAt
  have hpole (p : ℂ) (hp : p∈S) :
      CircleIntegrable (fun z : ℂ => (g p/deriv h p)/(z-p)) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have hzp : z-p≠0 := sub_ne_zero.mpr (by
      intro he
      exact hboundary z hz (he.symm ▸ hp))
    exact (continuousAt_const.div (continuousAt_id.sub_const p) hzp).continuousWithinAt
  have hsum : CircleIntegrable (fun z : ℂ => ∑ p∈S,(g p/deriv h p)/(z-p)) c R := by
    have he : (∑ p∈S,fun z : ℂ => (g p/deriv h p)/(z-p))=
        (fun z : ℂ => ∑ p∈S,(g p/deriv h p)/(z-p)) := by
      funext z
      simp only [Finset.sum_apply]
    exact he ▸ CircleIntegrable.sum S hpole
  have heq : (∮ z in C(c,R),finitePoleRegularization g h S z)=
      (∮ z in C(c,R),g z/h z)-(∮ z in C(c,R),∑ p∈S,(g p/deriv h p)/(z-p)) := by
    rw [← circleIntegral.integral_sub hquot hsum]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    exact ite_eq_right (hboundary z hz)
  have hprincipal (p : ℂ) (hp : p∈S) :
      (∮ z in C(c,R),(g p/deriv h p)/(z-p))=
        (2*(Real.pi:ℂ)*Complex.I)*(g p/deriv h p) := by
    have h := (diffContOnCl_const : DiffContOnCl ℂ (fun _ : ℂ => g p/deriv h p) (ball c R)).circleIntegral_sub_inv_smul (hinside p hp)
    simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using h
  rw [circleIntegral.integral_fun_sum hpole] at heq
  have hsumint : (∑ p∈S,∮ z in C(c,R),(g p/deriv h p)/(z-p))=
      (2*(Real.pi:ℂ)*Complex.I)*(∑ p∈S,g p/deriv h p) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hprincipal
  rw [hsumint] at heq
  have hi : (∮ z in C(c,R),g z/h z)=
      (2*(Real.pi:ℂ)*Complex.I)*(∑ p∈S,g p/deriv h p) := by
    rw [hzero] at heq
    exact sub_eq_zero.mp heq.symm
  rw [hi,smul_eq_mul,← mul_assoc,inv_mul_cancel₀ (by simp [Real.pi_ne_zero]),one_mul]

end
end jacobi.Complex
