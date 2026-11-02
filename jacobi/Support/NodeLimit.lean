import jacobi.Support.AffineScale
import jacobi.Jacobi.CorrectedDistance

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Every fixed original corrected support node has precisely the actual
Poeschl--Teller reference squared-distance limit. The proof uses the
literal model node and affine correction, independently of support
polynomial or weight asymptotics.
Use: supportNode_limit gives the full printed corrected support-node limit without a support asymptotic certificate.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The actual original cosine-grid squared distance has its exact indexed reference-phase limit.
Use: supportNode_limit gives the full printed corrected support-node limit without a support asymptotic certificate.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the actual grid angle tends to zero. Its exact half-angle identity writes the squared distance as the fixed original phase squared times sinc(angle/2)^2, whose limit is one. -/
theorem naturalNode_distance_limit (a b : ℝ) (k : ℕ) :
    Tendsto (fun n:ℕ => 2*(jacobi.Jacobi.frequency a b n)^2*
      (1-cos (jacobi.Jacobi.modelAngle a b n k))) atTop
      (𝓝 ((jacobi.Bessel.phaseGrid a k)^2)) := by
  -- The sinc normalization proves the exact leading constant without differentiating a moving complex or singular expression.
  have hangle : Tendsto (fun n:ℕ => jacobi.Jacobi.modelAngle a b n k/2) atTop (𝓝 (0:ℝ)) := by
    simpa only [zero_div,jacobi.Jacobi.modelAngle] using
      (tendsto_const_nhds.div_atTop (jacobi.Jacobi.frequency_tendsto a b)).div_const 2
  have hsinc := Real.continuous_sinc.continuousAt.tendsto.comp hangle
  simp only [Real.sinc_zero,Function.comp_def] at hsinc
  have ht := (hsinc.pow 2).const_mul ((jacobi.Bessel.phaseGrid a k)^2)
  simp only [one_pow,mul_one] at ht
  apply (tendsto_congr' ?_).mpr ht
  filter_upwards [(jacobi.Jacobi.frequency_tendsto a b).eventually (eventually_gt_atTop (0:ℝ))] with n hn
  have hcos : cos (jacobi.Jacobi.modelAngle a b n k)=1-2*sin (jacobi.Jacobi.modelAngle a b n k/2)^2 := by
    simpa only [show 2*(jacobi.Jacobi.modelAngle a b n k/2)= jacobi.Jacobi.modelAngle a b n k by ring]
      using Real.cos_two_mul_eq_one_sub (jacobi.Jacobi.modelAngle a b n k/2)
  have hsin (x : ℝ) : sin x=x*sinc x := by
    by_cases hx:x=0
    · simp [hx]
    · rw [sinc_of_ne_zero hx,mul_div_cancel₀ _ hx]
  rw [hcos,hsin]
  dsimp [jacobi.Jacobi.modelAngle]
  field_simp [hn.ne']
  ring

/-- The actual corrected original support nodes have exactly the genuine reference operator eigenvalue limit at every fixed original source index.
Use: support weight asymptotics and the original target/support norming ratios compare the same actual support and Jacobi-zero edge spectra.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the genuine natural cosine-grid distance has its exact phase-squared limit. The actual affine scale tends to one, and its independently proved exact endpoint correction adds precisely c_0alpha. -/
theorem supportNode_limit {a b : ℝ} (ha : -1<a) (hb : -1<b) (k : ℕ) :
    Tendsto (fun n:ℕ => 2*(jacobi.Jacobi.frequency a b n)^2*(1- jacobi.Jacobi.modelNode a b n k))
      atTop (𝓝 (eigenvalue a k)) := by
  -- The correction is an exact original finite identity, before passing to the limit.
  have ht := ((jacobi.Jacobi.modelScale_tendsto a b).mul (naturalNode_distance_limit a b k)).add_const
    (jacobi.Jacobi.endpointCorrection a)
  simp only [one_mul] at ht
  have he : (jacobi.Bessel.phaseGrid a k)^2+ jacobi.Jacobi.endpointCorrection a=eigenvalue a k := by
    rw [phaseGrid_eq]
    dsimp [eigenvalue]
    ring
  rw [he] at ht
  apply (tendsto_congr' ?_).mpr ht
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have h := affine_endpoint_correction ha hb hn
  dsimp [jacobi.Jacobi.modelNode]
  linear_combination h

end
end jacobi.Support
