import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
Article: jacobi, Theorem 2.1.
Compactly supported tests permit two integrations by parts against a function
which is only C2 in the physical interior.
Source: the classical Green identity for compactly supported test functions.
Use: compact_test_second_derivative supplies the coefficient identity placing
every compactly supported C2 test in the actual target spectral domain.
-/
namespace jacobi.Analysis
noncomputable section
open Set Filter MeasureTheory Function
open scoped Topology

/-- A continuous supported factor removes every possible singularity outside
the open set where the other factor is continuous.
Use: compact_test_second_derivative makes the Wronskian and its derivative
integrable without imposing regularity at either singular endpoint.
Article: jacobi, Theorem 2.1.
Proof: inside the support both factors are continuous; outside it the product
vanishes on a neighborhood. -/
theorem continuous_supported_mul {f g : ℝ → ℝ} {U : Set ℝ}
    (hf : Continuous f) (hU : IsOpen U) (hs : tsupport f ⊆ U)
    (hg : ContinuousOn g U) : Continuous (fun x => f x*g x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport f
  · exact (hf.continuousAt.mul (hg.continuousAt (hU.mem_nhds (hs hx))))
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hx)] with y hy
    simp [hy]

/-- Two integrations by parts for a compactly supported C2 test and an
arbitrary C2 function on a neighborhood of its support.
Use: the target eigenfunction equation then identifies every actual Fourier
coefficient of the differential expression, hence its full spectral domain.
Article: jacobi, Proposition C.2.
Source: Green's second identity, with vanishing compact-support boundary terms.
Proof: the actual Wronskian is differentiable everywhere, including outside
the physical interval where the test vanishes locally. Both it and its
derivative are continuous with compact support, so the integral of its
derivative is zero. -/
theorem compact_test_second_derivative {f g : ℝ → ℝ} {U : Set ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (hU : IsOpen U)
    (hs : tsupport f ⊆ U) (hg : ContDiffOn ℝ 2 g U) :
    (∫ x : ℝ, deriv (deriv f) x*g x) = ∫ x : ℝ, f x*deriv (deriv g) x := by
  have hfd : ContDiff ℝ 1 (deriv f) := (show ContDiff ℝ (1+1) f from hf).deriv'
  have hgd : ContDiffOn ℝ 1 (deriv g) U := hg.deriv_of_isOpen hU (by norm_num)
  have hfdd := hfd.continuous_deriv (by norm_num)
  have hgdd := hgd.continuousOn_deriv_of_isOpen hU (by norm_num)
  have hs1 : tsupport (deriv f) ⊆ U := tsupport_deriv_subset.trans hs
  have hs2 : tsupport (deriv (deriv f)) ⊆ U := tsupport_deriv_subset.trans hs1
  have h1 := continuous_supported_mul hfdd hU hs2 hg.continuousOn
  have h2 := continuous_supported_mul hf.continuous hU hs hgdd
  have hi1 : Integrable (fun x => deriv (deriv f) x*g x) :=
    h1.integrable_of_hasCompactSupport (hc.deriv.deriv.mul_right)
  have hi2 : Integrable (fun x => f x*deriv (deriv g) x) :=
    h2.integrable_of_hasCompactSupport (hc.mul_right)
  -- Compact support makes the actual Wronskian locally zero outside U,
  -- so integration over the whole line never tests a singular endpoint.
  let W := fun x => deriv f x*g x-f x*deriv g x
  have hWc : Continuous W :=
    (continuous_supported_mul hfd.continuous hU hs1 hg.continuousOn).sub
      (continuous_supported_mul hf.continuous hU hs hgd.continuousOn)
  have hWs : HasCompactSupport W := hc.deriv.mul_right.sub hc.mul_right
  have hd (x : ℝ) : HasDerivAt W
      (deriv (deriv f) x*g x-f x*deriv (deriv g) x) x := by
    by_cases hx : x ∈ tsupport f
    · have hu := hs hx
      have hg1 := ((hg x hu).contDiffAt (hU.mem_nhds hu)).differentiableAt (by norm_num)
      have hg2 := ((hgd x hu).contDiffAt (hU.mem_nhds hu)).differentiableAt (by norm_num)
      convert ((hfd.differentiable (by norm_num) x).hasDerivAt.mul hg1.hasDerivAt).sub
        ((hf.differentiable (by norm_num) x).hasDerivAt.mul hg2.hasDerivAt) using 1
      ring
    · have hx1 : x ∉ tsupport (deriv f) := fun h => hx (tsupport_deriv_subset h)
      have he : W =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx,
          notMem_tsupport_iff_eventuallyEq.mp hx1] with y hy hy1
        simp [W,hy,hy1]
      simpa [image_eq_zero_of_notMem_tsupport hx,deriv_of_notMem_tsupport hx1] using
        (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq he
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hd (hi1.sub hi2)
    (hWc.integrable_of_hasCompactSupport hWs)
  rw [integral_sub hi1 hi2] at hz
  exact sub_eq_zero.mp hz

end
end jacobi.Analysis
