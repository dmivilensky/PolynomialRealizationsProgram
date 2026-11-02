import jacobi.Hankel.BesselDecomposition
import jacobi.Bessel.Zeros

/-!
Article: jacobi, Lemma E.1.
Use: after the true relative phase is fixed, the outgoing coefficient is nonzero and the original Bessel zero equation may be divided by its actual leading amplitude on a common neighborhood.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter jacobi.Bessel
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual original Bessel-Jost coefficients never both vanish anywhere in their genuine admissible complex-order half-contraction domain.
Use: after the true relative phase is fixed, the outgoing coefficient is nonzero and the original Bessel zero equation may be divided by its actual leading amplitude on a common neighborhood.
Article: jacobi, Lemma E.1.
Proof: simultaneous zero coefficients would make the original Bessel Liouville wave vanish on the entire genuine ray. Its actual derivative at R+1 would also be zero; the nonzero exponential prefactor and spatial coordinate then force both the original entire Bessel function and its spectral derivative to vanish, contradicting the proved simplicity of its actual zeros. -/
theorem besselConnection_nontrivial {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : -1<a.re) (hc : ‖besselCoefficient a‖/R≤1/2) :
    outgoingBesselCoefficient hR a≠0 ∨ incomingBesselCoefficient hR a≠0 := by
  -- Original Bessel zero simplicity rules out a spurious vanishing asymptotic basis coefficient pair.
  by_contra hn
  push Not at hn
  have hz (x : ℝ) (hx : R<x) : complexBesselWave a x=0 := by
    rw [bessel_decomposition hR ha hc hx,hn.1,hn.2]
    ring
  let x : ℝ := R+1
  have hx : R<x := by dsimp [x]; linarith
  have hxp : 0<x := hR.trans hx
  have hd0 : HasDerivAt (complexBesselWave a) 0 x := by
    apply (hasDerivAt_const x (0:ℂ)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hz y hy
  have hs : complexBesselWaveSlope a x=0 :=
    (complexBesselWave_hasDerivAt a hxp).unique hd0
  have hF : normalized a ((x:ℂ)^2)=0 := (complexBesselWave_zero_iff a x).mp (hz x hx)
  have hP : complexWaveFactor a x≠0 := Complex.exp_ne_zero _
  have hG : deriv (normalized a) ((x:ℂ)^2)=0 := by
    rw [complexBesselWaveSlope,hF,mul_zero,zero_add] at hs
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hs).resolve_left hP)).resolve_left
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hxp.ne'))
  exact (normalized_zero_simple ha hF) hG

end
end jacobi.Hankel
