import jacobi.Bessel.EdgeData
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
Article: jacobi, Theorem C.5.
The actual slit resolvent domain has a common nonzero denominator
for the complete positive spectral interval, including its zero limit.
Compactness then gives one genuine bound for all original modes.
Source: the spectral resolvent denominator and the extreme-value theorem.
Use: edgeDomain is the actual source domain, and denominator_compact_bound controls the full positive spectral interval uniformly on each compact subset.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Set Real

/-- The original slit plane with the closed negative ray ending at -s removed.
Use: edgeDomain is the actual source domain, and denominator_compact_bound controls the full positive spectral interval uniformly on each compact subset.
Article: jacobi, Theorem C.5.
-/
def slitDomain (s:ℝ) : Set ℂ := {w | w.im≠0 ∨ -s<w.re}

/-- The genuine slit resolvent domain is open.
Use: the actual shifted-profile series is complex differentiable locally throughout the original source domain.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: it is the union of the nonreal plane and the inverse image of the open real interval above -s. -/
theorem slitDomain_open (s:ℝ) : IsOpen (slitDomain s) := by
  have hi : IsOpen {w:ℂ | w.im≠0} := isOpen_ne.preimage Complex.continuous_im
  exact hi.union
    (isOpen_lt continuous_const Complex.continuous_re)

/-- Every original positive spectral resolvent denominator, including the limiting zero spectral value, is nonzero on the actual slit domain.
Use: denominator_compact_bound and the genuine shifted Bessel coefficients have no independently assumed spectral nonvanishing certificate.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: zero x gives denominator one. For positive x, a vanishing denominator forces a real w with w<=-s, contradicting the actual slit condition. -/
theorem slit_denominator_ne {s x:ℝ} (hs:0<s) (hx:x∈Icc 0 (1/s)) {w:ℂ} (hw:w∈slitDomain s) :
    1+(x:ℂ)*w≠0 := by
  -- The full positive spectral interval is handled at once, so its zero accumulation point needs no separate infinite-index assumption.
  intro hzero
  by_cases hx0:x=0
  · simp [hx0] at hzero
  have hxp : 0<x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hi := congrArg Complex.im hzero
  have hr := congrArg Complex.re hzero
  simp only [Complex.add_im,Complex.one_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,add_zero,zero_add,Complex.zero_im] at hi
  simp only [Complex.add_re,Complex.one_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.zero_re] at hr
  have hwi : w.im=0 := (mul_eq_zero.mp hi).resolve_left hx0
  have hxr : x*s≤1 := (le_div_iff₀ hs).mp hx.2
  have hwr : w.re≤-s := by
    apply (mul_le_mul_iff_of_pos_left hxp).mp
    nlinarith only [hr,hxr]
  rcases hw with him | hre
  · exact him hwi
  · exact (not_lt_of_ge hwr) hre

/-- Every compact subset of the actual slit domain has one original resolvent denominator bound for the entire positive spectral interval.
Use: shiftedEdge_compact_bound supplies the genuine summable spectral majorant for Theorem C.5 on each original compact parameter set.
Article: jacobi, Theorem C.5.
Source: the extreme-value theorem on the compact product of the parameter set and the closed positive spectral interval.
Proof: the independently proved denominator is nonzero at every point of the compact product. Its actual inverse norm is continuous there and hence bounded; enlarge the resulting bound to a strictly positive constant. -/
theorem denominator_compact_bound {s:ℝ} (hs:0<s) {W:Set ℂ} (hW:IsCompact W)
    (hsub:W⊆slitDomain s) :
    ∃C:ℝ,0<C ∧ ∀w∈W,∀x∈Icc (0:ℝ) (1/s),‖(1+(x:ℂ)*w)⁻¹‖≤C := by
  -- Compactness includes the actual zero spectral limit, giving one bound for every original mode simultaneously.
  have hcont : ContinuousOn (fun p:ℂ×ℝ => ‖(1+(p.2:ℂ)*p.1)⁻¹‖) (W×ˢIcc (0:ℝ) (1/s)) := by
    intro p hp
    have hne := slit_denominator_ne hs hp.2 (hsub hp.1)
    have hc : ContinuousAt (fun p:ℂ×ℝ => ‖(1+(p.2:ℂ)*p.1)⁻¹‖) p := by fun_prop (disch := exact hne)
    exact hc.continuousWithinAt
  obtain ⟨B,hB⟩ := (hW.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨|B|+1,by positivity,?_⟩
  intro w hw x hx
  have h := hB (w,x) ⟨hw,hx⟩
  simp only [norm_norm] at h
  exact h.trans (by linarith [le_abs_self B])

/-- The source's actual slit domain for its genuine first positive squared Bessel zero.
Use: all shifted coefficient and profile statements in Theorem C.5 use precisely this original domain.
Article: jacobi, Theorem C.5.
-/
def edgeDomain (a:ℝ) (ha:-1<a) : Set ℂ := slitDomain (jacobi.Bessel.sigma a ha 0)

end
end jacobi.EdgeResolvent
