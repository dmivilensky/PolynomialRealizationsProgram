import jacobi.Jacobi.CosineMehlerHeine
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Order.Compact

/-!
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
The actual squared-edge Jacobi functions converge together with their
genuine complex derivatives on every compact set. Compacts disjoint from
the genuine Bessel zero set eventually contain no finite Jacobi zero.
Source: the community Weierstrass differentiation theorem for locally
uniform holomorphic limits, applied to the proved Mehler--Heine limit.
Use: proves local uniqueness and stability of the finite zeros near each simple Bessel zero.
-/
namespace jacobi.Jacobi
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The complex derivatives of the actual squared-edge Jacobi family converge locally uniformly to the genuine Bessel derivative.
Use: proves local uniqueness and stability of the finite zeros near each simple Bessel zero.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: every finite scaled polynomial is entire. Apply the community
Weierstrass differentiation theorem to the already proved genuine locally
uniform Mehler--Heine limit on the open complex plane. -/
theorem mehler_heine_deriv_locallyUniform {a b : ℂ} (ha : -1<a.re) :
    TendstoLocallyUniformly
      (fun n : ℕ => deriv (fun z : ℂ => normalized a b n (1-z/(2*(n:ℂ)^2))))
      (deriv (jacobi.Bessel.normalized a)) atTop := by
  -- All holomorphy assumptions concern the actual finite functions.
  have heach (n : ℕ) : DifferentiableOn ℂ
      (fun z : ℂ => normalized a b n (1-z/(2*(n:ℂ)^2))) univ := by
    intro z _
    have harg : DifferentiableAt ℂ (fun w : ℂ => 1-w/(2*(n:ℂ)^2)) z := by fun_prop
    have hcomp := (normalized_analytic a b n (1-z/(2*(n:ℂ)^2))).differentiableAt.comp z harg
    exact hcomp.differentiableWithinAt
  have hlocal := tendstoLocallyUniformlyOn_univ.mpr (mehler_heine_locallyUniform (b := b) ha)
  have hD := hlocal.deriv (Eventually.of_forall heach) isOpen_univ
  simpa only [Function.comp_def] using tendstoLocallyUniformlyOn_univ.mp hD

/-- The actual scaled Jacobi complex derivatives converge uniformly on every complex compact set.
Use: supplies one derivative error bound throughout each fixed zero neighborhood.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: restrict the proved locally uniform derivative limit to a compact set, where it is uniform. -/
theorem mehler_heine_deriv_uniform {a b : ℂ} (ha : -1<a.re) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun n : ℕ => deriv (fun z : ℂ => normalized a b n (1-z/(2*(n:ℂ)^2))))
      (deriv (jacobi.Bessel.normalized a)) atTop K := by
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
  exact (tendstoLocallyUniformlyOn_univ.mpr (mehler_heine_deriv_locallyUniform ha)).mono (subset_univ K)

/-- A compact set containing no actual Bessel zero eventually contains no scaled finite Jacobi zero.
Use: excludes spurious bounded zeros when identifying the ordered edge spectrum.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: the genuine nonvanishing Bessel function has a positive minimum
norm on the compact set. Uniform Mehler--Heine approximation eventually
has smaller norm error than half that minimum, excluding every finite zero there. -/
theorem scaled_nonvanishing_compact {a b : ℂ} (ha : -1<a.re) {K : Set ℂ}
    (hK : IsCompact K) (hzero : ∀ z∈K,jacobi.Bessel.normalized a z≠0) :
    ∀ᶠ n:ℕ in atTop,∀ z∈K,normalized a b n (1-z/(2*(n:ℂ)^2))≠0 := by
  -- Compactness supplies a genuine positive margin; there is no assumed numerical tolerance.
  have hc : ContinuousOn (fun z => ‖jacobi.Bessel.normalized a z‖) K :=
    fun z _ => (jacobi.Bessel.normalized_analytic a z).continuousAt.norm.continuousWithinAt
  obtain ⟨δ,hδ,hbound⟩ := hK.exists_forall_le' hc (fun z hz => norm_pos_iff.mpr (hzero z hz))
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((tendstoLocallyUniformlyOn_univ.mpr (mehler_heine_locallyUniform (b := b) ha)).mono (subset_univ K))
  have herror := (Metric.tendstoUniformlyOn_iff.mp hu) (δ/2) (by positivity)
  filter_upwards [herror] with n hn z hz hfinite
  have h := hn z hz
  rw [hfinite,dist_zero_right] at h
  linarith [hbound z hz]

end
end jacobi.Jacobi
