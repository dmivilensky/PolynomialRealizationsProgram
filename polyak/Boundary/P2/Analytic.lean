import polyak.Boundary.P2.Derivative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! Article: Theorem p2arc and regularity. Actual analytic inversion of the
rational P₂ coordinate on the complete open physical arc. -/
namespace polyak.Boundary.P2
noncomputable section
open Spectral Filter
open scoped Topology

theorem G_analyticAt {z : ℝ} (hz : z∈parameterInterval) : AnalyticAt ℝ G z := by
  have h0 := (parameter_pos hz).ne'
  have hr := (rMinus_pos hz).ne'
  unfold G rMinus
  fun_prop (disch := positivity)

theorem u_analyticAt {z : ℝ} (hz : z∈parameterInterval) : AnalyticAt ℝ u z := by
  have hr := (rMinus_pos hz).ne'
  have hp := (rPlus_pos z).ne'
  have hn : z^4-4≠0 := by
    have he : z^4-4=rMinus z*rPlus z := by unfold rMinus rPlus; ring
    rw [he]
    exact mul_ne_zero hr hp
  unfold u qMinus
  fun_prop

/-- Both exponent copies of the open rational arc have the actual analytic boundary. -/
theorem V_analyticAt {z t : ℝ} (hz : z∈Set.Ioo zeta1 zetaA)
    (ht : Real.cosh t=G z) : AnalyticAt ℝ V t := by
  have hm:=arc_mem_interval ⟨hz.1.le,hz.2.le⟩
  have hg:=G_analyticAt hm
  have hn : deriv G z≠0 := by
    rw [(hasDerivAt_G hm).deriv]
    exact (GDerivative_neg hm).ne
  let inv := hg.hasStrictDerivAt.localInverse G (deriv G z) z hn
  have hi : AnalyticAt ℝ inv (G z) := hg.analyticAt_localInverse hn
  have hleft : inv (G z)=z := (hg.hasStrictDerivAt.eventually_left_inverse hn).self_of_nhds
  have hit : inv (Real.cosh t)=z := by rw [ht]; exact hleft
  have hc : AnalyticAt ℝ Real.cosh t := Real.analyticAt_cosh
  have hir : AnalyticAt ℝ (fun s => inv (Real.cosh s)) t := hi.comp_of_eq hc ht
  have hu : AnalyticAt ℝ (fun s => u (inv (Real.cosh s))) t :=
    (u_analyticAt hm).comp_of_eq hir hit
  have ha : AnalyticAt ℝ (fun s => Real.arsinh (u (inv (Real.cosh s)))) t :=
    Real.analyticAt_arsinh.comp hu
  have hnear : ∀ᶠ s in 𝓝 t,inv (Real.cosh s)∈Set.Ioo zeta1 zetaA ∧
      G (inv (Real.cosh s))=Real.cosh s := by
    have hzt : inv (Real.cosh t)∈Set.Ioo zeta1 zetaA := by rwa [hit]
    have hio := hir.continuousAt.eventually (Ioo_mem_nhds hzt.1 hzt.2)
    have hr := hg.hasStrictDerivAt.eventually_right_inverse hn
    rw [←ht] at hr
    exact hio.and (Real.continuous_cosh.continuousAt.eventually hr)
  apply ha.congr
  filter_upwards [hnear] with s hs
  exact (optimal (arc_mem_interval ⟨hs.1.1.le,hs.1.2.le⟩)
    hs.1.1.le hs.1.2.le hs.2.symm).symm

end
end polyak.Boundary.P2
