import polyak.Boundary.ScalarPrescription
import polyak.Boundary.P1.Results
import polyak.Boundary.P2.Analytic
import polyak.Boundary.P2.Results

/-!
Article: Theorems classification and regularity, all noncentral open arcs.
Use: the independently proved actual P₁, P₂ and spiral derivatives discharge
the global scalar prescription's outer derivative obligations.
-/
noncomputable section
namespace polyak.Regularity
open Spectral Boundary Set
open Filter
open scoped Topology

theorem V_analyticAt_spiral {t : ℝ} (hl : G1<Real.cosh t) (hu : Real.cosh t<GW) :
    AnalyticAt ℝ V t := by
  have hf : AnalyticAt ℝ (fun r : ℝ => Real.arsinh (1-1/(2*Real.cosh r))) t := by
    fun_prop (disch := positivity)
  have hn : ∀ᶠ r in 𝓝 t,G1<Real.cosh r ∧ Real.cosh r<GW :=
    ((isOpen_lt continuous_const Real.continuous_cosh).inter
      (isOpen_lt Real.continuous_cosh continuous_const)).mem_nhds ⟨hl,hu⟩
  apply hf.congr
  filter_upwards [hn] with r hr
  exact (spiral_optimal hr.1.le hr.2.le).symm

theorem V_analytic_and_slope_outside_central {t : ℝ} (ha : P2.Ga<Real.cosh t)
    (h₁ : Real.cosh t≠G1) (hW : Real.cosh t≠GW) :
    AnalyticAt ℝ V t ∧ |deriv V t|<1 := by
  by_cases hG1 : Real.cosh t<G1
  · obtain ⟨z,hz,_⟩ := P2.p2_arc ⟨ha.le,hG1.le⟩
    have hzlo : P2.zeta1<z := by
      by_contra hn
      have he : z=P2.zeta1 := le_antisymm (le_of_not_gt hn) hz.1.1
      have hh : Real.cosh t=G1 := by rw [hz.2.1,he,P2.G_zeta1]
      exact h₁ hh
    have hzhi : z<P2.zetaA := by
      by_contra hn
      have he : z=P2.zetaA := le_antisymm hz.1.2 (le_of_not_gt hn)
      have hh : Real.cosh t=P2.Ga := by rw [hz.2.1,he]; rfl
      linarith
    exact ⟨P2.V_analyticAt ⟨hzlo,hzhi⟩ hz.2.1,
      P2.abs_deriv_V_lt_one ⟨hzlo,hzhi⟩ hz.2.1⟩
  by_cases hGW : Real.cosh t<GW
  · have hg : G1<Real.cosh t := lt_of_le_of_ne (le_of_not_gt hG1) h₁.symm
    exact ⟨V_analyticAt_spiral hg hGW,
      abs_deriv_V_spiral_lt_one hg hGW⟩
  · have hg : GW<Real.cosh t := lt_of_le_of_ne (le_of_not_gt hGW) hW.symm
    let z := 1/Real.cosh t
    have hz : z∈Ioo (0 : ℝ) P1.zW := by
      refine ⟨one_div_pos.mpr (Real.cosh_pos _),?_⟩
      exact one_div_lt_one_div_of_lt (by linarith [GW_bounds.1]) hg
    have he : Real.cosh t=1/z := by simp [z]
    exact ⟨P1.V_analyticAt hz he,P1.abs_deriv_V_lt_one hz he⟩

theorem V_regular_outside_central {t : ℝ} (ha : P2.Ga<Real.cosh t)
    (h₁ : Real.cosh t≠G1) (hW : Real.cosh t≠GW) :
    DifferentiableAt ℝ V t ∧ |deriv V t|<1 := by
  have hh := V_analytic_and_slope_outside_central ha h₁ hW
  exact ⟨hh.1.differentiableAt,hh.2⟩

theorem logarithmicCoordinate_strictMono_of_central
    (hcentral : ∀ t : ℝ,Real.cosh t<P2.Ga → DifferentiableAt ℝ V t ∧ |deriv V t|<1) :
    StrictMono logarithmicCoordinate := by
  apply logarithmicCoordinate_strictMono_of_derivative_bounds
  intro t ha h₁ hW
  by_cases hG : Real.cosh t<P2.Ga
  · exact hcentral t hG
  · exact V_regular_outside_central (lt_of_le_of_ne (le_of_not_gt hG) ha.symm) h₁ hW

end polyak.Regularity
