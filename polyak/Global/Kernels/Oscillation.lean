import polyak.Global.Kernels.Variation

/-! Literal supremum D_n of the source, rather than a substituted error parameter. -/
noncomputable section
namespace polyak.Global.Kernels
open Set

def oscillation (ε M η:ℝ) : ℝ :=
  sSup ((fun ξ:ℝ=>|kernelHat ε ξ-kernelHat ε η|) '' Icc (η-M) (η+M))

theorem oscillation_nonempty {M:ℝ} (hM:0≤M) (ε η:ℝ) :
    ((fun ξ:ℝ=>|kernelHat ε ξ-kernelHat ε η|) '' Icc (η-M) (η+M)).Nonempty :=
  ⟨0,η,⟨by linarith,by linarith⟩,by simp⟩

theorem oscillation_bdd (ε M η:ℝ) :
    BddAbove ((fun ξ:ℝ=>|kernelHat ε ξ-kernelHat ε η|) '' Icc (η-M) (η+M)) :=
  ((isCompact_Icc.image ((continuous_kernelHat ε).sub continuous_const).abs).bddAbove)

theorem le_oscillation {ε M ξ η:ℝ} (hξη:|ξ-η|≤M) :
    |kernelHat ε ξ-kernelHat ε η|≤oscillation ε M η := by
  apply le_csSup (oscillation_bdd ε M η)
  exact ⟨ξ,⟨by linarith [(abs_le.mp hξη).1],by linarith [(abs_le.mp hξη).2]⟩,rfl⟩

theorem oscillation_nonneg {M:ℝ} (hM:0≤M) (ε η:ℝ) : 0≤oscillation ε M η := by
  have hh := le_oscillation (ε:=ε) (ξ:=η) (η:=η) (by simpa using hM)
  simpa using hh

theorem oscillation_bound {ε M:ℝ} (hε:0≤ε) (hM:0≤M) (η:ℝ) :
    oscillation ε M η≤M*min (2*mPhi*ε^2*(|η|+M)) ε := by
  apply csSup_le (oscillation_nonempty hM ε η)
  rintro _ ⟨ξ,hξ,rfl⟩
  apply kernelHat_local_variation hε hM
  exact abs_le.mpr ⟨by linarith [hξ.1],by linarith [hξ.2]⟩

end polyak.Global.Kernels
