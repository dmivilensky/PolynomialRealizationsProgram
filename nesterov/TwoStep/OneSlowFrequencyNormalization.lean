import nesterov.TwoStep.OneSlowFrequencyLimit
import nesterov.Slow.BandQuery

/-! Exact normalization of literal stationary singleton feasibility. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set Spectral
open scoped Topology

theorem singleProgram_symbol_iff (a : SymbolPair) {ε c γ C : ℝ}
    (hω : ε*γ∈Icc (0:ℝ) Real.pi) :
    SingleProgram ε c γ (g a (Phase.frequency (ε*γ))) (2*skew a (Phase.frequency (ε*γ))) C ↔
      Feasible a (-c*ε) (Phase.singletonSpectrum (Phase.frequency (ε*γ))) C := by
  rw [Phase.singleton_feasible_iff]
  simp only [SingleProgram,lagA,lagB,Phase.arccos_frequency hω]

theorem singleProgram_query {ε c γ C : ℝ} {U P : ℂ} (hU : U≠0)
    (h : SingleProgram ε c γ (Complex.normSq U-Complex.normSq P) (2*(P*star U).im) C) :
    SingleProgram ε c γ (Slow.queryG U P) (Slow.queryS U P) (C/Complex.normSq U) := by
  have ha := Complex.normSq_pos.mpr hU
  have hg : Complex.normSq U*Slow.queryG U P=Complex.normSq U-Complex.normSq P := by
    rw [Slow.queryG_eq _ hU]
    field_simp
  have hs : Complex.normSq U*Slow.queryS U P=2*(P*star U).im := by
    rw [Slow.queryS_eq _ hU]
    field_simp
  apply (singleProgram_scale ha).mp
  simpa only [hg,hs,mul_div_cancel₀ C ha.ne'] using h

variable {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)

/-- Any feasible literal one-atom spectrum yields a program in the actual
scaled slow coefficients, with one normalized common charge. -/
theorem actual_singleton_to_slow {ε c γ C : ℝ} (hε : 0<ε) (hε1 : ε^2≠1)
    (hy : 0<F.stepAt ε) (hω : ε*γ∈Icc (0:ℝ) Real.pi)
    (hU : (F.u ε).eval₂ Complex.ofRealHom (F.wave ε (Slow.SecondOrderFamily.slowPoint c γ))≠0)
    (h : Feasible ((F.method ε).symbolPair (ε^2) 1 (-c*ε)) (-c*ε)
      (Phase.singletonSpectrum (Phase.frequency (ε*γ))) C) :
    ∃ D : ℝ,SingleProgram ε c γ
      (F.slowG ε (Slow.SecondOrderFamily.slowPoint c γ))
      (F.slowS ε (Slow.SecondOrderFamily.slowPoint c γ)) D := by
  let a := (F.method ε).symbolPair (ε^2) 1 (-c*ε)
  let x := Phase.frequency (ε*γ)
  have hUa : a.u x≠0 := by rwa [F.sampled_query_value hω]
  have hraw := (singleProgram_symbol_iff a hω).mpr h
  change SingleProgram ε c γ (Complex.normSq (a.u x)-Complex.normSq (a.p x))
    (2*(a.p x*star (a.u x)).im) C at hraw
  have hnorm := singleProgram_query hUa hraw
  have hr : a.p x/a.u x=F.queryRatio ε (Slow.SecondOrderFamily.slowPoint c γ) :=
    F.sampled_query_ratio hω hε1 hU
  simp only [Slow.queryG,Slow.queryS,hr] at hnorm
  have hcoeff := F.query_coefficients_exact hε.ne' hε1 hy.ne' (Slow.SecondOrderFamily.slowPoint c γ)
  rw [hcoeff.1,hcoeff.2] at hnorm
  let scale := 4*ε^2/F.stepAt ε
  have hscale : 0<scale := div_pos (mul_pos (by norm_num) (sq_pos_of_pos hε)) hy
  refine ⟨(C/Complex.normSq (a.u x))/scale,?_⟩
  apply (singleProgram_scale hscale).mp
  simpa only [scale,mul_div_cancel₀ _ hscale.ne'] using hnorm

end
end nesterov.TwoStep
