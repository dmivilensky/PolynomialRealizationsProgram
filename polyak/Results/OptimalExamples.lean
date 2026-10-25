import polyak.Spectral.Optimal
import polyak.Realization.ExplicitSpiral.CertifiedExecution

/-!
Article: Appendix C, one optimal example on all horizons.
Use: retain one objective, one start, and one positive constant, with a finite
dimension chosen before the horizon. A bound of five on that dimension is separate.
-/

namespace polyak.Results
noncomputable section
open Dynamics Spectral Waves Realization
open MeasureTheory

/-- Article: an attained finite optimal spectrum gives one actual optimal example.
No horizon-dependent function, dimension, or starting point is used. -/
theorem exists_finite_dimensional_optimal_example {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) :
    ∃ d : ℕ, 0<d ∧ ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
      CenteredSmoothStronglyConvex μ L f ∧ ∃ x₀, x₀≠0 ∧ ∃ c : ℝ,0<c ∧
        ∀ N : ℕ,c*Real.exp (N*T (polyakQ μ L))*‖x₀‖≤
          ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖ := by
  classical
  let q := polyakQ μ L
  have hq : 0<q := polyakQ_pos hμ hL
  have hq1 : q<1 := polyakQ_lt_one hμ hL
  by_cases ht : T q=0
  · obtain ⟨f,hf,x₀,_,hx,hbound⟩ := ExplicitSpiral.exists_spiral_lower hμ hL
    refine ⟨3,by norm_num,f,hf,x₀,hx,1/Real.sqrt 5,by positivity,fun N => ?_⟩
    have hcrit := (T_eq_zero_iff hq hq1).mp ht
    have hfac : Spiral.factor (polyakQ μ L)=1 := by
      change Spiral.factor q=1
      rw [hcrit,Spiral.factor_critical]
    simpa only [show T (polyakQ μ L)=0 from ht,mul_zero,Real.exp_zero,hfac,one_pow]
      using hbound N
  obtain ⟨ν,C,h⟩ := T_mem hq
  obtain ⟨F,hF,_,hcarrier⟩ := exists_actual_optimal_carrier hq hq1 ht
  let : Fintype F := hF.fintype
  obtain ⟨w,hw,he⟩ := exists_finiteSpectrum_of_support ν (hcarrier ν C h)
  have hm := (actual_feasible_iff hq (T q) C ν).mpr h
  have hstrict := actual_optimal_strict_minimizer hq hq1 ht h
  have hg : spectrumG ν (multiplierMap 0 (2*q) (q^2) (T q))=
      meanG ν (Real.sinh (T q-Real.log q)) := by
    rw [multiplierMap_polyak q (T q) hq,spectrumG_polyak]
  have hmix : MixtureFeasible (finiteSpectrum w (fun j => j.val) hw)
      (multiplierMap (normalizedA μ L (polyakAlpha μ L) (polyakBeta μ L))
        (normalizedB μ L (polyakAlpha μ L)) (polyakBeta μ L) (T q)) C (T q) := by
    rw [he,polyak_normalizedA hμ hL,polyak_normalizedB hμ hL]
    exact hm
  have hgap : |C|<spectrumG (finiteSpectrum w (fun j => j.val) hw)
      (multiplierMap (normalizedA μ L (polyakAlpha μ L) (polyakBeta μ L))
        (normalizedB μ L (polyakAlpha μ L)) (polyakBeta μ L) (T q)) := by
    rw [he,polyak_normalizedA hμ hL,polyak_normalizedB hμ hL]
    exact hg.symm ▸ hstrict
  obtain ⟨f,hf,x₀,hx,c,hc,hbound⟩ := exists_startup hμ hL (polyakAlpha_pos hμ hL)
    (polyakBeta_mem hμ hL).1 (polyakBeta_mem hμ hL).2 (polyak_quadratic_condition hμ hL).2
    w (fun j => j.val) hw hmix (fun _ => hgap)
  exact ⟨2*Fintype.card F+1,by omega,f,hf,x₀,hx,c,hc,hbound⟩

/-- Article: one positive prefactor lower-bounds the original unrestricted worst case at every horizon. -/
theorem exists_worstAll_optimal_lower {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) :
    ∃ c : ℝ,0<c ∧ ∀ N : ℕ,c*Real.exp (N*T (polyakQ μ L))≤
      worstAll μ L (polyakAlpha μ L) (polyakBeta μ L) N := by
  obtain ⟨d,hd,f,hf,x₀,hx,c,hc,hbound⟩ := exists_finite_dimensional_optimal_example hμ hL
  exact ⟨c,hc,fun N => example_le_worstAll hd f hf (polyakAlpha_pos hμ hL).le
    (polyakBeta_mem hμ hL).1 x₀ hx hbound N⟩

end
end polyak.Results
