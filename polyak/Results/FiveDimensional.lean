import polyak.Results.OptimalExamples
import polyak.Boundary.P2.Results
import polyak.Regularity.Critical

/-! Article: one optimal example in dimension five. The exact missing
classification input is only an actual optimal spectrum on two atoms; startup
and its strict minimizer condition are discharged here for the original method. -/
namespace polyak.Results
noncomputable section
open Dynamics Spectral Waves Realization Boundary Regularity

/-- A two-atom optimal spectrum gives one objective and one from-rest start in
ℝ⁵ which attain the exact rate at every horizon with one positive prefactor. -/
theorem exists_five_dimensional_optimal_example_of_two_atom {μ L C : ℝ}
    (hμ : 0<μ) (hL : μ<L) (w : Bool → NNReal) (c : Bool → Frequency)
    (hw : ∑ b,w b=1)
    (hfeas : Feasible (V (T (polyakQ μ L))) (T (polyakQ μ L))
      (finiteSpectrum w c hw) C) :
    ∃ f : EuclideanSpace ℝ (Fin 5) → ℝ,
      CenteredSmoothStronglyConvex μ L f ∧ ∃ x₀,x₀≠0 ∧ ∃ a : ℝ,0<a ∧
        ∀ N : ℕ,a*Real.exp (N*T (polyakQ μ L))*‖x₀‖≤
          ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖ := by
  let q:=polyakQ μ L
  have hq : 0<q:=polyakQ_pos hμ hL
  have hq1 : q<1:=polyakQ_lt_one hμ hL
  have hactual : Feasible (T q-Real.log q) (T q) (finiteSpectrum w c hw) C := by
    rw [T_sub_log_eq_V hq hq1]
    exact hfeas
  have hm := (actual_feasible_iff hq (T q) C _).mpr hactual
  have hmix : MixtureFeasible (finiteSpectrum w c hw)
      (multiplierMap (normalizedA μ L (polyakAlpha μ L) (polyakBeta μ L))
        (normalizedB μ L (polyakAlpha μ L)) (polyakBeta μ L) (T q)) C (T q) := by
    rw [polyak_normalizedA hμ hL,polyak_normalizedB hμ hL]
    exact hm
  have hstrict : 0<T q → |C|<spectrumG (finiteSpectrum w c hw)
      (multiplierMap (normalizedA μ L (polyakAlpha μ L) (polyakBeta μ L))
        (normalizedB μ L (polyakAlpha μ L)) (polyakBeta μ L) (T q)) := by
    intro ht
    rw [polyak_normalizedA hμ hL,polyak_normalizedB hμ hL]
    change |C|<spectrumG (finiteSpectrum w c hw) (multiplierMap 0 (2*q) (q^2) (T q))
    rw [multiplierMap_polyak q (T q) hq,spectrumG_polyak]
    exact actual_optimal_strict_minimizer hq hq1 ht.ne' hactual
  have hh:=exists_startup hμ hL (polyakAlpha_pos hμ hL)
    (polyakBeta_mem hμ hL).1 (polyakBeta_mem hμ hL).2
    (polyak_quadratic_condition hμ hL).2 w c hw hmix hstrict
  have hdim : 2*Fintype.card Bool+1=5 := by decide
  rw [hdim] at hh
  exact hh

/-- The full closed P₂ arc, including both switches and both exponent signs,
has an actual all-horizon optimal example in dimension five. -/
theorem exists_five_dimensional_optimal_example_p2 {μ L : ℝ}
    (hμ : 0<μ) (hL : μ<L)
    (hG : Real.cosh (T (polyakQ μ L))∈Set.Icc P2.Ga G1) :
    ∃ f : EuclideanSpace ℝ (Fin 5) → ℝ,
      CenteredSmoothStronglyConvex μ L f ∧ ∃ x₀,x₀≠0 ∧ ∃ a : ℝ,0<a ∧
        ∀ N : ℕ,a*Real.exp (N*T (polyakQ μ L))*‖x₀‖≤
          ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖ := by
  obtain ⟨z,hz,_⟩:=P2.p2_arc hG
  exact exists_five_dimensional_optimal_example_of_two_atom hμ hL
    (P2.weights z (P2.arc_mem_interval hz.1) hz.1.1)
    (P2.atoms z (P2.arc_mem_interval hz.1))
    (P2.weights_sum z (P2.arc_mem_interval hz.1) hz.1.1)
    (P2.spectrum_optimal hz.1 hz.2.1)

end
end polyak.Results
