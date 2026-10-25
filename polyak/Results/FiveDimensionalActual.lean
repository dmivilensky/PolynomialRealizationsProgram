import polyak.Results.FiveDimensional
import polyak.Boundary.Classification.Results

/-! Article: the complete classified boundary gives one optimal example in
dimension five, with one objective and start fixed for all horizons. -/
namespace polyak.Results
noncomputable section
open Dynamics Spectral Waves Boundary

theorem exists_five_dimensional_optimal_example {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) :
    ∃ f : EuclideanSpace ℝ (Fin 5) → ℝ,
      CenteredSmoothStronglyConvex μ L f ∧ ∃ x₀,x₀≠0 ∧ ∃ a : ℝ,0<a ∧
        ∀ N : ℕ,a*Real.exp (N*T (polyakQ μ L))*‖x₀‖≤
          ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖ := by
  obtain ⟨w,c,hw,C,hfeas⟩:=Classification.exists_twoAtom_optimal (T (polyakQ μ L))
  exact exists_five_dimensional_optimal_example_of_two_atom hμ hL w c hw hfeas

theorem exists_worst_five_optimal_lower {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) :
    ∃ a : ℝ,0<a ∧ ∀ N : ℕ,a*Real.exp (N*T (polyakQ μ L))≤
      worst μ L (polyakAlpha μ L) (polyakBeta μ L) 5 N := by
  obtain ⟨f,hf,x₀,hx,a,ha,hbound⟩:=exists_five_dimensional_optimal_example hμ hL
  have hxpos:=norm_pos_iff.mpr hx
  have hmin : ∀ y,f 0≤f y := (hf.toSmoothStronglyConvex.minimizer_iff 0).mpr hf.gradient_zero
  refine ⟨a,ha,fun N => ?_⟩
  have hr : ‖iterate (gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖/‖x₀‖∈
      ratios μ L (polyakAlpha μ L) (polyakBeta μ L) 5 N := by
    refine ⟨f,hf.toSmoothStronglyConvex,0,x₀,hmin,hx,?_⟩
    simp
  exact ((le_div_iff₀ hxpos).mpr (hbound N)).trans
    (le_csSup (ratios_bddAbove hμ hL (polyakAlpha_pos hμ hL).le
      (polyakBeta_mem hμ hL).1 5 N) (Set.mem_insert_of_mem _ hr))

end
end polyak.Results
