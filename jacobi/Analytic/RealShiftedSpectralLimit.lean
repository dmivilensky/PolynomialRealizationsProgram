import jacobi.Analytic.RealFiniteSpectrum
import jacobi.Analysis.ScaledSpectralLimit

/-!
Article: jacobi, Appendix E.1.
The true transformed fibre spectrum converges along every cofinal
sequence of original dimensions. All finite small-dimension exclusions
are explicit, so near-minimizers may be selected from the original fibres.
Use: scalar-normalization continuity applies to the same finite sequence used in the shifted fibre.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter jacobi.Finite jacobi.Packing jacobi.Variational
open scoped Topology

/-- The genuine real shifted finite spectrum is summable in every original dimension.
Use: scalar-normalization continuity applies to the same finite sequence used in the shifted fibre.
Article: jacobi, Appendix E.1.
Proof: its actual original numerator vanishes outside the dimension cutoff. -/
theorem finiteRealShiftedEdge_summable (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (w:ℝ) :
    Summable (fun k => finiteRealShiftedEdge a b ha hb n k w) := by
  apply summable_of_ne_finset_zero (s:=Finset.range (n+1))
  intro k hk
  simp only [finiteRealShiftedEdge,jacobi.Jacobi.finiteLambdaAt_zero ha hb
    (by simpa only [Finset.mem_range,not_lt] using hk),zero_div]

/-- Every cofinal sequence of genuine transformed fibres has exactly the original shifted L1 edge limit.
Use: shiftedOptimalEnergy_lower transfers all four calibrations to true original near-minimizers.
Article: jacobi, Appendix E.1.
Proof: the actual finite real shifted L1 theorem and theta_N -> 1 give
the normalized L1 limit. Compose with the original cofinal selector and
identify every finite transformed spectrum by its exact source formula. -/
theorem shiftedNodes_spectral_limit {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {w:ℝ} (hw: - jacobi.Bessel.sigma a ha 0<w) (α:ℕ→ℕ) (hα:Tendsto α atTop atTop)
    (hz:∀n,0<1+w/(2*((α n:ℝ)+1)^2))
    (ht:∀n,∀k,(jacobi.Jacobi.nodes a b ha hb (α n+1)).value k<1+w/(2*((α n:ℝ)+1)^2)) :
    Tendsto (fun n => distance (fibreSpectrum (shiftedNodes
      (jacobi.Jacobi.nodes a b ha hb (α n+1)) _ (hz n) (ht n)))
        (realShiftSpectrum a ha w hw).value) atTop (𝓝 0) := by
  have h := jacobi.Analysis.scaled_spectral_limit
    (fun n => finiteRealShiftedEdge_summable a b ha hb n w)
    (realShiftedEdge_summable a ha hw) (finiteRealShiftedEdge_l1_limit ha hb hw) (shiftScale_limit w)
  simpa only [shiftedNodes_spectrum,realShiftSpectrum,Function.comp_def] using h.comp hα

end
end jacobi.EdgeResolvent
