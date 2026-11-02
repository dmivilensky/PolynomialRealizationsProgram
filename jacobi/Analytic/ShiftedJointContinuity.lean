import jacobi.Analytic.ShiftedHolomorphy

/-!
Article: jacobi, Theorem C.5.
The original shifted profile is jointly continuous on the full physical
interval times each compact slit-domain parameter set. The same actual
series and its already proved uniform compact majorant are used.
Use: the uniform finite shifted-resolvent comparison and both shifted energy limits retain a single genuine compact parameter modulus.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Set Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology

/-- The actual original shifted continuum profile is jointly continuous
in the physical variable and every original compact shift parameter.
Use: the uniform finite shifted-resolvent comparison and both shifted
energy limits retain a single genuine compact parameter modulus.
Article: jacobi, Theorem C.5.
Proof: its actual finite spectral sums are jointly continuous, since
each original shifted coefficient is analytic on the genuine slit domain.
Their proved common uniform compact limit is the original profile. -/
theorem shiftedProfile_joint_continuous (a:ℝ) (ha:-1<a) {W:Set ℂ} (hW:IsCompact W)
    (hsub:W⊆edgeDomain a ha) :
    Continuous (fun p:Interval×W => shiftedProfile a ha p.1 p.2) := by
  -- The same source series already converges uniformly on the complete compact product.
  apply (shiftedProfile_uniform_limit a ha hW hsub).continuous
  exact Eventually.of_forall (fun N => by
    apply continuous_finsetSum
    intro k _
    have hc : Continuous (fun w:W => shiftedEdge a ha k w) := by
      apply continuous_iff_continuousAt.mpr
      intro w
      exact ((shiftedEdge_analytic a ha k (hsub w.property)).continuousAt.comp
        continuous_subtype_val.continuousAt)
    exact (hc.comp continuous_snd).mul
      (Complex.continuous_ofReal.comp ((spectralProfile a ha k).continuous.comp continuous_fst))) |>.frequently

end
end jacobi.EdgeResolvent
