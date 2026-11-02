import jacobi.Rearrangement.RegularDistribution
import jacobi.Rearrangement.RegularSpectral

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
The complete rearrangement conclusion is proved here for compactly supported
Lipschitz densities: an actual symmetric decreasing equimeasurable density
preserves all three normalizations and increases every cyclic moment, the
largest eigenvalue and every extended Fredholm functional. The construction
uses only proved compactness, strict radial maximization and actual integral
identities. Approximation of general finite-energy densities is a separate step.
Source: the polarization proof of the Riesz and Brascamp–Lieb–Luttinger inequalities.
Use: the regular case of the article's rearrangement lemma, before finite-energy approximation.
-/
namespace jacobi.Rearrangement
noncomputable section
open Set Real MeasureTheory jacobi.Variational
open scoped NNReal Topology BoundedContinuousFunction BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A regular density has an actual equimeasurable symmetric decreasing replacement
preserving mass, energy and root mass and increasing all actual spectral observations.
Use: the regular case of the article's rearrangement lemma, before finite-energy approximation.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: choose the proved radial orbit limit. Closedness preserves its regular
bounds; the proved orbit invariants give its full distribution and three integrals,
and the integrated graph comparisons give all spectral inequalities simultaneously. -/
theorem regular_rearrangement {f : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hR : 0 ≤ R) (hf : f ∈ regularFamily R C K) :
    ∃ (g : ℝ →ᵇ ℝ) (hgr : g ∈ regularFamily R C K),
      SymmetricDecreasing g ∧
      (∀ t, volume {x | t < g x}=volume {x | t < f x}) ∧
      (regularDensity g hgr).mass=(regularDensity f hf).mass ∧
      (regularDensity g hgr).energy=(regularDensity f hf).energy ∧
      (regularDensity g hgr).rootMass=(regularDensity f hf).rootMass ∧
      (∀ n : ℕ, (∑' j, (regularDensity f hf).spectrum j^(n+1)) ≤
        ∑' j, (regularDensity g hgr).spectrum j^(n+1)) ∧
      observe (regularDensity f hf) .top ≤ observe (regularDensity g hgr) .top ∧
      (∀ s : ℝ, 0 ≤ s → (regularDensity f hf).fredholm s ≤ (regularDensity g hgr).fredholm s) ∧
      (∀ F : ℝ → ℝ, Continuous F → F 0=0 → (∫ x, F (g x))=∫ x, F (f x)) := by
  -- One actual limit works for every test function, cyclic order and Fredholm parameter.
  obtain ⟨g,hg,hs⟩ := regularOrbit_radial hR hf
  have hgr : g ∈ regularFamily R C K := closure_minimal
    (fun _ hq => hq.regular hf) (regularFamily_closed R C K) hg
  obtain ⟨hM,hE,hr⟩ := regularOrbit_integrals hf hg hgr
  exact ⟨g,hgr,hs,regularOrbit_superlevel hf hg hgr,hM,hE,hr,
    regularOrbit_moment_le hf hg hgr,regularOrbit_top_le hf hg hgr,
    (fun _ hs => regularOrbit_fredholm_le hf hg hgr hs),
    fun _ hF h0 => regularOrbit_integral_comp hf hg hF h0⟩

end
end jacobi.Rearrangement
