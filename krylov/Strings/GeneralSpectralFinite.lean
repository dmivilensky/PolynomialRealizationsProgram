import krylov.Strings.GeneralSpectralMeasure
import krylov.Strings.SpectralPrincipal

/-!
Article: main_krylov, thm:value and apC:prop:tauber.
Use: the arbitrary-mass physical realization extends exactly the original
finite-mass principal measure. In particular the tail theorem applies to
the same optimizer measure whose zero atom was computed in stage 9.
Source: equality of the literal local primitive constraints, followed by
the actual Hilbert projection and scalar spectral-measure constructions.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped NNReal
variable (M : Mass) [IsFiniteMeasure M.measure]

local instance : IsFiniteMeasure (StringMeasure.ofMass M).measure :=
  inferInstanceAs (IsFiniteMeasure M.measure)

omit [IsFiniteMeasure M.measure] in
theorem boundaryVector_ofMass : boundaryVector (StringMeasure.ofMass M) = Spectral.boundaryVector M := rfl

omit [IsFiniteMeasure M.measure] in
theorem boundaryTrace_ofMass : boundaryTrace (StringMeasure.ofMass M) = Spectral.boundaryTrace M := rfl

omit [IsFiniteMeasure M.measure] in
/-- The local restriction is the same physical indicator in both energy
constructions. -/
theorem windowMultiplier_ofMass (L : Window M.measure) :
    windowMultiplier M.measure L = Spectral.windowMultiplier M L.val := by
  ext u
  exact (windowMultiplier_ae M.measure L u).trans
    (Spectral.windowMultiplier_ae M L.val u).symm

/-- The finite construction's restricted constant is the general local
constant, with the same unit physical representative. -/
theorem windowConstant_ofMass (L : Window M.measure) :
    windowConstant M.measure L = Spectral.windowMultiplier M L.val (Spectral.constantVector M) := by
  apply Lp.ext
  filter_upwards [windowConstant_ae M.measure L,
    Spectral.windowMultiplier_ae M L.val (Spectral.constantVector M),
    indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := measure_ne_top _ _) (c := (1 : ℂ))] with x hc hw hv
  change Spectral.constantVector M x = _ at hv
  simp only [indicator_univ] at hv
  rw [hc, hw]
  by_cases hx : x ∈ Icc (0 : ℝ) L.val
  · simp only [indicator_of_mem hx, hv]
  · simp only [indicator_of_notMem hx]

/-- Both primitives are the same actual Lebesgue integral of the same
physical L² gradient. -/
theorem localPrimitive_ofMass (L : Window M.measure) :
    localPrimitive M.measure L = Spectral.localPrimitive M L.val := by
  ext g
  filter_upwards [localPrimitive_ae M.measure L g, Spectral.localPrimitive_ae M L.val g] with x hg hs
  rw [hg, hs]
  by_cases hx : x ∈ Icc (0 : ℝ) L.val
  · simp only [indicator_of_mem hx, Spectral.gradientPrimitive_eq_setIntegral g hx.1]
  · simp only [indicator_of_notMem hx]

/-- The general physical closed graph is literally the original finite
mass graph; no uniqueness certificate is assumed. -/
theorem energyGraph_ofMass : energyGraph (StringMeasure.ofMass M) = Spectral.energyGraph M := by
  ext w
  change w ∈ energyGraph (StringMeasure.ofMass M) ↔ w ∈ Spectral.energyGraph M
  rw [mem_energyGraph, Spectral.mem_energyGraph]
  change (∀ L : Window M.measure, windowMultiplier M.measure L w.fst =
      Spectral.boundaryTrace M w.fst • windowConstant M.measure L + localPrimitive M.measure L w.snd) ↔ _
  constructor
  · intro hw L
    have he := hw ⟨L, measure_ne_top _ _⟩
    simpa only [windowMultiplier_ofMass, localPrimitive_ofMass,
      windowConstant_ofMass, map_smul] using he
  · intro hw L
    have he := hw L.val
    simpa only [windowMultiplier_ofMass, localPrimitive_ofMass,
      windowConstant_ofMass, map_smul] using he

/-- Therefore the actual projected resolvent is the same operator. -/
theorem neumannResolvent_ofMass : neumannResolvent (StringMeasure.ofMass M) = Spectral.neumannResolvent M := by
  have he : ∀ K L : ClosedSubmodule ℂ (Spectral.EnergyAmbient M), K = L →
      Spectral.compressedProjection K.toSubmodule = Spectral.compressedProjection L.toSubmodule := by
    intro K L h
    cases h
    rfl
  exact he _ _ (energyGraph_ofMass M)

/-- Equality of the actual principal measures, including every atom and
the entire tail, rather than merely an equality of a selected moment. -/
theorem principalMeasure_ofMass : principalMeasure (StringMeasure.ofMass M) = Spectral.principalMeasure M := by
  have he : ∀ (T U : Spectral.MassHilbert M →L[ℂ] Spectral.MassHilbert M)
      (hT : IsSelfAdjoint T) (hU : IsSelfAdjoint U) (v : Spectral.MassHilbert M), T = U →
      (Spectral.scalarMeasure T hT v).map (fun u : spectrum ℝ T ↦ (u : ℝ)⁻¹ - 1) =
        (Spectral.scalarMeasure U hU v).map (fun u : spectrum ℝ U ↦ (u : ℝ)⁻¹ - 1) := by
    intro T U hT hU v h
    cases h
    rfl
  exact he _ _ _ _ _ (neumannResolvent_ofMass M)

end
end krylov.Strings.GeneralSpectral
