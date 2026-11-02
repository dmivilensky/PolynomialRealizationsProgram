import krylov.Strings.SpectralBoundary
import krylov.Strings.SpectralPrimitive
import krylov.Strings.SpectralCompression

/-!
Article: `main_krylov`, `thm:value`, the Neumann string realization.
The energy space is the closed graph of the actual local primitive relation
in the physical mass and gradient Hilbert spaces. Its orthogonal projection
therefore constructs the resolvent, rather than assuming one with the
required spectral atom. The fixed space is proved to be precisely constants.
Source: the standard closed energy-form construction, using mathlib Hilbert
orthogonal projection and genuine local Bochner primitives.
-/

namespace krylov.Strings.Spectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

variable (M : Mass) [IsFiniteMeasure M.measure]

/-- Actual origin trace, lifted to the constant function in mass L². -/
def constantTrace : MassHilbert M →L[ℂ] MassHilbert M :=
  (boundaryTrace M).smulRight (constantVector M)

/-- Local primitive equation as a bounded linear constraint. -/
def energyConstraint (L : ℝ≥0) : EnergyAmbient M →L[ℂ] MassHilbert M :=
  (windowMultiplier M L ∘L (ContinuousLinearMap.id ℂ _ - constantTrace M)) ∘L
    WithLp.fstL 2 ℂ _ _ - localPrimitive M L ∘L WithLp.sndL 2 ℂ _ _

/-- The true closed graph of the string derivative. Relations on every finite
physical window avoid any assumption that an unrestricted primitive is L². -/
def energyGraph : ClosedSubmodule ℂ (EnergyAmbient M) where
  toSubmodule := ⨅ L : ℝ≥0, (energyConstraint M L).ker
  isClosed' := by
    have he : (⨅ L : ℝ≥0, (energyConstraint M L).ker).carrier =
        ⋂ L : ℝ≥0, ((energyConstraint M L).ker : Set (EnergyAmbient M)) := by
      ext w
      change w ∈ (⨅ L : ℝ≥0, (energyConstraint M L).ker) ↔ _
      simp only [Submodule.mem_iInf, mem_iInter]
      rfl
    rw [he]
    exact isClosed_iInter fun L : ℝ≥0 ↦ (energyConstraint M L).isClosed_ker

theorem mem_energyGraph (w : EnergyAmbient M) : w ∈ energyGraph M ↔
    ∀ L : ℝ≥0, windowMultiplier M L w.fst =
      windowMultiplier M L (boundaryTrace M w.fst • constantVector M) +
        localPrimitive M L w.snd := by
  simp only [energyGraph, ClosedSubmodule.mem_mk, Submodule.mem_iInf,
    LinearMap.mem_ker]
  change (∀ L : ℝ≥0, energyConstraint M L w = 0) ↔ _
  simp only [energyConstraint, ContinuousLinearMap.comp_apply,
    sub_apply, constantTrace, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, map_sub, sub_sub, sub_eq_zero]
  rfl

/-- Every genuine primitive pair lies in the constructed closed energy graph. -/
theorem energyGraph_mem_of_ae (u : MassHilbert M) (g : GradientHilbert)
    (h : u =ᵐ[M.measure] fun x ↦ boundaryTrace M u + gradientPrimitive g x) :
    WithLp.toLp 2 (u, g) ∈ energyGraph M := by
  rw [mem_energyGraph]
  intro L
  apply Lp.ext
  filter_upwards [windowMultiplier_ae M L u,
    windowMultiplier_ae M L (boundaryTrace M u • constantVector M),
    localPrimitive_ae M L g,
    Lp.coeFn_add (windowMultiplier M L (boundaryTrace M u • constantVector M))
      (localPrimitive M L g),
    Lp.coeFn_smul (boundaryTrace M u) (constantVector M),
    indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := measure_ne_top _ _) (c := (1 : ℂ)), h]
      with x hu hv hg hadd hsm hc hx
  change windowMultiplier M L u x =
    (windowMultiplier M L (boundaryTrace M u • constantVector M) + localPrimitive M L g) x
  simp only [Pi.add_apply, Pi.smul_apply] at hadd hsm
  rw [hadd, hu, hv, hg]
  by_cases hs : x ∈ Icc (0 : ℝ) L
  · simp only [indicator_of_mem hs]
    rw [hsm]
    change constantVector M x = _ at hc
    simp only [indicator_univ] at hc
    rw [hc, smul_eq_mul, mul_one, ← gradientPrimitive_eq_setIntegral g hs.1]
    exact hx
  · simp only [indicator_of_notMem hs, add_zero]

/-- All actual constant modes have zero physical gradient. -/
theorem constant_mem_energyGraph (c : ℂ) :
    firstInclusion (F := GradientHilbert) (c • constantVector M) ∈ energyGraph M := by
  rw [mem_energyGraph]
  intro L
  change windowMultiplier M L (c • constantVector M) =
    windowMultiplier M L (boundaryTrace M (c • constantVector M) • constantVector M) +
      localPrimitive M L 0
  simp only [map_smul, boundaryTrace_constant, smul_eq_mul, mul_one, map_zero, add_zero]

omit [IsFiniteMeasure M.measure] in
/-- Negative positions carry no actual string mass. -/
theorem ae_nonnegative : ∀ᵐ x ∂M.measure, 0 ≤ x := by
  rw [ae_iff]
  have h : M.measure (Iio 0) = 0 := by
    rw [Mass.measure, M.cumulative.measure_Iio (cumulative_tendsto_atBot_zero M),
      M.leftLim_origin, sub_self, ENNReal.ofReal_zero]
  simpa only [Iio, not_le] using h

omit [IsFiniteMeasure M.measure] in
/-- The local physical windows determine a mass L² function uniquely. -/
theorem eq_of_all_windows (u v : MassHilbert M)
    (h : ∀ L : ℝ≥0, windowMultiplier M L u = windowMultiplier M L v) : u = v := by
  apply Lp.ext
  have ha : ∀ n : ℕ, ∀ᵐ x ∂M.measure, x ∈ Icc (0 : ℝ) n → u x = v x := by
    intro n
    filter_upwards [windowMultiplier_ae M (n : ℝ≥0) u,
      windowMultiplier_ae M (n : ℝ≥0) v] with x hu hv hx
    rw [h (n : ℝ≥0)] at hu
    rw [hu] at hv
    have hx' : x ∈ Icc (0 : ℝ) (↑(n : ℝ≥0) : ℝ) := by exact_mod_cast hx
    simpa only [indicator_of_mem hx'] using hv
  filter_upwards [ae_all_iff.2 ha, ae_nonnegative M] with x hx hx0
  obtain ⟨n, hn⟩ := exists_nat_ge x
  exact hx n ⟨hx0, hn⟩

/-- No extra zero-gradient modes are hidden in the closed graph. -/
theorem zero_gradient_mem_iff (u : MassHilbert M) :
    firstInclusion (F := GradientHilbert) u ∈ energyGraph M ↔
      u ∈ ℂ ∙ constantVector M := by
  constructor
  · intro hu
    rw [mem_energyGraph] at hu
    have h : u = boundaryTrace M u • constantVector M := by
      apply eq_of_all_windows M
      intro L
      simpa only [firstInclusion_apply, WithLp.fst, WithLp.snd, WithLp.ofLp_toLp,
        map_zero, add_zero] using hu L
    exact Submodule.mem_span_singleton.2 ⟨boundaryTrace M u, h.symm⟩
  · intro hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    exact constant_mem_energyGraph M c

/-- The actual bounded Neumann resolvent from the string energy graph. -/
def neumannResolvent : MassHilbert M →L[ℂ] MassHilbert M :=
  compressedProjection (energyGraph M).toSubmodule

/-- The actual mass-and-gradient solution of the energy variational problem. -/
def neumannEnergySolution : MassHilbert M →L[ℂ] EnergyAmbient M :=
  compressedSolution (energyGraph M).toSubmodule

theorem neumannEnergySolution_mem (f : MassHilbert M) :
    neumannEnergySolution M f ∈ energyGraph M :=
  (energyGraph M).toSubmodule.starProjection_apply_mem _

/-- The constructed operator is the true unit-parameter Neumann resolvent:
its solution obeys the actual weak mass-plus-gradient equation against every
finite-energy physical string function. -/
theorem neumannEnergySolution_variational (f : MassHilbert M) {w : EnergyAmbient M}
    (hw : w ∈ energyGraph M) :
    inner ℂ (neumannResolvent M f) w.fst +
      inner ℂ (neumannEnergySolution M f).snd w.snd = inner ℂ f w.fst := by
  change inner ℂ (compressedSolution (energyGraph M).toSubmodule f).fst w.fst +
    inner ℂ (compressedSolution (energyGraph M).toSubmodule f).snd w.snd = inner ℂ f w.fst
  have h := compressedSolution_variational (energyGraph M).toSubmodule f hw
  simpa only [WithLp.prod_inner_apply, firstInclusion_apply, WithLp.ofLp_toLp,
    WithLp.ofLp_fst, WithLp.ofLp_snd, inner_zero_left, add_zero] using h

/-- The actual weak Neumann energy problem has a unique solution. Thus the
spectral realization is fixed by the physical primitive and energy equation. -/
theorem neumannEnergySolution_unique (f : MassHilbert M) {u : EnergyAmbient M}
    (hu : u ∈ energyGraph M)
    (hweak : ∀ w ∈ energyGraph M,
      inner ℂ u.fst w.fst + inner ℂ u.snd w.snd = inner ℂ f w.fst) :
    u = neumannEnergySolution M f := by
  symm
  change (energyGraph M).toSubmodule.starProjection (firstInclusion f) = u
  apply (energyGraph M).toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero hu
  intro w hw
  rw [inner_sub_left, WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change inner ℂ f w.fst + inner ℂ (0 : GradientHilbert) w.snd -
    (inner ℂ u.fst w.fst + inner ℂ u.snd w.snd) = 0
  rw [inner_zero_left, add_zero, hweak w hw, sub_self]

theorem neumannResolvent_selfAdjoint : IsSelfAdjoint (neumannResolvent M) :=
  compressedProjection_selfAdjoint _

theorem neumannResolvent_norm_le : ‖neumannResolvent M‖ ≤ 1 :=
  compressedProjection_norm_le _

theorem neumannResolvent_complement_norm_le : ‖1 - neumannResolvent M‖ ≤ 1 :=
  compressedProjection_complement_norm_le _

/-- The fixed space of the constructed resolvent is exactly the actual
one-dimensional constant eigenspace. -/
theorem neumannResolvent_fixed_space : (neumannResolvent M).eqLocus 1 =
    ℂ ∙ constantVector M := by
  ext u
  change neumannResolvent M u = u ↔ _
  rw [neumannResolvent, compressedProjection_fixed_iff]
  exact zero_gradient_mem_iff M u

end
end krylov.Strings.Spectral
