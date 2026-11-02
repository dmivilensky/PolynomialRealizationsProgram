import krylov.Strings.GeneralSpectralPrimitive
import krylov.Strings.SpectralCompression
import krylov.Strings.SpectralScalar

/-!
Article: main_krylov, apC:prop:tauber, actual Neumann energy realization.
Use: construct the closed physical derivative relation and its resolvent
without assuming finite total mass. Local constraints use only prefixes
whose actual mass is finite, so a singular finite right endpoint is allowed.
Source: the standard closed energy-form construction via Hilbert projection;
all primitives and traces below are actual physical operators.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
open Set MeasureTheory
open scoped Topology ContinuousFunctionalCalculus

/-- Actual mass data with the source's distinguished unit left atom.
No spectral or regularity conclusion is stored in these data. -/
structure StringMeasure where
  /-- The genuine physical mass measure. -/
  measure : Measure ℝ
  /-- The source unit origin atom. -/
  origin : measure {0} = 1

/-- Every original global Stieltjes mass supplies these actual mass data. -/
def StringMeasure.ofMass (M : Mass) : StringMeasure := ⟨M.measure, M.measure_origin⟩

variable (S : StringMeasure)

/-- The actual L² vector of the distinguished unit atom. -/
def boundaryVector : MassHilbert S.measure :=
  indicatorConstLp 2 (measurableSet_singleton 0) (by rw [S.origin]; exact ENNReal.one_ne_top) (1 : ℂ)

/-- The physical unit-atom vector has norm one. -/
theorem boundaryVector_norm : ‖boundaryVector S‖ = 1 := by
  simp [boundaryVector, norm_indicatorConstLp (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤), Measure.real, S.origin]

instance massHilbert_nontrivial : Nontrivial (MassHilbert S.measure) :=
  nontrivial_of_ne (boundaryVector S) 0 (by
    intro h
    have hn := boundaryVector_norm S
    rw [h, norm_zero] at hn
    exact zero_ne_one hn)

/-- The genuine bounded physical trace at the unit origin atom. -/
def boundaryTrace : MassHilbert S.measure →L[ℂ] ℂ := innerSL ℂ (boundaryVector S)

/-- The Hilbert trace is the actual origin value of every representative. -/
theorem boundaryTrace_apply (u : MassHilbert S.measure) : boundaryTrace S u = u 0 := by
  rw [boundaryTrace, innerSL_apply_apply, boundaryVector, L2.inner_indicatorConstLp_one,
    integral_singleton]
  simp [Measure.real, S.origin]

/-- The true bounded local constraint expressing the derivative primitive. -/
def energyConstraint (L : Window S.measure) : EnergyAmbient S.measure →L[ℂ] MassHilbert S.measure :=
  windowMultiplier S.measure L ∘L WithLp.fstL 2 ℂ _ _ -
    ((boundaryTrace S).comp (WithLp.fstL 2 ℂ _ _)).smulRight (windowConstant S.measure L) -
      localPrimitive S.measure L ∘L WithLp.sndL 2 ℂ _ _

/-- The actual closed physical energy graph, defined by all finite-prefix
primitive equations. It permits infinite global mass. -/
def energyGraph : ClosedSubmodule ℂ (EnergyAmbient S.measure) where
  toSubmodule := ⨅ L : Window S.measure, (energyConstraint S L).ker
  isClosed' := by
    have he : (⨅ L : Window S.measure, (energyConstraint S L).ker).carrier =
        ⋂ L : Window S.measure, ((energyConstraint S L).ker : Set (EnergyAmbient S.measure)) := by
      ext w
      change w ∈ (⨅ L : Window S.measure, (energyConstraint S L).ker) ↔ _
      simp only [Submodule.mem_iInf, mem_iInter]
      rfl
    rw [he]
    exact isClosed_iInter fun L ↦ (energyConstraint S L).isClosed_ker

/-- Membership means the literal actual local primitive equations. -/
theorem mem_energyGraph (w : EnergyAmbient S.measure) : w ∈ energyGraph S ↔
    ∀ L : Window S.measure, windowMultiplier S.measure L w.fst =
      boundaryTrace S w.fst • windowConstant S.measure L + localPrimitive S.measure L w.snd := by
  simp only [energyGraph, ClosedSubmodule.mem_mk, Submodule.mem_iInf, LinearMap.mem_ker]
  change (∀ L : Window S.measure, energyConstraint S L w = 0) ↔ _
  simp only [energyConstraint, ContinuousLinearMap.comp_apply, sub_apply,
    sub_sub, sub_eq_zero]
  rfl

/-- Every actual physical primitive pair satisfies the constructed local
constraints, even when the total mass is infinite. -/
theorem energyGraph_mem_of_ae (u : MassHilbert S.measure) (g : GradientHilbert)
    (h : u =ᵐ[S.measure] fun x ↦ boundaryTrace S u + Spectral.gradientPrimitive g x) :
    WithLp.toLp 2 (u, g) ∈ energyGraph S := by
  rw [mem_energyGraph]
  intro L
  apply Lp.ext
  filter_upwards [windowMultiplier_ae S.measure L u, windowConstant_ae S.measure L,
    localPrimitive_ae S.measure L g,
    Lp.coeFn_add (boundaryTrace S u • windowConstant S.measure L) (localPrimitive S.measure L g),
    Lp.coeFn_smul (boundaryTrace S u) (windowConstant S.measure L), h]
      with x hu hc hg hadd hsm hx
  change windowMultiplier S.measure L u x =
    (boundaryTrace S u • windowConstant S.measure L + localPrimitive S.measure L g) x
  simp only [Pi.add_apply, Pi.smul_apply] at hadd hsm
  rw [hadd, hu, hsm, hc, hg]
  by_cases hs : x ∈ Icc (0 : ℝ) L.val
  · simpa only [indicator_of_mem hs, smul_eq_mul, mul_one] using hx
  · simp only [indicator_of_notMem hs, smul_zero, add_zero]

/-- The actual unit-parameter Neumann energy resolvent. -/
def neumannResolvent : MassHilbert S.measure →L[ℂ] MassHilbert S.measure :=
  Spectral.compressedProjection (energyGraph S).toSubmodule

/-- The genuine mass-and-gradient weak solution operator. -/
def neumannEnergySolution : MassHilbert S.measure →L[ℂ] EnergyAmbient S.measure :=
  Spectral.compressedSolution (energyGraph S).toSubmodule

/-- The actual solution lies in the actual physical energy graph. -/
theorem neumannEnergySolution_mem (f : MassHilbert S.measure) :
    neumannEnergySolution S f ∈ energyGraph S :=
  (energyGraph S).toSubmodule.starProjection_apply_mem _

/-- The actual weak mass-plus-gradient Neumann equation. -/
theorem neumannEnergySolution_variational (f : MassHilbert S.measure) {w : EnergyAmbient S.measure}
    (hw : w ∈ energyGraph S) :
    inner ℂ (neumannResolvent S f) w.fst +
      inner ℂ (neumannEnergySolution S f).snd w.snd = inner ℂ f w.fst := by
  change inner ℂ (Spectral.compressedSolution (energyGraph S).toSubmodule f).fst w.fst +
    inner ℂ (Spectral.compressedSolution (energyGraph S).toSubmodule f).snd w.snd = inner ℂ f w.fst
  have h := Spectral.compressedSolution_variational (energyGraph S).toSubmodule f hw
  simpa only [WithLp.prod_inner_apply, Spectral.firstInclusion_apply, WithLp.ofLp_toLp,
    WithLp.ofLp_fst, WithLp.ofLp_snd, inner_zero_left, add_zero] using h

/-- The actual energy resolvent is self-adjoint. -/
theorem neumannResolvent_selfAdjoint : IsSelfAdjoint (neumannResolvent S) :=
  Spectral.compressedProjection_selfAdjoint _

/-- The actual energy resolvent is a contraction. -/
theorem neumannResolvent_norm_le : ‖neumannResolvent S‖ ≤ 1 :=
  Spectral.compressedProjection_norm_le _

/-- The complement of the actual energy resolvent is a contraction. -/
theorem neumannResolvent_complement_norm_le : ‖1 - neumannResolvent S‖ ≤ 1 :=
  Spectral.compressedProjection_complement_norm_le _

end
end krylov.Strings.GeneralSpectral
