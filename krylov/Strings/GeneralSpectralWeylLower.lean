import krylov.Strings.GeneralSpectralWeylTrace
import krylov.Strings.GeneralSpectralMeasure

/-!
Article: main_krylov, apC:prop:tauber, lower local energy comparison.
Use: apply the sharp local Sobolev trace bound to the actual closed physical
energy graph.  The mass may have infinite total mass or a singular finite
endpoint; only one initial finite prefix is used.
Source: the true local primitive equations, mass domination and L² norms.
-/

namespace krylov.Strings.GeneralSpectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

/-- The squared physical L² norm is the actual integral of the squared
norm of its representative, for arbitrary underlying measures. -/
theorem integral_norm_sq_eq {μ : Measure ℝ} (u : Lp ℂ 2 μ) :
    (∫ x, ‖u x‖ ^ 2 ∂μ) = ‖u‖ ^ 2 := by
  calc
    (∫ x, ‖u x‖ ^ 2 ∂μ) = ∫ x, (inner ℂ (u x) (u x)).re ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ (inner_self_eq_norm_sq (𝕜 := ℂ) (u x)).symm
    _ = (∫ x, inner ℂ (u x) (u x) ∂μ).re := by
      simpa only [RCLike.re_to_complex] using integral_re (L2.integrable_inner (𝕜 := ℂ) u u)
    _ = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u

/-- The true continuous local representative of a physical energy pair. -/
def energyRepresentative (S : StringMeasure) (w : EnergyAmbient S.measure) (x : ℝ) : ℂ :=
  boundaryTrace S w.fst + Spectral.gradientPrimitive w.snd x

/-- The local representative is continuous before any density regularity
is imposed on the physical mass. -/
theorem energyRepresentative_continuous (S : StringMeasure) (w : EnergyAmbient S.measure) :
    Continuous (energyRepresentative S w) :=
  continuous_const.add (Spectral.gradientPrimitive_continuous w.snd)

/-- The defining local energy constraints give actual almost-everywhere
agreement with the continuous primitive on every finite prefix. -/
theorem energyGraph_local_ae (S : StringMeasure) {w : EnergyAmbient S.measure}
    (hw : w ∈ energyGraph S) (L : Window S.measure) :
    w.fst =ᵐ[S.measure.restrict (Icc (0 : ℝ) L.val)] energyRepresentative S w := by
  have he := (mem_energyGraph S w).mp hw L
  filter_upwards [ae_restrict_of_ae (windowMultiplier_ae S.measure L w.fst),
    ae_restrict_of_ae (windowConstant_ae S.measure L),
    ae_restrict_of_ae (localPrimitive_ae S.measure L w.snd),
    ae_restrict_of_ae (Lp.coeFn_add (boundaryTrace S w.fst • windowConstant S.measure L)
      (localPrimitive S.measure L w.snd)),
    ae_restrict_of_ae (Lp.coeFn_smul (boundaryTrace S w.fst) (windowConstant S.measure L)),
    ae_restrict_mem measurableSet_Icc] with x hu hc hg ha hs hx
  have hh := congrArg (fun z : MassHilbert S.measure ↦ z x) he
  simp only [Pi.add_apply, Pi.smul_apply] at ha hs
  rw [ha, hu, hs, hc, hg, indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx,
    smul_eq_mul, mul_one] at hh
  exact hh

/-- Restricting a physical L² gradient to a positive compact interval
gives the usual Lebesgue integrability, with no change of representative. -/
theorem gradient_intervalIntegrable_volume (g : GradientHilbert) {δ : ℝ} (hδ : 0 ≤ δ) :
    IntervalIntegrable (fun x ↦ g x) volume 0 δ := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδ]
  have hi := (Spectral.gradient_intervalIntegrable g 0 δ).1
  change Integrable (fun x ↦ g x) ((volume.restrict (Ioi (0 : ℝ))).restrict (Ioc 0 δ)) at hi
  change Integrable (fun x ↦ g x) (volume.restrict (Ioc 0 δ))
  simpa only [Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr Ioc_subset_Ioi_self] using hi

/-- On the physical half-line the gradient primitive is the ordinary
Lebesgue primitive; the positive-half-line restriction removes no point. -/
theorem gradientPrimitive_eq_volume (g : GradientHilbert) {x : ℝ} (hx : 0 ≤ x) :
    Spectral.gradientPrimitive g x = ∫ y in (0 : ℝ)..x, g y := by
  rw [Spectral.gradientPrimitive, intervalIntegral.integral_of_le hx,
    intervalIntegral.integral_of_le hx, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr Ioc_subset_Ioi_self]

/-- The gradient square is locally Lebesgue integrable. -/
theorem gradient_sq_intervalIntegrable (g : GradientHilbert) {δ : ℝ} (hδ : 0 ≤ δ) :
    IntervalIntegrable (fun x ↦ ‖g x‖ ^ 2) volume 0 δ := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδ]
  have hi := ((Lp.memLp g).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integrableOn
    (s := Ioc (0 : ℝ) δ)
  change Integrable (fun x ↦ ‖g x‖ ^ 2) ((volume.restrict (Ioi (0 : ℝ))).restrict (Ioc 0 δ)) at hi
  change Integrable (fun x ↦ ‖g x‖ ^ 2) (volume.restrict (Ioc 0 δ))
  simpa only [Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr Ioc_subset_Ioi_self] using hi

/-- The local gradient energy is bounded by the actual global gradient
norm, including when the physical mass has infinite total mass. -/
theorem gradient_local_energy_le (g : GradientHilbert) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ x in (0 : ℝ)..δ, ‖g x‖ ^ 2) ≤ ‖g‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le hδ]
  have he : (volume.restrict (Ioi (0 : ℝ))).restrict (Ioc (0 : ℝ) δ) =
      volume.restrict (Ioc (0 : ℝ) δ) := by
    rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self]
  rw [← he]
  exact (integral_mono_measure Measure.restrict_le_self
    (Eventually.of_forall fun x ↦ sq_nonneg ‖g x‖)
    ((Lp.memLp g).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))).trans_eq
      (integral_norm_sq_eq g)

/-- The unit origin atom and the positive compact prefix have disjoint
mass energy, both dominated by the full physical mass norm. -/
theorem mass_local_energy_le (S : StringMeasure) (u : MassHilbert S.measure) (δ : ℝ) :
    ‖boundaryTrace S u‖ ^ 2 + (∫ x in Ioc 0 δ, ‖u x‖ ^ 2 ∂S.measure) ≤ ‖u‖ ^ 2 := by
  have hi := (Lp.memLp u).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hd : Disjoint ({0} : Set ℝ) (Ioc 0 δ) := by simp
  have hmeasure : S.measure.restrict {0} + S.measure.restrict (Ioc 0 δ) ≤ S.measure := by
    rw [← Measure.restrict_union hd measurableSet_Ioc]
    exact Measure.restrict_le_self
  have hh := integral_mono_measure hmeasure (Eventually.of_forall fun x ↦ sq_nonneg ‖u x‖) hi
  rw [integral_add_measure hi.integrableOn hi.integrableOn, integral_singleton,
    Measure.real, S.origin, ENNReal.toReal_one, one_smul, integral_norm_sq_eq] at hh
  rw [boundaryTrace_apply]
  exact hh

/-- A positive lower density on one finite prefix gives the actual local
mass estimate for every energy pair.  It allows arbitrary mass elsewhere. -/
theorem energyGraph_local_mass_lower (S : StringMeasure) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hf : S.measure (Icc 0 δ) ≠ ⊤)
    (hlower : ENNReal.ofReal ρ • volume.restrict (Ioc 0 δ) ≤ S.measure.restrict (Ioc 0 δ))
    {w : EnergyAmbient S.measure} (hw : w ∈ energyGraph S) :
    ‖boundaryTrace S w.fst‖ ^ 2 +
      ρ * (∫ x in (0 : ℝ)..δ, ‖energyRepresentative S w x‖ ^ 2) ≤ ‖w.fst‖ ^ 2 := by
  let L : Window S.measure := ⟨⟨δ, hδ.le⟩, hf⟩
  have hrepμ : w.fst =ᵐ[S.measure.restrict (Ioc 0 δ)] energyRepresentative S w :=
    (energyGraph_local_ae S hw L).filter_mono
      (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
  have hrep : w.fst =ᵐ[volume.restrict (Ioc 0 δ)] energyRepresentative S w :=
    (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr hρ)).mp (ae_mono hlower hrepμ)
  have hi := (Lp.memLp w.fst).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hh := integral_mono_measure hlower
    (Eventually.of_forall fun x ↦ sq_nonneg ‖w.fst x‖) hi.integrableOn
  rw [integral_smul_measure, ENNReal.toReal_ofReal hρ.le, smul_eq_mul] at hh
  have he : (∫ x in Ioc 0 δ, ‖w.fst x‖ ^ 2) =
      ∫ x in Ioc 0 δ, ‖energyRepresentative S w x‖ ^ 2 :=
    integral_congr_ae (hrep.mono fun x hx ↦ by dsimp only; rw [hx])
  rw [he] at hh
  rw [intervalIntegral.integral_of_le hδ.le]
  linarith [mass_local_energy_le S w.fst δ]

/-- The actual closed physical graph satisfies the high-energy trace
bound whenever k²+k/delta is below the available local mass coefficient. -/
theorem energyGraph_trace_lower (S : StringMeasure) {δ ρ t k : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (ht : 0 ≤ t) (hk : 0 ≤ k)
    (hf : S.measure (Icc 0 δ) ≠ ⊤)
    (hlower : ENNReal.ofReal ρ • volume.restrict (Ioc 0 δ) ≤ S.measure.restrict (Ioc 0 δ))
    (hkbound : k ^ 2 + k / δ ≤ t * ρ)
    {w : EnergyAmbient S.measure} (hw : w ∈ energyGraph S) :
    (t + k) * ‖boundaryTrace S w.fst‖ ^ 2 ≤ t * ‖w.fst‖ ^ 2 + ‖w.snd‖ ^ 2 := by
  have htr := trace_primitive_energy_lower (boundaryTrace S w.fst) hδ hk
    (gradient_intervalIntegrable_volume w.snd hδ.le) (gradient_sq_intervalIntegrable w.snd hδ.le)
  have hrep : (∫ x in (0 : ℝ)..δ, ‖w.snd x‖ ^ 2 +
      (k ^ 2 + k / δ) * ‖boundaryTrace S w.fst + ∫ y in (0 : ℝ)..x, w.snd y‖ ^ 2) =
      ∫ x in (0 : ℝ)..δ, ‖w.snd x‖ ^ 2 + (k ^ 2 + k / δ) * ‖energyRepresentative S w x‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0 ≤ x := by rw [uIcc_of_le hδ.le] at hx; exact hx.1
    dsimp only [energyRepresentative]
    rw [gradientPrimitive_eq_volume w.snd hx0]
  rw [hrep] at htr
  have hi : IntervalIntegrable (fun x ↦ ‖energyRepresentative S w x‖ ^ 2) volume 0 δ :=
    (energyRepresentative_continuous S w).norm.pow 2 |>.intervalIntegrable 0 δ
  rw [intervalIntegral.integral_add (gradient_sq_intervalIntegrable w.snd hδ.le) (hi.const_mul _),
    intervalIntegral.integral_const_mul] at htr
  have hn : 0 ≤ ∫ x in (0 : ℝ)..δ, ‖energyRepresentative S w x‖ ^ 2 :=
    intervalIntegral.integral_nonneg hδ.le (fun x _ ↦ sq_nonneg _)
  have hm := energyGraph_local_mass_lower S hδ hρ hf hlower hw
  have hg := gradient_local_energy_le w.snd hδ.le
  have hcoeff := mul_le_mul_of_nonneg_right hkbound hn
  nlinarith [mul_le_mul_of_nonneg_left hm ht]

end
end krylov.Strings.GeneralSpectral
