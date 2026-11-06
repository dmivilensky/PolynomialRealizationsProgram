import nesterov.Spectral.Realization
import Mathlib.MeasureTheory.Function.Holder

/-! Multiplication by the unit phase is an actual orthogonal equivalence of
L²(ν;ℂ), not merely a norm identity on the realized trajectory. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace nesterov.Spectral

def phaseMap (θ : ℝ) : C(Frequency,ℂ) :=
  ⟨fun c => polyak.Waves.z 0 (θ*Real.arccos c), by unfold polyak.Waves.z; fun_prop⟩

def phaseLp (ν : Spectrum) (θ : ℝ) : Lp ℂ ∞ (ν : Measure Frequency) :=
  ContinuousMap.toLp ∞ (ν : Measure Frequency) ℝ (phaseMap θ)

theorem norm_phaseMap (θ : ℝ) (c : Frequency) : ‖phaseMap θ c‖=1 := by
  simpa only [phaseMap,ContinuousMap.coe_mk,pow_one,mul_zero,Real.exp_zero] using
    polyak.Waves.norm_z_pow 0 (θ*Real.arccos c) 1

theorem norm_phase_smul (ν : Spectrum) (θ : ℝ) (v : WaveSpace ν) :
    ‖(phaseLp ν θ • v : WaveSpace ν)‖=‖v‖ := by
  have hs : ‖(phaseLp ν θ • v : WaveSpace ν)‖^2=‖v‖^2 := by
    rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_lpSMul (r := 2) (phaseLp ν θ) v,
      (phaseMap θ).coeFn_toLp (p := ∞) (𝕜 := ℝ) (ν : Measure Frequency)] with c hmul hphase
    change phaseLp ν θ c = phaseMap θ c at hphase
    change inner ℝ ((phaseLp ν θ • v : WaveSpace ν) c) ((phaseLp ν θ • v : WaveSpace ν) c) = _
    rw [hmul]
    change inner ℝ (phaseLp ν θ c * v c) (phaseLp ν θ c * v c)=_
    rw [hphase,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,norm_mul,norm_phaseMap,one_mul]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

def phaseIsometry (ν : Spectrum) (θ : ℝ) : WaveSpace ν →ₗᵢ[ℝ] WaveSpace ν where
  toFun v := phaseLp ν θ • v
  map_add' v w := Lp.add_smul (phaseLp ν θ) v w
  map_smul' a v := (Lp.smul_comm a (phaseLp ν θ) v).symm
  norm_map' := norm_phase_smul ν θ

theorem phase_inverse_smul (ν : Spectrum) (v : WaveSpace ν) :
    (phaseLp ν 1 • (phaseLp ν (-1) • v : WaveSpace ν) : WaveSpace ν)=v := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (phaseLp ν 1) (phaseLp ν (-1) • v : WaveSpace ν),
    Lp.coeFn_lpSMul (r := 2) (phaseLp ν (-1)) v,
    (phaseMap 1).coeFn_toLp (p := ∞) (𝕜 := ℝ) (ν : Measure Frequency),
    (phaseMap (-1)).coeFn_toLp (p := ∞) (𝕜 := ℝ) (ν : Measure Frequency)] with c h₁ h₂ hp hm
  change phaseLp ν 1 c = phaseMap 1 c at hp
  change phaseLp ν (-1) c = phaseMap (-1) c at hm
  rw [h₁]
  change phaseLp ν 1 c * (phaseLp ν (-1) • v : WaveSpace ν) c = v c
  rw [h₂]
  change phaseLp ν 1 c * (phaseLp ν (-1) c * v c)=v c
  rw [hp,hm,← mul_assoc]
  have he : phaseMap 1 c * phaseMap (-1) c=1 := by
    simp only [phaseMap,ContinuousMap.coe_mk,polyak.Waves.z]
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    push_cast
    ring
  rw [he,one_mul]

/-- The actual orthogonal map multiplying each frequency coordinate by exp(iω). -/
def rotation (ν : Spectrum) : WaveSpace ν ≃ₗᵢ[ℝ] WaveSpace ν :=
  LinearIsometryEquiv.ofSurjective (phaseIsometry ν 1) (fun v =>
    ⟨(phaseLp ν (-1) • v : WaveSpace ν),phase_inverse_smul ν v⟩)

theorem rotation_latent (ν : Spectrum) (t : ℝ) (k : ℕ) :
    latent ν t (k+1)=Real.exp t • rotation ν (latent ν t k) := by
  apply Lp.ext
  filter_upwards [
    (polyak.Waves.positionMap t (some (k+1))).coeFn_toLp (p := 2) (𝕜 := ℝ) (ν : Measure Frequency),
    Lp.coeFn_smul (Real.exp t) (rotation ν (latent ν t k)),
    Lp.coeFn_lpSMul (r := 2) (phaseLp ν 1) (latent ν t k),
    (phaseMap 1).coeFn_toLp (p := ∞) (𝕜 := ℝ) (ν : Measure Frequency),
    (polyak.Waves.positionMap t (some k)).coeFn_toLp (p := 2) (𝕜 := ℝ) (ν : Measure Frequency)] with c hk₁ hsmul hphase hp hk
  change phaseLp ν 1 c = phaseMap 1 c at hp
  change latent ν t (k+1) c = polyak.Waves.positionMap t (some (k+1)) c at hk₁
  change latent ν t k c = polyak.Waves.positionMap t (some k) c at hk
  rw [hsmul]
  change latent ν t (k+1) c = Real.exp t • (phaseLp ν 1 • latent ν t k : WaveSpace ν) c
  rw [hphase]
  change latent ν t (k+1) c = Real.exp t • (phaseLp ν 1 c * latent ν t k c)
  rw [hp,hk₁,hk]
  change polyak.Waves.z t (Real.arccos c)^(k+1)=
    Real.exp t • (polyak.Waves.z 0 (1*Real.arccos c)*polyak.Waves.z t (Real.arccos c)^k)
  rw [one_mul,Complex.real_smul]
  have hz : polyak.Waves.z t (Real.arccos c)=(Real.exp t : ℂ)*polyak.Waves.z 0 (Real.arccos c) := by
    unfold polyak.Waves.z
    rw [Complex.ofReal_exp,← Complex.exp_add]
    congr 1
    simp
  rw [pow_succ,hz]
  ring

/-- The full memory state in its genuine Hilbert product norm. -/
def stateVector (M : StationaryMethod) (ν : Spectrum) (t : ℝ) (k : ℕ) :
    PiLp 2 (fun _ : Fin M.memory => WaveSpace ν) :=
  WithLp.toLp 2 (fun j => latent ν t (k+j.val))

/-- The orthogonal map on the whole memory-state Hilbert space. -/
def stateRotation (M : StationaryMethod) (ν : Spectrum) :
    PiLp 2 (fun _ : Fin M.memory => WaveSpace ν) ≃ₗᵢ[ℝ]
      PiLp 2 (fun _ : Fin M.memory => WaveSpace ν) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ => rotation ν)

theorem stateVector_step (M : StationaryMethod) (ν : Spectrum) (t : ℝ) (k : ℕ) :
    stateVector M ν t (k+1)=Real.exp t • stateRotation M ν (stateVector M ν t k) := by
  apply PiLp.ext
  intro j
  change latent ν t (k+1+j.val)=Real.exp t • rotation ν (latent ν t (k+j.val))
  rw [show k+1+j.val=k+j.val+1 by omega]
  exact rotation_latent ν t (k+j.val)

theorem norm_stateVector (M : StationaryMethod) (ν : Spectrum) (t : ℝ) (k : ℕ) :
    ‖stateVector M ν t k‖=M.stateNorm (latent ν t) k := by
  apply (sq_eq_sq₀ (norm_nonneg _) (M.stateNorm_nonneg _ _)).mp
  rw [PiLp.norm_sq_eq_of_L2,M.stateNorm_sq]
  rfl

/-- The complete geometric realization with one actual objective and the
literal orthogonal update of the entire memory state. -/
theorem Feasible.exists_rotating_objective {M : StationaryMethod} {μ L t C : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) {ν : Spectrum}
    (h : Feasible (M.symbolPair μ L t) t ν C) :
    ∃ f : WaveSpace ν → ℝ,polyak.CenteredSmoothStronglyConvex μ L f ∧
      M.IsTrajectory (gradient f) (latent ν t) ∧
      (∀ k,stateVector M ν t (k+1)=Real.exp t •stateRotation M ν (stateVector M ν t k)) ∧
      (∀ k,‖stateVector M ν t k‖=Real.exp (k*t)*‖stateVector M ν t 0‖) := by
  obtain ⟨f,hf,ht⟩ := h.exists_objective hμ hμL
  refine ⟨f,hf,ht,stateVector_step M ν t,fun k => ?_⟩
  rw [norm_stateVector,norm_stateVector]
  exact stateNorm_latent M ν t k

end nesterov.Spectral
