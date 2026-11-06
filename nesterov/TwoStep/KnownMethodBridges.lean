import nesterov.TwoStep.KnownTuningRates
import nesterov.Momentum.CorrectionRates
import nesterov.Momentum.Scaling

/-! Physical gradient-correction executors for the over-relaxed heavy-ball
clause of Corollary B, retaining the actual uniform factor. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

/-- The source over-relaxed update is precisely gradient correction with
h₁=2γ, h₂=γ, hence τ=1 and h=γ. -/
theorem overrelaxed_physical_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E→E) (β γ : ℝ) (p : E × E) :
    Momentum.Correction.step g β 1 γ p=
      (p.2,p.2+β • (p.2-p.1)-γ • ((2:ℝ) • g p.2-g p.1)) := by
  simp only [Momentum.Correction.step]
  apply Prod.ext
  · rfl
  · module

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

/-- For every scaling family the source determinant tends to one. In
particular the exceptional correction realization is excluded eventually. -/
theorem correction_determinant_tendsto :
    Tendsto (fun a=>Momentum.Correction.determinant (F.tuning a).beta (F.tuning a).tau) l (𝓝 1) := by
  have hh := ((F.tau_tendsto.const_add 1).mul F.beta_tendsto).sub F.tau_tendsto
  have hv : (1+τ)*1-τ=1 := by ring
  simpa only [Momentum.Correction.determinant,hv] using hh

/-- The physical gradient-correction factor equals the latent momentum factor
for every sufficiently small family member; no extra nondegeneracy is assumed. -/
theorem correction_rate_eventually_eq :
    ∀ᶠ a in l,Momentum.Correction.rate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
      (F.epsilon a^2) 1=Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
        (F.tuning a).step_pos.ne' (F.epsilon a^2) 1 := by
  filter_upwards [F.correction_determinant_tendsto.eventually_ne (by norm_num : (1:ℝ)≠0),
    F.epsilon_pos,F.epsilon_zero.eventually (eventually_lt_nhds zero_lt_one)] with a hd he he1
  exact Momentum.Correction.rate_eq_momentumRate (F.tuning a).step_pos.ne' hd
    (sq_pos_of_pos he) (by nlinarith)

end Scaling

/-- Objective/step normalization also preserves the literal correction rate. -/
theorem correction_rate_normalized {β τ h μ L : ℝ} (hh : h≠0)
    (hd : Momentum.Correction.determinant β τ≠0) (hμ : 0<μ) (hμL : μ<L) :
    Momentum.Correction.rate β τ (h*L) (μ/L) 1=Momentum.Correction.rate β τ h μ L := by
  have hL : 0<L := hμ.trans hμL
  rw [Momentum.Correction.rate_eq_momentumRate (mul_ne_zero hh hL.ne') hd
    (div_pos hμ hL) ((div_lt_one hL).mpr hμL),
    Momentum.Correction.rate_eq_momentumRate hh hd hμ hμL]
  exact Momentum.momentumRate_normalized β τ h μ L hh hL

namespace KnownTunings

/-- The source physical parameter β=Lγ is exactly the normalized parameter
(1+ε)⁻², with ε=√(μ/L). -/
theorem overrelaxed_normalized_parameters {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    L*(1/(Real.sqrt L+Real.sqrt μ)^2)=overrelaxedStep (Real.sqrt (μ/L)) := by
  have hL : 0<L := hμ.trans hμL
  have hsL : 0<Real.sqrt L := Real.sqrt_pos.mpr hL
  have hid : 1+Real.sqrt μ/Real.sqrt L=(Real.sqrt L+Real.sqrt μ)/Real.sqrt L := by
    field_simp [hsL.ne']
  symm
  calc
    overrelaxedStep (Real.sqrt (μ/L))=(Real.sqrt L/(Real.sqrt L+Real.sqrt μ))^2 := by
      unfold overrelaxedStep
      rw [Real.sqrt_div hμ.le,hid,inv_div]
    _=L/(Real.sqrt L+Real.sqrt μ)^2 := by rw [div_pow,Real.sq_sqrt hL.le]
    _=L*(1/(Real.sqrt L+Real.sqrt μ)^2) := by ring

/-- Corollary B(iv) for the actual over-relaxed gradient-correction execution,
with arbitrary initial physical memories and the supremum before the limit. -/
theorem overrelaxed_physical_rate :
    Tendsto (fun ε : ℝ=>(1-Momentum.Correction.rate (overrelaxedStep ε) 1 (overrelaxedStep ε)
      (ε^2) 1)/ε) (𝓝[>] (0:ℝ)) (𝓝 (2/3:ℝ)) := by
  have heq : (fun ε : ℝ=>overrelaxed.fullCoefficient ε)=ᶠ[𝓝[>] (0:ℝ)]
      (fun ε : ℝ=>(1-Momentum.Correction.rate (overrelaxedStep ε) 1 (overrelaxedStep ε) (ε^2) 1)/ε) := by
    filter_upwards [overrelaxed.correction_rate_eventually_eq,overrelaxed_parameters] with ε hr hp
    change Momentum.Correction.rate _ _ _ (ε^2) 1=Momentum.momentumRate _ _ _ _ (ε^2) 1 at hr
    unfold Scaling.fullCoefficient
    rw [←hr,hp.1,hp.2.1,hp.2.2]
  exact overrelaxed_rates.1.congr' heq

end KnownTunings
end
end nesterov.TwoStep
