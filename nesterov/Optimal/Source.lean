import nesterov.Optimal.Necessity
import nesterov.TwoStep.FrontierRigidity

/-! The complete optimal-tuning theorem for unrestricted stable physical families.
Convergence to the corner is a conclusion on the forward implication. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

def tuningCornerAlpha (ε : ℝ) (q : Momentum.Tuning) : ℝ :=
  (1/2-q.tau)*q.stepSize/(2*ε)
def tuningCornerMargin (ε : ℝ) (q : Momentum.Tuning) : ℝ :=
  (4-q.stepSize*(1+2*q.tau))/ε

def tuningCornerN (ε : ℝ) (q : Momentum.Tuning) (ξ : ℝ) : ℝ :=
  4*((1-q.beta)/ε)+2*((1-q.beta)/ε-4*tuningCornerAlpha ε q)*ξ+
    (tuningCornerMargin ε q+4*tuningCornerAlpha ε q-4*((1-q.beta)/ε))*ξ^2

def tuningCornerLag (ε : ℝ) (q : Momentum.Tuning) : ℝ :=
  sInf ((fun ξ=>tuningCornerN ε q ξ/(4*(3-ξ))) '' Icc 0 2)

def tuningCornerDefect (ε : ℝ) (q : Momentum.Tuning) : ℝ :=
  max (4*tuningCornerAlpha ε q-5) 0

def tuningCornerCriterionRatio (ε : ℝ) (q : Momentum.Tuning) : ℝ :=
  tuningCornerDefect ε q^2/(tuningCornerMargin ε q+5+tuningCornerDefect ε q)

def tuningRestCoefficient (ε : ℝ) (q : Momentum.Tuning) : ℝ :=
  (1-Momentum.momentumRestRate q.beta q.tau q.stepSize q.step_pos.ne' (ε^2) 1)/ε

variable {A : Type*} {l : Filter A} {ε : A→ℝ} {q : A→Momentum.Tuning}

def cornerFamilyOfData (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hdata : Tendsto (fun p=>parameterTriple (ε p) (q p)) l (𝓝 (3,(2,1/2)))) :
    Scaling A l 3 2 (1/2) where
  epsilon := ε
  tuning := q
  epsilon_tendsto := he
  theta_tendsto := (continuous_fst.tendsto _).comp hdata
  step_tendsto := (continuous_fst.tendsto _).comp ((continuous_snd.tendsto _).comp hdata)
  tau_tendsto := (continuous_snd.tendsto _).comp ((continuous_snd.tendsto _).comp hdata)
  theta_pos := by norm_num
  step_pos := by norm_num
  tau_nonneg := by norm_num

namespace Scaling
variable {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem tuningCornerLag_eq (p : A) :
    tuningCornerLag (F.epsilon p) (F.tuning p)=F.cornerLagAt p := rfl

end Scaling

/-- The source theorem, with no prior limit or boundedness hypothesis on tuning parameters. -/
theorem optimal_tuning_family_iff [l.IsCountablyGenerated] [NeBot l]
    (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ p in l,(q p).Stable (ε p^2) 1) :
    Tendsto (fun p=>tuningFullCoefficient (ε p) (q p)) l (𝓝 1) ↔
      Tendsto (fun p=>parameterTriple (ε p) (q p)) l (𝓝 (3,(2,1/2))) ∧
        Tendsto (fun p=>tuningCornerLag (ε p) (q p)) l (𝓝 1) := by
  constructor
  · intro hfull
    have hdata := optimal_parameters_tendsto he hstable (by
      have hco : Tendsto (fun p=>(tuningFullCoefficient (ε p) (q p):EReal)) l (𝓝 (1:EReal)) :=
        EReal.tendsto_coe.mpr hfull
      rw [hco.liminf_eq])
    let F := cornerFamilyOfData he hdata
    have hFs : ∀ᶠ p in l,(F.tuning p).Stable (F.epsilon p^2) 1 := hstable
    have hFfull : Tendsto F.fullCoefficientAt l (𝓝 1) := hfull
    exact ⟨hdata,F.optimal_lag_minimum_necessary hFs hFfull⟩
  · rintro ⟨hdata,hmin⟩
    let F := cornerFamilyOfData he hdata
    have hFs : ∀ᶠ p in l,(F.tuning p).Stable (F.epsilon p^2) 1 := hstable
    have hFmin : Tendsto F.cornerLagAt l (𝓝 1) := hmin
    exact (F.optimal_coefficients_tendsto hFs hFmin).1

theorem optimal_tuning_rest_limit [l.IsCountablyGenerated] [NeBot l]
    (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ p in l,(q p).Stable (ε p^2) 1)
    (hfull : Tendsto (fun p=>tuningFullCoefficient (ε p) (q p)) l (𝓝 1)) :
    Tendsto (fun p=>tuningRestCoefficient (ε p) (q p)) l (𝓝 1) := by
  obtain ⟨hdata,hmin⟩ := (optimal_tuning_family_iff he hstable).mp hfull
  let F := cornerFamilyOfData he hdata
  have hFs : ∀ᶠ p in l,(F.tuning p).Stable (F.epsilon p^2) 1 := hstable
  have hFmin : Tendsto F.cornerLagAt l (𝓝 1) := hmin
  exact (F.optimal_coefficients_tendsto hFs hFmin).2


theorem optimal_tuning_ratio_reformulation [NeBot l]
    (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ p in l,(q p).Stable (ε p^2) 1)
    (hdata : Tendsto (fun p=>parameterTriple (ε p) (q p)) l (𝓝 (3,(2,1/2)))) :
    Tendsto (fun p=>tuningCornerLag (ε p) (q p)) l (𝓝 1) ↔
      (7:EReal)≤liminf (fun p=>(tuningCornerMargin (ε p) (q p):EReal)) l ∧
        Tendsto (fun p=>tuningCornerCriterionRatio (ε p) (q p)) l (𝓝 0) := by
  let F := cornerFamilyOfData he hdata
  have hFs : ∀ᶠ p in l,(F.tuning p).Stable (F.epsilon p^2) 1 := hstable
  exact F.corner_ratio_criterion_iff hFs

theorem optimal_tuning_family_ratio_iff [l.IsCountablyGenerated] [NeBot l]
    (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ p in l,(q p).Stable (ε p^2) 1) :
    Tendsto (fun p=>tuningFullCoefficient (ε p) (q p)) l (𝓝 1) ↔
      Tendsto (fun p=>parameterTriple (ε p) (q p)) l (𝓝 (3,(2,1/2))) ∧
        (7:EReal)≤liminf (fun p=>(tuningCornerMargin (ε p) (q p):EReal)) l ∧
          Tendsto (fun p=>tuningCornerCriterionRatio (ε p) (q p)) l (𝓝 0) := by
  rw [optimal_tuning_family_iff he hstable]
  constructor
  · rintro ⟨hdata,hmin⟩
    exact ⟨hdata,(optimal_tuning_ratio_reformulation he hstable hdata).mp hmin⟩
  · rintro ⟨hdata,hm,hr⟩
    exact ⟨hdata,(optimal_tuning_ratio_reformulation he hstable hdata).mpr ⟨hm,hr⟩⟩

end
end nesterov.TwoStep
