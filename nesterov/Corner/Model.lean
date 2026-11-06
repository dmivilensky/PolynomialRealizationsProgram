import nesterov.Corner.Constants
import nesterov.TwoStep.StabilityMargin

/-! Source corner coordinates are derived from the actual physical tuning. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter
open scoped Topology
variable {A : Type*} {l : Filter A} {θ : ℝ} (F : Scaling A l θ 2 (1/2))

def cornerA (p : A) : ℝ := (1/2-(F.tuning p).tau)/F.epsilon p
def cornerB (p : A) : ℝ := (2-(F.tuning p).stepSize)/F.epsilon p

theorem corner_coordinates_exact : ∀ᶠ p in l,
    (F.tuning p).tau=1/2-F.cornerA p*F.epsilon p ∧
    (F.tuning p).stepSize=2-F.cornerB p*F.epsilon p := by
  filter_upwards [F.epsilon_pos] with p hp
  unfold cornerA cornerB
  constructor <;> field_simp <;> ring

theorem corner_margin_exact : ∀ᶠ p in l,
    F.stabilityMargin p=4*F.cornerA p+2*F.cornerB p-
      2*F.cornerA p*F.cornerB p*F.epsilon p := by
  filter_upwards [F.epsilon_pos,F.corner_coordinates_exact] with p hp h
  unfold stabilityMargin
  rw [h.1,h.2]
  field_simp
  ring

theorem corner_margin_tendsto {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b)) :
    Tendsto F.stabilityMargin l (𝓝 (4*a+2*b)) := by
  have h := ((ha.const_mul 4).add (hb.const_mul 2)).sub
    (((ha.const_mul 2).mul hb).mul F.epsilon_zero)
  simp only [mul_zero,sub_zero] at h
  exact h.congr' (F.corner_margin_exact.mono fun _ h=>h.symm)

theorem corner_eventually_stable {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hstable : θ<2*a+b) :
    ∀ᶠ p in l,(F.tuning p).Stable (F.epsilon p^2) 1 :=
  F.eventually_stable_of_margin_limit (F.corner_margin_tendsto ha hb) (by linarith)

theorem corner_eventually_unstable {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hunstable : 2*a+b<θ) :
    ∀ᶠ p in l,¬(F.tuning p).Stable (F.epsilon p^2) 1 :=
  F.eventually_unstable_of_margin_limit (F.corner_margin_tendsto ha hb) (by linarith)

end
end nesterov.TwoStep.Scaling
