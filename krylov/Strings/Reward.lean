import krylov.Strings.TypeClock
import krylov.Strings.StateRegularity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
Article: main_krylov, s3:def:string, actual continuum reward.
Use: define the nonnegative reward from the actual string energy and type
density, allowing an infinite reward, and justify all finite physical integrals.
Source: local RN integrability and monotone convergence in mathlib.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace Mass

/-- Reward per unit physical length for the actual string state. -/
def rewardDensity (M : Mass) (γ : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  integralEnergy M.measure φ x ^ (-γ) * M.typeDensity x

/-- The reward is nonnegative independently of any integrability conclusion. -/
theorem rewardDensity_nonneg (M : Mass) (γ : ℝ) (φ : ℝ → ℝ) (x : ℝ) :
    0 ≤ M.rewardDensity γ φ x :=
  mul_nonneg (Real.rpow_nonneg (by linarith [integralEnergy_one_le M.measure φ x]) _)
    (M.typeDensity_nonneg x)

/-- For positive gamma, the type density dominates the reward density. -/
theorem rewardDensity_le_typeDensity (M : Mass) {γ : ℝ} (hγ : 0 ≤ γ)
    (φ : ℝ → ℝ) (x : ℝ) : M.rewardDensity γ φ x ≤ M.typeDensity x := by
  exact mul_le_of_le_one_left (M.typeDensity_nonneg x)
    (Real.rpow_le_one_of_one_le_of_nonpos (integralEnergy_one_le _ _ _) (neg_nonpos.mpr hγ))

/-- Measurability follows from the actual monotone energy, not an assumed
measurability field for an abstract reward profile. -/
theorem measurable_rewardDensity (M : Mass) (γ : ℝ) {φ : ℝ → ℝ} (hc : Continuous φ) :
    Measurable (M.rewardDensity γ φ) :=
  ((M.energy_monotone hc).measurable.pow_const (-γ)).mul M.measurable_typeDensity

/-- Every compact physical reward integral is finite, even with general
singular mass and without finite total mass on the half-line. -/
theorem rewardDensity_integrableOn (M : Mass) {γ : ℝ} (hγ : 0 ≤ γ)
    {φ : ℝ → ℝ} (hc : Continuous φ) (a b : ℝ) :
    IntegrableOn (M.rewardDensity γ φ) (Ioc a b) volume := by
  apply (M.typeDensity_integrableOn a b).mono'
    (M.measurable_rewardDensity γ hc).aestronglyMeasurable.restrict
  filter_upwards with x
  rw [Real.norm_of_nonneg (M.rewardDensity_nonneg γ φ x)]
  exact M.rewardDensity_le_typeDensity hγ φ x

/-- Extended nonnegative reward: divergent strings are not assigned zero
by the default value of a nonintegrable real Bochner integral. -/
def reward (M : Mass) (γ : ℝ) (φ : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (M.rewardDensity γ φ x)

/-- The actual reward accumulated before a finite physical endpoint. -/
def rewardPrefix (M : Mass) (γ : ℝ) (φ : ℝ → ℝ) (X : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioc 0 X, ENNReal.ofReal (M.rewardDensity γ φ x)

/-- Prefix rewards increase with physical length, including singular strings. -/
theorem rewardPrefix_mono (M : Mass) (γ : ℝ) (φ : ℝ → ℝ) :
    Monotone (M.rewardPrefix γ φ) := by
  intro a b hab
  exact lintegral_mono_set (fun _ hx ↦ ⟨hx.1, hx.2.trans hab⟩)

/-- The full nonnegative reward is exactly the increasing limit of actual
finite-prefix rewards. No global integrability is assumed. -/
theorem reward_eq_iSup_prefix (M : Mass) (γ : ℝ) (φ : ℝ → ℝ) :
    M.reward γ φ = ⨆ n : ℕ, M.rewardPrefix γ φ n := by
  have hcover : (⋃ n : ℕ, Ioc (0 : ℝ) (n : ℝ)) = Ioi 0 :=
    iUnion_Ioc_eq_Ioi_self_iff.mpr fun x _ ↦ exists_nat_ge x
  have hmono : Monotone (fun n : ℕ ↦ Ioc (0 : ℝ) (n : ℝ)) := by
    intro n m hnm x hx
    exact ⟨hx.1, hx.2.trans (by exact_mod_cast hnm)⟩
  unfold reward rewardPrefix
  rw [← hcover]
  exact setLIntegral_iUnion_of_directed _ hmono.directed_le

/-- Uniform finite-prefix bounds control the full reward, including arbitrary
singular mass and infinitely many atoms. -/
theorem reward_le_of_prefix_le (M : Mass) (γ : ℝ) (φ : ℝ → ℝ)
    {C : ℝ≥0∞} (h : ∀ X ≥ 0, M.rewardPrefix γ φ X ≤ C) :
    M.reward γ φ ≤ C := by
  rw [M.reward_eq_iSup_prefix]
  exact iSup_le fun n ↦ h n (Nat.cast_nonneg n)

end Mass
end
end krylov.Strings
