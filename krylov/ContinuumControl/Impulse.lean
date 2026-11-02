import krylov.ContinuumControl.SmoothIdentity

/-!
Article: main_krylov, apC:lem:fund, the atom term Jξ.
Use: an atom is unfolded into the genuine straight state curve
(φ,p+uφ,K+uφ²). Its exact potential loss is an integral, and every positive
atom causes a strictly positive loss. No limiting small-atom assumption enters.
Source: the chain rule and fundamental theorem of calculus in mathlib.
-/

namespace krylov.ContinuumControl
noncomputable section
open Set MeasureTheory

/-- The positive mass-direction loss coefficient, before its factor 1/2.
Article: main_krylov, apC:lem:fund. -/
def massLossRate (γ : ℝ) (σ : ℝ → ℝ) (φ p K : ℝ) : ℝ :=
  K ^ (-γ) * φ * Real.sqrt (σ (φ * p / K)) / p

/-- The exact finite-atom loss in the fundamental identity.
Article: main_krylov, apC:lem:fund, Jξ. -/
def impulseLoss (γ : ℝ) (σ : ℝ → ℝ) (φ p K m : ℝ) : ℝ :=
  1 / 2 * ∫ u in 0..m, massLossRate γ σ φ (p + u * φ) (K + u * φ ^ 2)

/-- The two increasing impulse coordinates remain strictly positive.
Article: main_krylov, apC:eq:state, atom update. -/
theorem impulse_coordinates_pos {φ p K u : ℝ} (hφ : 0 < φ)
    (hp : 0 < p) (hK : 0 < K) (hu : 0 ≤ u) :
    0 < p + u * φ ∧ 0 < K + u * φ ^ 2 :=
  ⟨add_pos_of_pos_of_nonneg hp (mul_nonneg hu hφ.le),
    add_pos_of_pos_of_nonneg hK (mul_nonneg hu (sq_nonneg _))⟩

/-- Continuous loss along the unfolded atom follows from differentiability of
the graph, rather than being assumed as an integrability certificate.
Article: main_krylov, apC:lem:fund, impulse integration. -/
theorem continuousOn_impulse_massLossRate {γ φ p K m : ℝ} {σ : ℝ → ℝ}
    (hφ : 0 < φ) (hp : 0 < p) (hK : 0 < K) (hm : 0 ≤ m)
    (hgraph : ∀ u ∈ Icc 0 m,
      FeedbackGraphAt γ σ (φ * (p + u * φ) / (K + u * φ ^ 2))) :
    ContinuousOn (fun u => massLossRate γ σ φ (p + u * φ) (K + u * φ ^ 2))
      (uIcc 0 m) := by
  intro u hu
  have hu' : u ∈ Icc 0 m := (uIcc_of_le hm) ▸ hu
  have hpos := impulse_coordinates_pos hφ hp hK hu'.1
  have hpc : ContinuousAt (fun u => p + u * φ) u :=
    continuousAt_const.add (continuousAt_id.mul continuousAt_const)
  have hKc : ContinuousAt (fun u => K + u * φ ^ 2) u :=
    continuousAt_const.add (continuousAt_id.mul continuousAt_const)
  have hrc : ContinuousAt (fun u => φ * (p + u * φ) / (K + u * φ ^ 2)) u :=
    (continuousAt_const.mul hpc).div hKc (ne_of_gt hpos.2)
  have hσc := (hgraph u hu').differentiable.continuousAt.comp
    (f := fun v => φ * (p + v * φ) / (K + v * φ ^ 2)) hrc
  exact ((((hKc.rpow_const (Or.inl (ne_of_gt hpos.2))).mul continuousAt_const).mul
    hσc.sqrt).div hpc (ne_of_gt hpos.1)).continuousWithinAt

/-- Derivative along a finite impulse, including its two endpoints whenever
the graph equation is valid there.
Article: main_krylov, apC:lem:fund, impulse derivative. -/
theorem hasDerivAt_impulse_stateValue {γ φ p K u : ℝ} {σ : ℝ → ℝ}
    (hγ : γ ≠ 0) (hφ : 0 < φ) (hp : 0 < p) (hK : 0 < K) (hu : 0 ≤ u)
    (hgraph : FeedbackGraphAt γ σ (φ * (p + u * φ) / (K + u * φ ^ 2))) :
    HasDerivAt (fun v => stateValue γ σ φ (p + v * φ) (K + v * φ ^ 2))
      (-(1 / 2 * massLossRate γ σ φ (p + u * φ) (K + u * φ ^ 2))) u := by
  have hpos := impulse_coordinates_pos hφ hp hK hu
  have hd := hasDerivAt_stateValue (γ := γ) (x := u) (dx := 0) (dm := 1)
    (φ := fun _ => φ) (p := fun v => p + v * φ) (K := fun v => K + v * φ ^ 2)
    hγ (ne_of_gt hφ) (ne_of_gt hpos.1) hpos.2 hgraph.positive
    hgraph.differentiable.hasDerivAt hgraph.equation
    (by simpa only [mul_zero] using hasDerivAt_const u φ)
    (by simpa only [id_eq, mul_one, one_mul] using
      ((hasDerivAt_id u).mul_const φ).const_add p)
    (by simpa only [id_eq, mul_one, one_mul] using
      ((hasDerivAt_id u).mul_const (φ ^ 2)).const_add K)
  convert hd using 1
  dsimp only [massLossRate]
  ring

/-- Exact potential decrement across every finite atom.
Article: main_krylov, apC:lem:fund, Jξ formula. -/
theorem impulse_potential_decrement {γ φ p K m : ℝ} {σ : ℝ → ℝ}
    (hγ : γ ≠ 0) (hφ : 0 < φ) (hp : 0 < p) (hK : 0 < K) (hm : 0 ≤ m)
    (hgraph : ∀ u ∈ Icc 0 m,
      FeedbackGraphAt γ σ (φ * (p + u * φ) / (K + u * φ ^ 2))) :
    stateValue γ σ φ p K - stateValue γ σ φ (p + m * φ) (K + m * φ ^ 2) =
      impulseLoss γ σ φ p K m := by
  have hc := continuousOn_impulse_massLossRate hφ hp hK hm hgraph
  have hi : IntervalIntegrable
      (fun u => massLossRate γ σ φ (p + u * φ) (K + u * φ ^ 2)) volume 0 m :=
    hc.intervalIntegrable
  have hint := (hi.const_mul (1 / 2)).neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu =>
    hasDerivAt_impulse_stateValue hγ hφ hp hK ((uIcc_of_le hm ▸ hu).1)
      (hgraph u (uIcc_of_le hm ▸ hu))) hint
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hFTC
  simp only [zero_mul, add_zero] at hFTC
  unfold impulseLoss
  linarith

/-- Every nonzero atom strictly lowers the Bellman potential.
Article: main_krylov, apC:lem:fund, Jξ > 0. -/
theorem impulseLoss_pos {γ φ p K m : ℝ} {σ : ℝ → ℝ}
    (hφ : 0 < φ) (hp : 0 < p) (hK : 0 < K) (hm : 0 < m)
    (hgraph : ∀ u ∈ Icc 0 m,
      FeedbackGraphAt γ σ (φ * (p + u * φ) / (K + u * φ ^ 2))) :
    0 < impulseLoss γ σ φ p K m := by
  apply mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (continuousOn_impulse_massLossRate hφ hp hK hm.le hgraph).intervalIntegrable
    (fun u hu => ?_) hm
  have hpos := impulse_coordinates_pos hφ hp hK hu.1.le
  exact div_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos hpos.2 _) hφ)
    (Real.sqrt_pos.2 (hgraph u ⟨hu.1.le, hu.2.le⟩).positive)) hpos.1

/-- An impulse is lossless exactly when no mass is inserted.
Article: main_krylov, proof of thm:value, exclusion of positive atoms. -/
theorem impulseLoss_eq_zero_iff {γ φ p K m : ℝ} {σ : ℝ → ℝ}
    (hφ : 0 < φ) (hp : 0 < p) (hK : 0 < K) (hm : 0 ≤ m)
    (hgraph : ∀ u ∈ Icc 0 m,
      FeedbackGraphAt γ σ (φ * (p + u * φ) / (K + u * φ ^ 2))) :
    impulseLoss γ σ φ p K m = 0 ↔ m = 0 := by
  constructor
  · intro hzero
    by_contra hmzero
    have hpos := impulseLoss_pos hφ hp hK (lt_of_le_of_ne hm (Ne.symm hmzero)) hgraph
    linarith
  · intro hzero
    simp [hzero, impulseLoss]

/-- Inserting positive atomic mass strictly decreases the genuine potential.
Article: main_krylov, apC:lem:fund, strict atom loss. -/
theorem impulse_stateValue_lt {γ φ p K m : ℝ} {σ : ℝ → ℝ}
    (hγ : γ ≠ 0) (hφ : 0 < φ) (hp : 0 < p) (hK : 0 < K) (hm : 0 < m)
    (hgraph : ∀ u ∈ Icc 0 m,
      FeedbackGraphAt γ σ (φ * (p + u * φ) / (K + u * φ ^ 2))) :
    stateValue γ σ φ (p + m * φ) (K + m * φ ^ 2) < stateValue γ σ φ p K := by
  have hd := impulse_potential_decrement hγ hφ hp hK hm.le hgraph
  have hp := impulseLoss_pos hφ hp hK hm hgraph
  linarith

end
end krylov.ContinuumControl
