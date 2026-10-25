import polyak.GapEdges.Tips.Base
import polyak.FareyPlateau.Edge.Certificate
import polyak.ModeLocking.Regular.Endpoints

/-! The strictly positive three-lag symbol at every actual tongue tip is
constructed by a compact perturbation; its existence is not a premise. -/
noncomputable section
namespace polyak.GapEdges.Tip
open General Levels ModeLocking Set Filter
open scoped Topology BigOperators
variable {q : Tuning} {k : ℕ} (T : Tip q k)
include T

def lags (k : ℕ) : Finset ℤ := {1, 1 + (k : ℤ), 1 - (k : ℤ)}

def weight (ε : ℝ) (n : ℤ) : ℝ := if n = 1 then 1 - 2 * ε else ε

def perturbation (T : Tip q k) (x : ℝ) : ℝ :=
  let _ := T

  lagExtension q 0 (1 + (k : ℤ)) x + lagExtension q 0 (1 - (k : ℤ)) x -
    2 * lagExtension q 0 1 x

theorem lag_mem_classes {n : ℤ} (hn : n ∈ lags k) : n % (k : ℤ) = 1 := by
  have hk : 1 < (k : ℤ) := by have := T.period_ge; omega
  have ho : (1 : ℤ) % (k : ℤ) = 1 := Int.emod_eq_of_lt (by norm_num) hk
  simp only [lags, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl
  · exact ho
  · simp only [Int.add_emod, Int.emod_self, add_zero, ho]
  · simp only [Int.sub_emod, Int.emod_self, sub_zero, ho]

theorem symbol_formula (ε x : ℝ) :
    finiteSymbol q 0 (lags k) (weight ε) x =
      lagExtension q 0 1 x + ε * T.perturbation x := by
  have hk := T.period_ge
  have h₁ : (1 : ℤ) ≠ 1 + (k : ℤ) := by omega
  have h₂ : (1 : ℤ) ≠ 1 - (k : ℤ) := by omega
  have h₃ : 1 + (k : ℤ) ≠ 1 - (k : ℤ) := by omega
  have hm₁ : (1 : ℤ) ∉ ({1 + (k : ℤ), 1 - (k : ℤ)} : Finset ℤ) := by simp [h₁, h₂]
  have hm₂ : 1 + (k : ℤ) ∉ ({1 - (k : ℤ)} : Finset ℤ) := by simp [h₃]
  simp only [finiteSymbol, lags, Finset.sum_insert hm₁,
    Finset.sum_insert hm₂, Finset.sum_singleton,
    weight, ite_true, ite_eq_right h₁.symm, ite_eq_right h₂.symm, perturbation]
  ring

theorem perturbation_analytic {x : ℝ} (hx : x ∈ Icc (0 : ℝ) Real.pi) :
    AnalyticAt ℝ T.perturbation x :=
  ((ModeLocking.analyticAt_lagExtension q 0 _ hx).add
    (ModeLocking.analyticAt_lagExtension q 0 _ hx)).sub
      (analyticAt_const.mul (ModeLocking.analyticAt_lagExtension q 0 1 hx))

omit T in
theorem lag_endpoint (n : ℤ) : lagExtension q 0 n 0 = 0 := by
  change lagExtension q 0 n frequencyZero = 0
  rw [lagExtension_actual, Curve.lag_at_zero]

theorem perturbation_zero (x : ℝ) (hx : x = 0 ∨ x = (T.frequency : ℝ)) :
    T.perturbation x = 0 := by
  rcases hx with rfl | rfl
  · simp only [perturbation, lag_endpoint (q := q), add_zero, mul_zero, sub_zero]
  · simp only [perturbation,
      T.lag_zero (T.lag_mem_classes (by simp [lags] : 1 + (k : ℤ) ∈ lags k)),
      T.lag_zero (T.lag_mem_classes (by simp [lags] : 1 - (k : ℤ) ∈ lags k)),
      T.lag_zero (T.lag_mem_classes (by simp [lags] : (1 : ℤ) ∈ lags k)),
      add_zero, mul_zero, sub_zero]

theorem perturbation_slope (x : ℝ) (hx : x = 0 ∨ x = (T.frequency : ℝ)) :
    deriv T.perturbation x = 0 := by
  have hxm : x ∈ Icc (0 : ℝ) Real.pi := by
    rcases hx with rfl | rfl
    · exact ⟨le_rfl, Real.pi_pos.le⟩
    · exact T.frequency.property
  have hd : HasDerivAt T.perturbation
      (deriv (lagExtension q 0 (1 + (k : ℤ))) x +
        deriv (lagExtension q 0 (1 - (k : ℤ))) x - 2 * deriv (lagExtension q 0 1) x) x := by
    exact (((ModeLocking.analyticAt_lagExtension q 0 (1 + (k : ℤ)) hxm).differentiableAt.hasDerivAt).add
      ((ModeLocking.analyticAt_lagExtension q 0 (1 - (k : ℤ)) hxm).differentiableAt.hasDerivAt)).sub
      (((ModeLocking.analyticAt_lagExtension q 0 1 hxm).differentiableAt.hasDerivAt).const_mul 2)
  rw [hd.deriv]
  rcases hx with rfl | rfl
  · simp only [lagExtension_deriv_zero, add_zero, mul_zero, sub_zero]
  · rw [T.lag_first (T.lag_mem_classes (by simp [lags] : 1 + (k : ℤ) ∈ lags k)),
      T.lag_first (T.lag_mem_classes (by simp [lags] : 1 - (k : ℤ) ∈ lags k)),
      T.lag_first (T.lag_mem_classes (by simp [lags] : (1 : ℤ) ∈ lags k))]
    push_cast
    ring

theorem exists_negative_cover : ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧
    Nonempty (Analysis.NegativeJetCover 0 Real.pi {0, (T.frequency : ℝ)}
      (finiteSymbol q 0 (lags k) (weight ε))) := by
  classical
  let Z : Finset ℝ := {0, (T.frequency : ℝ)}
  have hZ : ∀ z ∈ Z, z ∈ Icc (0 : ℝ) Real.pi := by
    intro z hz
    simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨le_rfl, Real.pi_pos.le⟩
    · exact T.frequency.property
  have hf : ∀ x ∈ Icc (0 : ℝ) Real.pi, ContDiffAt ℝ 2 (lagExtension q 0 1) x :=
    fun _ hx => (ModeLocking.analyticAt_lagExtension q 0 1 hx).contDiffAt
  have hf2 : ContinuousOn (iteratedDeriv 2 (lagExtension q 0 1)) (Icc (0 : ℝ) Real.pi) := by
    intro x hx
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    exact (ModeLocking.analyticAt_lagExtension q 0 1 hx).deriv.deriv.continuousAt.continuousWithinAt
  have hzero : ∀ z ∈ Z, lagExtension q 0 1 z = 0 := by
    intro z hz
    simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact lag_endpoint (q := q) 1
    · exact T.lag_zero (T.lag_mem_classes (by simp [lags]))
  have hslope : ∀ z ∈ Z, deriv (lagExtension q 0 1) z = 0 := by
    intro z hz
    simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact lagExtension_deriv_zero q 0 1
    · rw [T.lag_first (T.lag_mem_classes (by simp [lags]))]
      norm_num
  have hcurv : ∀ z ∈ Z, iteratedDeriv 2 (lagExtension q 0 1) z < 0 := by
    intro z hz
    rw [iteratedDeriv_eq_iterate]
    simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · rw [lagExtension_second_zero]
      norm_num only [Int.cast_one, one_mul]
      linarith [Geometry.tau_pos q]
    · exact T.lag_one_curvature
  have hstrict : ∀ x ∈ Icc (0 : ℝ) Real.pi, x ∉ Z → lagExtension q 0 1 x < 0 := by
    intro x hx hn
    simp only [Z, Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    exact T.lag_one_strict (lt_of_le_of_ne hx.1 (Ne.symm hn.1)) hx.2 hn.2
  have hE2 : ContinuousOn (iteratedDeriv 2 T.perturbation) (Icc (0 : ℝ) Real.pi) := by
    intro x hx
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    exact (T.perturbation_analytic hx).deriv.deriv.continuousAt.continuousWithinAt
  obtain ⟨r, hr, hperturb⟩ := Analysis.finite_zero_perturbation
    (show Z.Nonempty from ⟨0, by simp [Z]⟩) hZ hf hf2 hzero hslope hcurv hstrict
    (fun _ hx => (T.perturbation_analytic hx).contDiffAt) hE2
    (fun z hz => T.perturbation_zero z (by simpa only [Z, Finset.mem_insert, Finset.mem_singleton] using hz))
    (fun z hz => T.perturbation_slope z (by simpa only [Z, Finset.mem_insert, Finset.mem_singleton] using hz))
  let ε := min r (1 / 2) / 2
  have hε : 0 < ε := div_pos (lt_min hr (by norm_num)) (by norm_num)
  have hεr : ε < r := by
    have hh := min_le_left r (1 / 2 : ℝ)
    dsimp [ε] at hε ⊢
    linarith
  have hεhalf : ε < 1 / 2 := by
    have hh := min_le_right r (1 / 2 : ℝ)
    dsimp [ε] at hε ⊢
    linarith
  refine ⟨ε, hε, hεhalf, ?_⟩
  have hfun : finiteSymbol q 0 (lags k) (weight ε) =
      fun x => lagExtension q 0 1 x + ε * T.perturbation x := funext (T.symbol_formula ε)
  rw [hfun]
  exact hperturb ε (by rw [abs_of_pos hε]; exact hεr)

end polyak.GapEdges.Tip
