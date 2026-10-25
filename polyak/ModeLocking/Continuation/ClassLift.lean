import polyak.ModeLocking.Regular.Definitions

/-! Explicit affine right inverse for a class sum and its slope moment.
The correction changes two chosen lags and leaves every other weight fixed. -/
noncomputable section
namespace polyak.ModeLocking.Continuation
open scoped BigOperators

def classSum (N : Finset ℤ) (a : ℤ → ℝ) : ℝ := ∑ n ∈ N, a n

def classMoment (N : Finset ℤ) (t a : ℤ → ℝ) : ℝ := ∑ n ∈ N, a n * t n

def liftFirst (t₁ t₂ u v : ℝ) : ℝ := (v - t₂ * u) / (t₁ - t₂)
def liftSecond (t₁ t₂ u v : ℝ) : ℝ := (t₁ * u - v) / (t₁ - t₂)

theorem lift_sum {t₁ t₂ : ℝ} (ht : t₁ ≠ t₂) (u v : ℝ) :
    liftFirst t₁ t₂ u v + liftSecond t₁ t₂ u v = u := by
  unfold liftFirst liftSecond
  field_simp
  ring

theorem lift_moment {t₁ t₂ : ℝ} (ht : t₁ ≠ t₂) (u v : ℝ) :
    liftFirst t₁ t₂ u v * t₁ + liftSecond t₁ t₂ u v * t₂ = v := by
  unfold liftFirst liftSecond
  field_simp
  ring

def affineClassLift (N : Finset ℤ) (a t : ℤ → ℝ) (n₁ n₂ : ℤ)
    (μ m : ℝ) (n : ℤ) : ℝ := a n +
  (if n = n₁ then liftFirst (t n₁) (t n₂) (μ - classSum N a) (m - classMoment N t a) else 0) +
  (if n = n₂ then liftSecond (t n₁) (t n₂) (μ - classSum N a) (m - classMoment N t a) else 0)

theorem affineClassLift_base (N : Finset ℤ) (a t : ℤ → ℝ) (n₁ n₂ n : ℤ) :
    affineClassLift N a t n₁ n₂ (classSum N a) (classMoment N t a) n = a n := by
  simp [affineClassLift, liftFirst, liftSecond]

theorem affineClassLift_outside (N : Finset ℤ) (a t : ℤ → ℝ) (n₁ n₂ : ℤ)
    (μ m : ℝ) {n : ℤ} (h₁ : n ≠ n₁) (h₂ : n ≠ n₂) :
    affineClassLift N a t n₁ n₂ μ m n = a n := by
  simp only [affineClassLift, ite_eq_right h₁, ite_eq_right h₂, add_zero]

theorem affineClassLift_sum (N : Finset ℤ) (a t : ℤ → ℝ) {n₁ n₂ : ℤ}
    (h₁ : n₁ ∈ N) (h₂ : n₂ ∈ N) (ht : t n₁ ≠ t n₂) (μ m : ℝ) :
    classSum N (affineClassLift N a t n₁ n₂ μ m) = μ := by
  classical
  unfold classSum affineClassLift
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left h₁, ite_eq_left h₂]
  have hs := lift_sum ht (μ - classSum N a) (m - classMoment N t a)
  simp only [classSum] at hs ⊢
  linarith

theorem affineClassLift_moment (N : Finset ℤ) (a t : ℤ → ℝ) {n₁ n₂ : ℤ}
    (h₁ : n₁ ∈ N) (h₂ : n₂ ∈ N) (ht : t n₁ ≠ t n₂) (μ m : ℝ) :
    classMoment N t (affineClassLift N a t n₁ n₂ μ m) = m := by
  classical
  unfold classMoment affineClassLift
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', ite_eq_left h₁, ite_eq_left h₂]
  have hs := lift_moment ht (μ - classSum N a) (m - classMoment N t a)
  simp only [classMoment] at hs ⊢
  linarith

theorem continuous_affineClassLift (N : Finset ℤ) (a t : ℤ → ℝ) (n₁ n₂ n : ℤ) :
    Continuous (fun p : ℝ × ℝ => affineClassLift N a t n₁ n₂ p.1 p.2 n) := by
  unfold affineClassLift liftFirst liftSecond
  split_ifs <;> fun_prop

theorem analyticAt_affineClassLift (N : Finset ℤ) (a t : ℤ → ℝ)
    (n₁ n₂ n : ℤ) (p : ℝ × ℝ) :
    AnalyticAt ℝ (fun z : ℝ × ℝ => affineClassLift N a t n₁ n₂ z.1 z.2 n) p := by
  have hf : AnalyticAt ℝ (fun z : ℝ × ℝ =>
      liftFirst (t n₁) (t n₂) (z.1 - classSum N a) (z.2 - classMoment N t a)) p := by
    exact ((analyticAt_snd.sub analyticAt_const).sub
      (analyticAt_const.mul (analyticAt_fst.sub analyticAt_const))).div_const
  have hs : AnalyticAt ℝ (fun z : ℝ × ℝ =>
      liftSecond (t n₁) (t n₂) (z.1 - classSum N a) (z.2 - classMoment N t a)) p := by
    exact ((analyticAt_const.mul (analyticAt_fst.sub analyticAt_const)).sub
      (analyticAt_snd.sub analyticAt_const)).div_const
  unfold affineClassLift
  split_ifs
  · exact (analyticAt_const.add hf).add hs
  · exact (analyticAt_const.add hf).add analyticAt_const
  · exact (analyticAt_const.add analyticAt_const).add hs
  · exact analyticAt_const

theorem affineClassLift_positive_near (N : Finset ℤ) (a t : ℤ → ℝ)
    (n₁ n₂ : ℤ) (ha : ∀ n ∈ N, 0 < a n) :
    ∀ᶠ p : ℝ × ℝ in nhds (classSum N a, classMoment N t a),
      ∀ n ∈ N, 0 < affineClassLift N a t n₁ n₂ p.1 p.2 n := by
  classical
  rw [Filter.eventually_all_finset]
  intro n hn
  apply (continuous_affineClassLift N a t n₁ n₂ n).continuousAt.eventually
  apply eventually_gt_nhds
  simpa only [affineClassLift_base] using ha n hn

end polyak.ModeLocking.Continuation
