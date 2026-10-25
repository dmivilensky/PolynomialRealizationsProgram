import polyak.ModeLocking.Continuation.Moments
import polyak.ModeLocking.Continuation.ClassLift

/-! Positive analytic lifts of the continued class masses and slope
moments to the original signed-lag set. The zero class is kept fixed. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels Filter
open scoped BigOperators Topology
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

def classPair (r : Fin D.d) : {p : ℤ × ℤ // p.1 ∈ D.lags ∧ p.2 ∈ D.lags ∧
    p.1 ≠ p.2 ∧ p.1 % (L : ℤ) = D.reps r ∧ p.2 % (L : ℤ) = D.reps r} := by
  have h : ∃ p : ℤ × ℤ, p.1 ∈ D.lags ∧ p.2 ∈ D.lags ∧
      p.1 ≠ p.2 ∧ p.1 % (L : ℤ) = D.reps r ∧ p.2 % (L : ℤ) = D.reps r := by
    obtain ⟨n₁, h₁, n₂, h₂, hne, hr₁, hr₂⟩ := D.class_pair r
    exact ⟨(n₁, n₂), h₁, h₂, hne, hr₁, hr₂⟩
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

theorem classPair_quotient_ne (r : Fin D.d) :
    (((D.classPair r).val.1 / (L : ℤ) : ℤ) : ℝ) ≠
      (((D.classPair r).val.2 / (L : ℤ) : ℤ) : ℝ) := by
  intro he
  have hquot : (D.classPair r).val.1 / (L : ℤ) = (D.classPair r).val.2 / (L : ℤ) := by exact_mod_cast he
  have h₁ := Int.emod_add_ediv_mul (D.classPair r).val.1 (L : ℤ)
  have h₂ := Int.emod_add_ediv_mul (D.classPair r).val.2 (L : ℤ)
  rw [(D.classPair r).property.2.2.2.1] at h₁
  rw [(D.classPair r).property.2.2.2.2, ← hquot] at h₂
  exact (D.classPair r).property.2.2.1 (h₁.symm.trans h₂)

theorem classSum_lagClass (r : Fin D.d) :
    Continuation.classSum (D.lagClass r) D.dual = D.classWeight r := by
  classical
  simp only [Continuation.classSum, lagClass, Finset.sum_filter, classWeight]

theorem classMoment_lagClass (r : Fin D.d) :
    Continuation.classMoment (D.lagClass r) (fun n => ((n / (L : ℤ) : ℤ) : ℝ)) D.dual = D.slopeMoment r := by
  classical
  simp only [Continuation.classMoment, lagClass, Finset.sum_filter, slopeMoment]

def liftedWeights (μ m : Fin D.d → ℝ) (n : ℤ) : ℝ :=
  if h : ∃ r, n % (L : ℤ) = D.reps r then
    Continuation.affineClassLift (D.lagClass (Classical.choose h)) D.dual
      (fun n => ((n / (L : ℤ) : ℤ) : ℝ)) (D.classPair (Classical.choose h)).val.1
      (D.classPair (Classical.choose h)).val.2 (μ (Classical.choose h)) (m (Classical.choose h)) n
  else D.dual n

theorem liftedWeights_class (μ m : Fin D.d → ℝ) (r : Fin D.d) {n : ℤ}
    (hn : n % (L : ℤ) = D.reps r) : D.liftedWeights μ m n =
      Continuation.affineClassLift (D.lagClass r) D.dual (fun n => ((n / (L : ℤ) : ℤ) : ℝ))
        (D.classPair r).val.1 (D.classPair r).val.2 (μ r) (m r) n := by
  unfold liftedWeights
  split_ifs with hc
  · have hr : Classical.choose hc = r := D.reps_injective ((Classical.choose_spec hc).symm.trans hn)
    rw [hr]
  · exact (hc ⟨r, hn⟩).elim

theorem liftedWeights_zeroClass (μ m : Fin D.d → ℝ) {n : ℤ} (hn : n % (L : ℤ) = 0) :
    D.liftedWeights μ m n = D.dual n := by
  unfold liftedWeights
  apply dite_eq_right
  rintro ⟨r, hr⟩
  rw [hn] at hr
  exact (D.reps_pos r).ne hr

theorem liftedWeights_base (n : ℤ) : D.liftedWeights D.classWeight D.slopeMoment n = D.dual n := by
  unfold liftedWeights
  split_ifs with hc
  · rw [← D.classSum_lagClass, ← D.classMoment_lagClass, Continuation.affineClassLift_base]
  · rfl

theorem analyticAt_liftedWeights (μ m : Continuation.Parameters → (Fin D.d → ℝ))
    (hμ : AnalyticAt ℝ μ (Continuation.parameters q))
    (hm : AnalyticAt ℝ m (Continuation.parameters q)) (n : ℤ) :
    AnalyticAt ℝ (fun p => D.liftedWeights (μ p) (m p) n) (Continuation.parameters q) := by
  unfold liftedWeights
  split_ifs with hc
  · let r := Classical.choose hc
    have hμr : AnalyticAt ℝ (fun p => μ p r) (Continuation.parameters q) :=
      ((ContinuousLinearMap.proj (R := ℝ) r : (Fin D.d → ℝ) →L[ℝ] ℝ).analyticAt _).comp hμ
    have hmr : AnalyticAt ℝ (fun p => m p r) (Continuation.parameters q) :=
      ((ContinuousLinearMap.proj (R := ℝ) r : (Fin D.d → ℝ) →L[ℝ] ℝ).analyticAt _).comp hm
    exact (Continuation.analyticAt_affineClassLift (D.lagClass r) D.dual
      (fun n => ((n / (L : ℤ) : ℤ) : ℝ)) (D.classPair r).val.1 (D.classPair r).val.2 n _).comp
      (hμr.prod hmr)
  · exact analyticAt_const

theorem classPair_mem_first (r : Fin D.d) : (D.classPair r).val.1 ∈ D.lagClass r := by
  classical
  exact Finset.mem_filter.mpr ⟨(D.classPair r).property.1, (D.classPair r).property.2.2.2.1⟩

theorem classPair_mem_second (r : Fin D.d) : (D.classPair r).val.2 ∈ D.lagClass r := by
  classical
  exact Finset.mem_filter.mpr ⟨(D.classPair r).property.2.1, (D.classPair r).property.2.2.2.2⟩

theorem liftedWeights_classSum (μ m : Fin D.d → ℝ) (r : Fin D.d) :
    Continuation.classSum (D.lagClass r) (D.liftedWeights μ m) = μ r := by
  classical
  calc
    Continuation.classSum (D.lagClass r) (D.liftedWeights μ m) =
      Continuation.classSum (D.lagClass r)
        (Continuation.affineClassLift (D.lagClass r) D.dual
          (fun n => ((n / (L : ℤ) : ℤ) : ℝ)) (D.classPair r).val.1 (D.classPair r).val.2 (μ r) (m r)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact D.liftedWeights_class μ m r (Finset.mem_filter.mp hn).2
    _ = μ r := Continuation.affineClassLift_sum _ _ _ (D.classPair_mem_first r)
      (D.classPair_mem_second r) (D.classPair_quotient_ne r) _ _

theorem liftedWeights_classMoment (μ m : Fin D.d → ℝ) (r : Fin D.d) :
    Continuation.classMoment (D.lagClass r) (fun n => ((n / (L : ℤ) : ℤ) : ℝ))
      (D.liftedWeights μ m) = m r := by
  classical
  calc
    Continuation.classMoment (D.lagClass r) (fun n => ((n / (L : ℤ) : ℤ) : ℝ))
        (D.liftedWeights μ m) =
      Continuation.classMoment (D.lagClass r) (fun n => ((n / (L : ℤ) : ℤ) : ℝ))
        (Continuation.affineClassLift (D.lagClass r) D.dual
          (fun n => ((n / (L : ℤ) : ℤ) : ℝ)) (D.classPair r).val.1 (D.classPair r).val.2 (μ r) (m r)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [D.liftedWeights_class μ m r (Finset.mem_filter.mp hn).2]
    _ = m r := Continuation.affineClassLift_moment _ _ _ (D.classPair_mem_first r)
      (D.classPair_mem_second r) (D.classPair_quotient_ne r) _ _

theorem liftedWeights_sum (μ m : Fin D.d → ℝ)
    (hμ : (∑ r, μ r) = ∑ r, D.classWeight r) : (∑ n ∈ D.lags, D.liftedWeights μ m n) = 1 := by
  classical
  have hclasses (r : Fin D.d) :
      (∑ n ∈ D.lags, if n % (L : ℤ) = D.reps r then D.liftedWeights μ m n else 0) = μ r := by
    simpa only [Continuation.classSum, lagClass, Finset.sum_filter] using D.liftedWeights_classSum μ m r
  have hzero : (∑ n ∈ D.lags, if n % (L : ℤ) = 0 then D.liftedWeights μ m n else 0) =
      ∑ n ∈ D.lags, if n % (L : ℤ) = 0 then D.dual n else 0 := by
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n % (L : ℤ) = 0
    · rw [ite_eq_left hn, ite_eq_left hn, D.liftedWeights_zeroClass μ m hn]
    · rw [ite_eq_right hn, ite_eq_right hn]
  rw [D.sum_classes, hzero]
  simp_rw [hclasses]
  rw [hμ]
  have hold := D.sum_classes D.dual
  rw [D.dual_sum] at hold
  exact hold.symm

theorem liftedWeights_positive_near (μ m : Continuation.Parameters → (Fin D.d → ℝ))
    (hμ : AnalyticAt ℝ μ (Continuation.parameters q))
    (hm : AnalyticAt ℝ m (Continuation.parameters q))
    (hμbase : μ (Continuation.parameters q) = D.classWeight)
    (hmbase : m (Continuation.parameters q) = D.slopeMoment) :
    ∀ᶠ p in 𝓝 (Continuation.parameters q), ∀ n ∈ D.lags, 0 < D.liftedWeights (μ p) (m p) n := by
  classical
  rw [Filter.eventually_all_finset]
  intro n hn
  apply (D.analyticAt_liftedWeights μ m hμ hm n).continuousAt.eventually
  apply eventually_gt_nhds
  change 0 < D.liftedWeights (μ (Continuation.parameters q)) (m (Continuation.parameters q)) n
  rw [hμbase, hmbase, D.liftedWeights_base]
  exact D.dual_pos n hn

end polyak.ModeLocking.RegularData
