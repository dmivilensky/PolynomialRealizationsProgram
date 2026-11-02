import krylov.LotkaVolterra.AnalyticSaddleDerivative
import krylov.LotkaVolterra.GlobalSaddleWeighted
import krylov.LotkaVolterra.GlobalSaddleChord

/-!
Article: main_krylov, apC:prop:LV, analytic stable graph through the saddle.
Use: apply the analytic Banach implicit theorem to the actual weighted chord
identity. The bounded shooting chord is thereby analytic at its singular point;
analyticity is not a premise of the orbit construction.
Source: the classical Briot--Bouquet integral proof, using actual bounded path
integration and mathlib's analytic inverse theorem.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set Filter MeasureTheory
open krylov.AnalyticTools
open scoped Topology

/-- Every actual continuous saddle chord satisfying the concrete differential
equation is analytic at zero. -/
theorem analyticAt_actual_saddle_chord {γ r : ℝ} {w : ℝ → ℝ}
    (hγ : 0 < γ) (hγ₁ : γ < 1) (hr : r ∈ Ioo 0 γ)
    (hroot : saddleSlopeRate γ 0 r = 0) (hw₀ : w 0 = r)
    (hw : ContinuousOn w (Icc (-1 : ℝ) 1))
    (hstrip : ∀ u ∈ Icc (-1 : ℝ) 1, w u ∈ Icc 0 γ)
    (hd : ∀ u ∈ Icc (-1 : ℝ) 1, u ≠ 0 →
      HasDerivAt w (saddleSlopeRate γ ((saddleU γ / 2) * u) (w u) / u) u) :
    AnalyticAt ℝ w 0 := by
  let c := saddleU γ / 2
  let a := -saddleSlopeDerivative γ 0 r
  have hc : 0 < c := half_pos (saddleU_pos hγ₁)
  have hr₁ : r < 1 := hr.2.trans hγ₁
  have ha : 0 < a := by
    have hder := saddleSlopeDerivative_le_neg_third hγ hγ₁
      (z := 0) ⟨neg_nonpos.mpr hc.le, hc.le⟩ ⟨hr.1.le, hr.2.le⟩
    dsimp [a]
    linarith
  let we : ℝ → ℝ := fun z ↦ w (projIcc (-1) 1 (by norm_num) z)
  have hwe : Continuous we := hw.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun z ↦ (projIcc (-1) 1 _ z).2)
  have hext {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) : we z = w z := by
    dsimp [we]
    rw [projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) hz]
  let q : ℝ → SaddlePaths := fun z ↦
    ⟨fun u ↦ we (z * (u : ℝ)) - r, (hwe.comp (by fun_prop)).sub continuous_const⟩
  have hq : Continuous q := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (hwe.comp (by fun_prop)).sub continuous_const
  have hq₀ : q 0 = 0 := by
    ext u
    simp [q, hext (by norm_num : (0 : ℝ) ∈ Icc (-1) 1), hw₀]
  let N := saddleNonlinearLift γ c r a
  let L : SaddlePaths →L[ℝ] SaddlePaths := weightedDilationCLM a ha
  obtain ⟨A, hA⟩ := saddleNonlinearLift_hasFDerivAt (c := c) hγ₁ hr₁
  obtain ⟨v, hv, _, _, huniq⟩ := exists_analytic_operator_fixedPoint L N
    (analyticAt_saddleNonlinearLift hγ₁ hr₁) (saddleNonlinearLift_zero hγ₁ hr₁ hroot) A hA
  have hmul {z : ℝ} (hz : |z| ≤ 1) (u : SymmetricPathDomain) :
      z * (u : ℝ) ∈ Icc (-1 : ℝ) 1 := by
    apply abs_le.mp
    rw [abs_mul]
    exact (mul_le_mul hz (abs_le.mpr u.2) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hunits {z : ℝ} (hz : |z| ≤ 1) :
      IsUnit (ContinuousMap.const SymmetricPathDomain (saddleU γ) - saddleLiftZ c (z, q z)) ∧
      IsUnit (1 - saddleLiftV r (z, q z)) := by
    constructor
    · apply ContinuousMap.isUnit_iff_forall_ne_zero _ |>.mpr
      intro u
      have hz' := hmul hz u
      have hlo := mul_le_mul_of_nonneg_left hz'.2 hc.le
      change saddleU γ - c * z * (u : ℝ) ≠ 0
      dsimp [c] at hlo ⊢
      nlinarith [saddleU_pos hγ₁]
    · apply ContinuousMap.isUnit_iff_forall_ne_zero _ |>.mpr
      intro u
      have he := hext (hmul hz u)
      have hs := (hstrip _ (hmul hz u)).2
      change 1 - (r + (we (z * (u : ℝ)) - r)) ≠ 0
      rw [he]
      linarith
  have hfix {z : ℝ} (hz : |z| ≤ 1) : q z = L (N (z, q z)) := by
    ext u
    have hactual := actual_saddle_chord_weighted_identity hγ₁ ha hw₀ hroot hw hstrip hd
      (z := z * u) (abs_le.mpr (hmul hz u))
    calc
      q z u = w (z * u) - r := by change we (z * u) - r = _; rw [hext (hmul hz u)]
      _ = _ := hactual
      _ = L (N (z, q z)) u := by
        rw [weightedDilationCLM_apply]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        rw [saddleNonlinearLift_apply (hunits hz).1 (hunits hz).2]
        have hdil : (unitDilation u t : ℝ) = (u : ℝ) * t := by
          simp only [unitDilation, projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1)
            (show t ∈ Icc 0 1 from ⟨ht.1.le, ht.2⟩)]
        have he := hext (hmul hz (unitDilation u t))
        change _ = t ^ (a - 1) *
          (saddleSlopeRate γ (c * z * ↑(unitDilation u t))
            (r + (we (z * ↑(unitDilation u t)) - r)) + a * (we (z * ↑(unitDilation u t)) - r))
        rw [he, hdil]
        simp only [add_sub_cancel, mul_assoc, c]
  have ht : Tendsto (fun z : ℝ ↦ (z, q z)) (𝓝 0) (𝓝 ((0 : ℝ), (0 : SaddlePaths))) := by
    have hh := (continuous_id.prodMk hq).continuousAt (x := (0 : ℝ))
    change Tendsto (fun z : ℝ ↦ (z, q z)) (𝓝 0) (𝓝 ((0 : ℝ), q 0)) at hh
    rwa [hq₀] at hh
  let ev : SaddlePaths →L[ℝ] ℝ :=
    ContinuousMap.evalCLM (R := ℝ) (⟨1, by norm_num⟩ : SymmetricPathDomain)
  have hav : AnalyticAt ℝ (fun z ↦ r + ev (v z)) 0 :=
    analyticAt_const.add ((ev.analyticAt _).comp hv)
  apply hav.congr
  filter_upwards [ht.eventually huniq, Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1)] with z hu hz
  have hz' : |z| ≤ 1 := abs_le.mpr ⟨hz.1.le, hz.2.le⟩
  have heq := congrArg ev (hu (hfix hz'))
  change we (z * 1) - r = ev (v z) at heq
  rw [mul_one, hext ⟨hz.1.le, hz.2.le⟩] at heq
  linarith

/-- An actual analytic stable chord exists through every subcritical saddle.
The chord is first constructed by bounded shooting; the preceding theorem
then proves its analyticity at the singular point. -/
theorem exists_analytic_saddle_chord {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) :
    ∃ r : ℝ, ∃ w : ℝ → ℝ,
      r ∈ Ioo 0 γ ∧ saddleSlopeRate γ 0 r = 0 ∧ w 0 = r ∧
      AnalyticAt ℝ w 0 ∧ ContinuousOn w (Icc (-1 : ℝ) 1) ∧
      ∀ u ∈ Icc (-1 : ℝ) 1, w u ∈ Ioo 0 γ ∧
        (u ≠ 0 → HasDerivAt w (saddleSlopeRate γ ((saddleU γ / 2) * u) (w u) / u) u) := by
  obtain ⟨r, w, hr, hroot, hw₀, _, hw, hder⟩ := exists_continuous_saddle_chord hγ hγ₁
  refine ⟨r, w, hr, hroot, hw₀, ?_, hw, hder⟩
  exact analyticAt_actual_saddle_chord hγ hγ₁ hr hroot hw₀ hw
    (fun u hu ↦ ⟨(hder u hu).1.1.le, (hder u hu).1.2.le⟩)
    (fun u hu ↦ (hder u hu).2)

end
end krylov.LotkaVolterra
