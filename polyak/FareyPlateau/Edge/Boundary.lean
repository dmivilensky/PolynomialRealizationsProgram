import polyak.FareyPlateau.Edge.Singleton
import polyak.Farey.Tongue.Explicit
import polyak.ModeLocking.Plateaus.Source

/-! The single-harmonic boundary is the article's exact rational tongue
graph, independently of the regular certificate's chosen period. -/
noncomputable section
namespace polyak.FareyPlateau.Edge
open General Levels Set

theorem tongue_eq_of_phase (q : Tuning) {j k : ℕ} (_hk : 3 ≤ k)
    (hj : 1 ≤ j) (hjk : 2 * j < k)
    (hphase : q.angle (Regions.rationalAngle j k) = Real.pi / k) :
    Farey.rationalTongue (Global.Threshold.parameters q) j k = (q.kappa : EReal) := by
  let ω := Regions.rationalAngle j k
  let c := Real.cos ω
  let h := (Real.cos (Real.pi / k) / Real.sin (Real.pi / k)) * Real.sin ω
  let den := Farey.tongueDenominator q.y q.beta c h
  have hω := Regions.rationalAngle_mem hj hjk
  have hs := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hXi : q.Xi c = h := by
    have he := q.cot_angle hω
    rw [hphase] at he
    change _ = q.Xi c / Real.sin ω at he
    exact ((div_eq_iff hs.ne').mp he.symm)
  have hyβ : 0 < q.y * (1 - q.beta) := mul_pos q.y_pos (sub_pos.mpr q.beta_lt_one)
  have hκ : 0 < q.kappa - 1 := sub_pos.mpr q.kappa_gt_one
  have hN := kappaNumerator_pos q (c := c) ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hden : den = q.y * (1 - q.beta) * (Farey.XiInfinity q.y q.beta c - h) := by
    unfold den Farey.tongueDenominator Farey.XiInfinity
    conv_rhs => rw [mul_sub, mul_div_cancel₀ _ hyβ.ne']
    ring
  have hx := Farey.Xi_inverse_kappa q c
  rw [hXi] at hx
  have he : den * (q.kappa - 1) = kappaNumerator q.y q.beta c := by
    rw [hden, show Farey.XiInfinity q.y q.beta c - h =
      kappaNumerator q.y q.beta c / (q.y * (1 - q.beta) * (q.kappa - 1)) by linarith]
    calc
      _ = (q.y * (1 - q.beta) * (q.kappa - 1)) *
          (kappaNumerator q.y q.beta c / (q.y * (1 - q.beta) * (q.kappa - 1))) := by ring
      _ = _ := mul_div_cancel₀ _ (mul_ne_zero hyβ.ne' hκ.ne')
  have hd : 0 < den := by nlinarith
  change (if 0 < den then ((1 + kappaNumerator q.y q.beta c / den : ℝ) : EReal) else ⊤) = _
  rw [ite_eq_left hd]
  congr 1
  have hr : kappaNumerator q.y q.beta c / den = q.kappa - 1 :=
    (div_eq_iff hd.ne').mpr (by nlinarith only [he])
  linarith

theorem singleton_boundary_graph {q : Tuning} {L j k : ℕ}
    (D : ModeLocking.RegularData q 0 L) (hk : 3 ≤ k) (hj : 1 ≤ j) (hjk : 2 * j < k)
    (b : ℤ) (hb : (b * j) % k = 1)
    (hS : Set.range D.atoms = {atom j k (by omega) hjk.le}) :
    q.angle (Regions.rationalAngle j k) = Real.pi / k ∧
      Farey.rationalTongue (Global.Threshold.parameters q) j k = (q.kappa : EReal) := by
  have hp := singleton_phase_eq D hk hj hjk b hb hS
  rw [Geometry.shiftedCurve_zero] at hp
  change q.angle (Regions.rationalAngle j k) = _ at hp
  exact ⟨hp, tongue_eq_of_phase q hk hj hjk hp⟩

theorem singleton_kappaBoundary {q : Tuning} {L j k : ℕ}
    (D : ModeLocking.RegularData q 0 L) (hk : 3 ≤ k) (hj : 1 ≤ j) (hjk : 2 * j < k)
    (b : ℤ) (hb : (b * j) % k = 1)
    (hS : Set.range D.atoms = {atom j k (by omega) hjk.le}) :
    (Global.Threshold.kappaBoundary (Global.Threshold.parameters q) : EReal) =
      Farey.rationalTongue (Global.Threshold.parameters q) j k := by
  have he := (Global.Threshold.kappaBoundary_eq_iff
    (Global.Threshold.parameters q) (Global.Threshold.conditionNumber q)).mpr
    (by simpa only [Global.Threshold.fixedThreshold, Global.Threshold.tuning_parameters] using D.sigma_eq)
  rw [he, (singleton_boundary_graph D hk hj hjk b hb hS).2]
  rfl

theorem singleton_plateau_anchor {p r : ModeLocking.Plateaus.regularBoundary}
    (hr : r.val ∈ ModeLocking.Plateaus.plateau p.val) {K : ℕ}
    (hgap : Geometry.Gap K r.val.val) {ω : Frequency}
    (hS : ModeLocking.Plateaus.boundarySupport p = {ω})
    {w : MeasureTheory.Measure Frequency}
    (hw : ProgramSolution (tuningCurve r.val.val) nonzeroLags w) :
    ∀ x : Frequency, Farey.Anchor r.val.val w x ↔ x = ω := by
  apply ModeLocking.Plateaus.plateau_unique_anchor hr hgap _ hw
  intro x hx _
  rw [hS] at hx
  exact Set.mem_singleton_iff.mp hx

end polyak.FareyPlateau.Edge
