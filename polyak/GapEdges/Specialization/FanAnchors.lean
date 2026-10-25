import polyak.GapEdges.Specialization.Opening
import polyak.GapEdges.Junction.AdjacentCoordinates
import polyak.FareyPlateau.FanAnalysis.ActualJets
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! At the quadratic fan shifts, exactly the atom on the opening side
belongs to the closed dip. This follows from the actual first phase jet. -/
noncomputable section
namespace polyak.GapEdges
open General Levels ModeLocking Set Filter
open scoped Topology

theorem eventually_same_sign_as_derivative {f : ℝ→ℝ} {d : ℝ}
    (hf : HasDerivAt f d 0) (hzero : f 0=0) (hd : d≠0) :
    ∀ᶠ δ : ℝ in 𝓝[≠] 0,(f δ≤0 ↔ d*δ<0) ∧ (f δ<0 ↔ d*δ<0) := by
  have hlim : Tendsto (fun δ=>f δ/δ) (𝓝[≠] 0) (𝓝 d) := by
    simpa only [zero_add,hzero,sub_zero,smul_eq_mul,←div_eq_inv_mul] using hf.tendsto_slope_zero
  have hr : Tendsto (fun δ=>f δ/(d*δ)) (𝓝[≠] 0) (𝓝 1) := by
    convert hlim.div_const d using 1
    · funext δ
      ring
    · rw [div_self hd]
  filter_upwards [hr.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1))] with δ hδ
  rcases div_pos_iff.mp hδ with ⟨hfpos,hprodpos⟩|⟨hfneg,hprodneg⟩
  · exact ⟨by constructor <;> intro h <;> linarith,by constructor <;> intro h <;> linarith⟩
  · exact ⟨iff_of_true hfneg.le hprodneg,iff_of_true hfneg hprodneg⟩

theorem adjacent_first_chi {q : Tuning} {k : ℕ}
    (A : FareyPlateau.Edge.AdjacentData q 1 k) :
    FareyPlateau.FanAnalysis.Actual.first A-1/2=firstChi q k := by
  rw [FareyPlateau.FanAnalysis.Actual.first_actual]
  unfold firstChi firstEdgePhase FareyPlateau.Edge.AdjacentData.edgeShift
  rw [Junction.adjacent_frequency_one A]

theorem fan_opening_signs {q : Tuning} {k : ℕ}
    (A : FareyPlateau.Edge.AdjacentData q 1 k) (e : ℝ) (hχ : firstChi q k≠0) :
    ∀ᶠ δ : ℝ in 𝓝[≠] 0,
      (FareyPlateau.FanAnalysis.Actual.nearAngle A e δ≤
        ((A.frequency:ℝ)+δ)/2 ↔ firstChi q k*δ<0) ∧
      (FareyPlateau.FanAnalysis.Actual.farAngle A e δ≤
        ((A.frequency:ℝ)-((k:ℝ)-1)*δ)/2 ↔ 0<firstChi q k*δ) := by
  let f := fun δ=>FareyPlateau.FanAnalysis.Actual.nearAngle A e δ-((A.frequency:ℝ)+δ)/2
  let g := fun δ=>FareyPlateau.FanAnalysis.Actual.farAngle A e δ-
    ((A.frequency:ℝ)-((k:ℝ)-1)*δ)/2
  have hf : HasDerivAt f (firstChi q k) 0 := by
    have hh := (FareyPlateau.FanAnalysis.Actual.near_analytic A e).differentiableAt.hasDerivAt
    rw [FareyPlateau.FanAnalysis.Actual.near_first] at hh
    convert hh.sub (((hasDerivAt_id (0:ℝ)).const_add (A.frequency:ℝ)).div_const 2) using 1
    · rfl
    · simpa only [id_eq] using (adjacent_first_chi A).symm
  have hg : HasDerivAt g (-((k:ℝ)-1)*firstChi q k) 0 := by
    have hh := (FareyPlateau.FanAnalysis.Actual.far_analytic A e).differentiableAt.hasDerivAt
    rw [FareyPlateau.FanAnalysis.Actual.far_first] at hh
    convert hh.sub ((((hasDerivAt_id (0:ℝ)).const_mul ((k:ℝ)-1)).const_sub (A.frequency:ℝ)).div_const 2) using 1
    · rfl
    · rw [←adjacent_first_chi A]
      ring
  have hfzero : f 0=0 := by
    dsimp [f]
    rw [FareyPlateau.FanAnalysis.Actual.near_value,Junction.adjacent_frequency_one A]
    ring
  have hgzero : g 0=0 := by
    dsimp [g]
    rw [FareyPlateau.FanAnalysis.Actual.far_value,Junction.adjacent_frequency_one A]
    ring
  have hk : 0<(k:ℝ)-1 := by
    have hh : (3:ℝ)≤k := by exact_mod_cast A.period_ge
    linarith
  filter_upwards [eventually_same_sign_as_derivative hf hfzero hχ,
    eventually_same_sign_as_derivative hg hgzero (mul_ne_zero (neg_ne_zero.mpr hk.ne') hχ)]
    with δ hnear hfar
  refine ⟨?_,?_⟩
  · simpa only [f,sub_nonpos] using hnear.1
  · have he : (-((k:ℝ)-1)*firstChi q k)*δ<0 ↔ 0<firstChi q k*δ := by
      rw [mul_assoc,mul_neg_iff]
      simp only [neg_lt_zero,hk,not_lt_of_ge (neg_nonpos.mpr hk.le),false_and,
        true_and,false_or]
    simpa only [g,sub_nonpos,he] using hfar.1

theorem fan_closedDip_side {q : Tuning} {k : ℕ}
    (A : FareyPlateau.Edge.AdjacentData q 1 k) (e : ℝ) (hχ : firstChi q k≠0) :
    ∀ᶠ δ : ℝ in 𝓝[≠] 0,∀a c : Frequency,
      (a:ℝ)=(A.frequency:ℝ)+δ →
      (c:ℝ)=(A.frequency:ℝ)-((k:ℝ)-1)*δ →
      (a∈Geometry.closedDip (Geometry.shiftedCurve q (A.edgeShift-e*δ^2)) ↔ firstChi q k*δ<0) ∧
      (c∈Geometry.closedDip (Geometry.shiftedCurve q (A.edgeShift-e*δ^2)) ↔ 0<firstChi q k*δ) := by
  have ha := FareyPlateau.FanAnalysis.anglePath_actual q A.edgeShift A.frequency 1 e
    (FareyPlateau.FanAnalysis.Actual.frequency_interior A)
  have hc := FareyPlateau.FanAnalysis.anglePath_actual q A.edgeShift A.frequency (-((k:ℝ)-1)) e
    (FareyPlateau.FanAnalysis.Actual.frequency_interior A)
  filter_upwards [fan_opening_signs A e hχ,ha.filter_mono nhdsWithin_le_nhds,
    hc.filter_mono nhdsWithin_le_nhds] with δ hsign hnear hfar a c h a₁
  have hnear' : FareyPlateau.FanAnalysis.Actual.nearAngle A e δ=
      Geometry.shiftedAngle q (A.edgeShift-e*δ^2) a := by
    rw [h]
    simpa only [FareyPlateau.FanAnalysis.Actual.nearAngle,one_mul] using hnear
  have hfar' : FareyPlateau.FanAnalysis.Actual.farAngle A e δ=
      Geometry.shiftedAngle q (A.edgeShift-e*δ^2) c := by
    rw [a₁]
    simpa only [FareyPlateau.FanAnalysis.Actual.farAngle,neg_mul,sub_eq_add_neg] using hfar
  change (Geometry.shiftedAngle q (A.edgeShift-e*δ^2) a≤(a:ℝ)/2 ↔ _) ∧
    (Geometry.shiftedAngle q (A.edgeShift-e*δ^2) c≤(c:ℝ)/2 ↔ _)
  rw [←hnear',←hfar',h,a₁]
  exact hsign

end polyak.GapEdges
