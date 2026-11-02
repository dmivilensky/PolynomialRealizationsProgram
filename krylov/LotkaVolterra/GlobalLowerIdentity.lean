import krylov.LotkaVolterra.GlobalGraphChord
import krylov.LotkaVolterra.GlobalSaddleContraction
import krylov.LotkaVolterra.GlobalExpandingUniqueness

/-!
Article: `main_krylov`, `apC:prop:LV`, canonical identification of the lower
graph with every actual bounded logistic shooting solution. This connects
the graph's crossing value to the independently constructed physical orbit.

Source: expansion on the positive half-line and global Lipschitz ODE
uniqueness, with no assumed uniqueness of the separating graph.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal

theorem lowerLogisticRate_eq_chord {γ q v : ℝ} (hγ₁ : γ < 1) (hq : q < 1)
    (hv : 1 - v ≠ 0) :
    logisticSlopeRate γ true q v = -(1 - q) * saddleSlopeRate γ (saddleU γ * q) v := by
  have hB := saddleU_pos hγ₁
  have hU : 0 < saddleU γ * (1 - q) := mul_pos hB (sub_pos.mpr hq)
  have hh := lowerLogisticRate_eq (ne_of_gt hB) (ne_of_gt hU) hv
  have hq' : (saddleU γ - saddleU γ * (1 - q)) / saddleU γ = q := by
    field_simp
    ring
  have hz : saddleU γ - saddleU γ * (1 - q) = saddleU γ * q := by ring
  have hfac : saddleU γ * (1 - q) / saddleU γ = 1 - q := by field_simp
  rw [hq'] at hh
  simpa only [hz, hfac] using hh

theorem logisticParameter_le_half {t : ℝ} (ht : 0 ≤ t) : logisticParameter t ≤ 1 / 2 := by
  have hE : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  unfold logisticParameter
  apply (div_le_iff₀ (by linarith [Real.exp_pos t] : 0 < 1 + Real.exp t)).mpr
  linarith

theorem lowerLogisticRate_expansion {γ t x y : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (ht : 0 ≤ t) (hx : x ∈ Icc 0 γ) (hy : y ∈ Icc 0 γ) :
    (1 / 6 : ℝ) * (x - y) ^ 2 ≤ (x - y) *
      (logisticSlopeRate γ true (logisticParameter t) x -
        logisticSlopeRate γ true (logisticParameter t) y) := by
  let q := logisticParameter t
  have hq := logisticParameter_mem t
  have hqhalf := logisticParameter_le_half ht
  have hB := saddleU_pos hγ₁
  have hz : saddleU γ * q ∈ Icc (-(saddleU γ / 2)) (saddleU γ / 2) := by
    have hqp := mul_pos hB hq.1
    have hqu := mul_le_mul_of_nonneg_left hqhalf hB.le
    constructor <;> dsimp [q] at * <;> linarith
  have hh := saddleSlopeRate_expansion hγ hγ₁ hz hx hy
  have hx₁ : 1 - x ≠ 0 := by linarith [hx.2]
  have hy₁ : 1 - y ≠ 0 := by linarith [hy.2]
  calc
    (1 / 6 : ℝ) * (x - y) ^ 2 ≤ (1 - q) * ((x - y) ^ 2 / 3) := by
      have hm := mul_nonneg (sq_nonneg (x - y)) (show 0 ≤ 1 / 2 - q by dsimp [q]; linarith)
      nlinarith
    _ ≤ (1 - q) * ((x - y) * (-saddleSlopeRate γ (saddleU γ * q) x +
        saddleSlopeRate γ (saddleU γ * q) y)) :=
      mul_le_mul_of_nonneg_left hh (sub_pos.mpr hq.2).le
    _ = _ := by rw [lowerLogisticRate_eq_chord hγ₁ hq.2 hx₁,
      lowerLogisticRate_eq_chord hγ₁ hq.2 hy₁]; ring

namespace SubcriticalGraph
variable {γ : ℝ} (G : SubcriticalGraph γ)

def lowerLogisticSlope (t : ℝ) : ℝ := G.rawChord (2 * logisticParameter t)

theorem lowerLogisticSlope_bounds (hγ₁ : γ < 1) (t : ℝ) : G.lowerLogisticSlope t ∈ Ioo 0 γ := by
  have hq := logisticParameter_mem t
  exact G.rawChord_bounds_of_lt_two hγ₁ (by linarith [hq.2])
    (ne_of_gt (by linarith [hq.1]))

theorem lowerLogisticSlope_hasDerivAt (hγ₁ : γ < 1) (t : ℝ) :
    HasDerivAt G.lowerLogisticSlope
      (logisticSlopeRate γ true (logisticParameter t) (G.lowerLogisticSlope t)) t := by
  have hq := logisticParameter_mem t
  have hu₀ : 2 * logisticParameter t ≠ 0 := ne_of_gt (by linarith [hq.1])
  have hv := G.lowerLogisticSlope_bounds hγ₁ t
  have hh := (G.rawChord_hasDerivAt_of_lt_two hγ₁ (by linarith [hq.2]) hu₀).comp t
    ((logisticParameter_hasDerivAt t).const_mul 2)
  have harg : (saddleU γ / 2) * (2 * logisticParameter t) = saddleU γ * logisticParameter t := by ring
  rw [harg] at hh
  have hid : saddleSlopeRate γ (saddleU γ * logisticParameter t) (G.lowerLogisticSlope t) /
      (2 * logisticParameter t) * (2 * (-logisticParameter t * (1 - logisticParameter t))) =
      -(1 - logisticParameter t) * saddleSlopeRate γ (saddleU γ * logisticParameter t) (G.lowerLogisticSlope t) := by
    field_simp [ne_of_gt hq.1]
  change HasDerivAt G.lowerLogisticSlope
    (saddleSlopeRate γ (saddleU γ * logisticParameter t) (G.lowerLogisticSlope t) /
      (2 * logisticParameter t) * (2 * (-logisticParameter t * (1 - logisticParameter t)))) t at hh
  rw [hid, ← lowerLogisticRate_eq_chord hγ₁ hq.2 (by linarith [hv.2])] at hh
  exact hh

theorem lowerLogisticSlope_eq (hγ : 0 < γ) (hγ₁ : γ < 1) {v : ℝ → ℝ}
    (hv : ∀ t, v t ∈ Icc 0 γ ∧ HasDerivAt v
      (logisticSlopeRate γ true (logisticParameter t) (v t)) t) : G.lowerLogisticSlope = v := by
  have hG (t : ℝ) : G.lowerLogisticSlope t ∈ Icc 0 γ ∧ HasDerivAt G.lowerLogisticSlope
      (logisticSlopeRate γ true (logisticParameter t) (G.lowerLogisticSlope t)) t :=
    ⟨⟨(G.lowerLogisticSlope_bounds hγ₁ t).1.le, (G.lowerLogisticSlope_bounds hγ₁ t).2.le⟩,
      G.lowerLogisticSlope_hasDerivAt hγ₁ t⟩
  have hsame : EqOn G.lowerLogisticSlope v (Ici 0) :=
    bounded_expanding_solution_unique (F := fun t x ↦ logisticSlopeRate γ true (logisticParameter t) x)
    (by norm_num : (0 : ℝ) < 1 / 6)
    (fun t ht x hx y hy ↦ lowerLogisticRate_expansion hγ hγ₁ ht hx hy)
    (fun t _ ↦ hG t) (fun t _ ↦ hv t)
  obtain ⟨_, K, _, hLip⟩ := clippedLogisticSlopeRate_bounds hγ hγ₁ true
  apply ODE_solution_unique_univ (v := clippedLogisticSlopeRate γ true)
    (s := fun _ ↦ univ) (K := K) (t₀ := 0)
    (fun t ↦ (hLip t).lipschitzOnWith)
    (fun t ↦ ⟨?_, mem_univ _⟩) (fun t ↦ ⟨?_, mem_univ _⟩) (hsame (by norm_num))
  · simpa only [clippedLogisticSlopeRate, saddleSlopeClip_eq (hG t).1] using (hG t).2
  · simpa only [clippedLogisticSlopeRate, saddleSlopeClip_eq (hv t).1] using (hv t).2

theorem graph_eq_lower_logistic (hγ : 0 < γ) (hγ₁ : γ < 1) {v : ℝ → ℝ}
    (hv : ∀ t, v t ∈ Icc 0 γ ∧ HasDerivAt v
      (logisticSlopeRate γ true (logisticParameter t) (v t)) t)
    {U : ℝ} (hU : U ∈ Ioo (0 : ℝ) (saddleU γ)) :
    G.σ U = saddleS γ - v (lowerGraphTime γ U) * (saddleU γ - U) := by
  have hh := congrFun (G.lowerLogisticSlope_eq hγ hγ₁ hv) (lowerGraphTime γ U)
  have hden : (saddleU γ / 2) * (2 * logisticParameter (lowerGraphTime γ U)) = saddleU γ - U := by
    rw [lowerGraphTime_parameter hγ₁ hU]
    field_simp [ne_of_gt (saddleU_pos hγ₁)]
  have hback : saddleU γ - (saddleU γ / 2) * (2 * logisticParameter (lowerGraphTime γ U)) = U := by
    rw [hden]
    ring
  change (saddleS γ - G.σ (saddleU γ - (saddleU γ / 2) *
    (2 * logisticParameter (lowerGraphTime γ U)))) /
      ((saddleU γ / 2) * (2 * logisticParameter (lowerGraphTime γ U))) = v (lowerGraphTime γ U) at hh
  rw [hback, hden] at hh
  have hm := (div_eq_iff (ne_of_gt (sub_pos.mpr hU.2))).mp hh
  linarith

theorem unique_lower_graph (hγ : 0 < γ) (hγ₁ : γ < 1) (G' : SubcriticalGraph γ) :
    EqOn G.σ G'.σ (Ioo (0 : ℝ) (saddleU γ)) := by
  obtain ⟨v, hv⟩ := exists_whole_logistic_slope hγ hγ₁ true
  have hv' (t : ℝ) : v t ∈ Icc 0 γ ∧ HasDerivAt v
      (logisticSlopeRate γ true (logisticParameter t) (v t)) t :=
    ⟨⟨(hv t).1.1.le, (hv t).1.2.le⟩, (hv t).2⟩
  intro U hU
  rw [G.graph_eq_lower_logistic hγ hγ₁ hv' hU, G'.graph_eq_lower_logistic hγ hγ₁ hv' hU]

end SubcriticalGraph
end
end krylov.LotkaVolterra
