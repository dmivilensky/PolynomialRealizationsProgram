import polyak.FareyPlateau.Domain.Gap
import polyak.FareyPlateau.Domain.RedundantFace

/-! Source-specialized edge-domain theorem, for every fraction in every
gap.  Coprimality is not needed for this geometric coordinate result. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels Set

def aE (K j k : ℕ) (D : ℝ) : ℝ :=
  edgeBound (Chart.rationalCosine j k) (Chart.rationalHeight j k)
    (Chart.boundaryCosine K) (Chart.boundaryCosine (K+1)) D

theorem rationalCosine_mem {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) : Chart.rationalCosine j k∈Ioo (-1:ℝ) 1 := by
  obtain ⟨hl,hr⟩ := Chart.fraction_cosine_window hK hf
  exact ⟨(Chart.boundaryCosine_ge_neg_one K).trans_lt hl,
    hr.trans (Chart.boundaryCosine_succ_lt_one hK)⟩

theorem rationalHeight_above {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) :
    1+Chart.rationalCosine j k<Chart.rationalHeight j k := by
  obtain ⟨hj,hjk⟩ := Chart.fraction_window_arithmetic hK hf
  exact Chart.rationalHeight_gt_baseline hj hjk

theorem aE_pos {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (D : ℝ) : 0<aE K j k D :=
  edgeBound_pos (rationalHeight_above hK hf)
    (Chart.fraction_cosine_window hK hf).1 (Chart.fraction_cosine_window hK hf).2

@[fun_prop] theorem continuous_aE (K j k : ℕ) : Continuous (aE K j k) :=
  continuous_edgeBound _ _ _ _

theorem convexOn_aE (K j k : ℕ) : ConvexOn ℝ univ (aE K j k) :=
  convexOn_edgeBound _ _ _ _

theorem aE_three_faces {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (D : ℝ) :
    aE K j k D=max (edgeFace (Chart.rationalCosine j k) (Chart.rationalHeight j k) 1 D)
      (max (gapFace (Chart.rationalCosine j k) (Chart.rationalHeight j k)
        (Chart.boundaryCosine K) D)
        (gapFace (Chart.rationalCosine j k) (Chart.rationalHeight j k)
        (Chart.boundaryCosine (K+1)) D)) :=
  edgeBound_three_faces (rationalCosine_mem hK hf).1 (rationalHeight_above hK hf)
    (Chart.boundaryCosine_ge_neg_one K) (Chart.fraction_cosine_window hK hf).1
    (Chart.fraction_cosine_window hK hf).2

theorem source_edgedomain (q : Tuning) {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) {a D : ℝ}
    (he : Chart.coefficients q=edgeCoefficients (Chart.rationalCosine j k)
      (Chart.rationalHeight j k) a D) : Geometry.Gap K q ↔ aE K j k D<a :=
  edge_gap_iff q hK (rationalCosine_mem hK hf) (rationalHeight_above hK hf)
    (Chart.fraction_cosine_window hK hf).1 (Chart.fraction_cosine_window hK hf).2 he

theorem source_edge_exists_unique {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) {a D : ℝ} (ha : aE K j k D<a) :
    ∃! q : Tuning, Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D := by
  let q := edgeTuning (rationalCosine_mem hK hf) (rationalHeight_above hK hf)
    (Chart.fraction_cosine_window hK hf).1 (Chart.fraction_cosine_window hK hf).2 ha
  refine ⟨q,coefficients_edgeTuning _ _ _ _ ha,?_⟩
  intro p hp
  exact edgeTuning_unique p _ _ _ _ ha hp

end polyak.FareyPlateau
