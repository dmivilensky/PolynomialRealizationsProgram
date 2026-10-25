import polyak.FareyPlateau.Edge.Jets
import polyak.ModeLocking.TwoLag.Extension
import polyak.GapEdges.Specialization.FirstTongue

/-! The two-lag j=1 formula on either side of slope one. It is the
positive edge symbol in the strip 0 < |chi| < k/2; outside that strip the
definition is only an algebraic extension. -/
noncomputable section
namespace polyak.GapEdges
open General Levels ModeLocking Set

def firstEdgePhase (q : Tuning) (k : ℕ) : ℝ → ℝ :=
  TwoLag.phase q (FareyPlateau.Edge.shift q k (2 * Real.pi / k))

def firstChi (q : Tuning) (k : ℕ) : ℝ :=
  deriv (firstEdgePhase q k) (2 * Real.pi / k) - 1 / 2

def firstEdgeSymbol (q : Tuning) (k : ℕ) : ℝ → ℝ :=
  if 0 ≤ firstChi q k then
    FareyPlateau.Edge.symbol (firstEdgePhase q k) 1 (1 + (k : ℤ)) (2 * firstChi q k / k)
  else
    FareyPlateau.Edge.symbol (firstEdgePhase q k) (1 - (k : ℤ)) 1 (1 + 2 * firstChi q k / k)

theorem first_edge_weights_positive {k : ℕ} (hk : 3 ≤ k) {χ : ℝ}
    (hχ : 0 < |χ|) (hbound : |χ| < (k : ℝ) / 2) :
    0 < 1 - 2 * |χ| / k ∧ 0 < 2 * |χ| / k ∧
      (1 - 2 * |χ| / k) + 2 * |χ| / k = 1 := by
  have hkp : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hratio : 2 * |χ| / (k : ℝ) < 1 := (div_lt_one hkp).mpr (by linarith)
  exact ⟨sub_pos.mpr hratio, div_pos (by positivity) hkp, by ring⟩

theorem firstEdgePhase_at (q : Tuning) {k : ℕ} (hk : 3 ≤ k) :
    firstEdgePhase q k (2 * Real.pi / k) = Real.pi / k := by
  have hω := Chart.boundaryAngle_strict_mem hk
  change 2 * Real.pi / (k : ℝ) ∈ Ioo 0 Real.pi at hω
  unfold firstEdgePhase TwoLag.phase
  rw [Geometry.jointAngle_actual q _ ⟨hω.1.le, hω.2.le⟩]
  exact FareyPlateau.Edge.phase_at_shift q hk hω

theorem firstEdgePhase_analytic (q : Tuning) {k : ℕ} (hk : 3 ≤ k) :
    AnalyticAt ℝ (firstEdgePhase q k) (2 * Real.pi / k) :=
  TwoLag.analyticAt_phase q _
    ⟨(Chart.boundaryAngle_strict_mem hk).1.le, (Chart.boundaryAngle_strict_mem hk).2.le⟩

theorem firstEdgePhase_trig (q : Tuning) {k : ℕ} (hk : 3 ≤ k) {n : ℤ}
    (hn : n % (k : ℤ) = 1) :
    Real.sin ((n : ℝ) * (2 * Real.pi / k) - firstEdgePhase q k (2 * Real.pi / k)) =
        Real.sin (Real.pi / k) ∧
      Real.cos ((n : ℝ) * (2 * Real.pi / k) - firstEdgePhase q k (2 * Real.pi / k)) =
        Real.cos (Real.pi / k) := by
  have hh := FareyPlateau.Edge.lag_trig_reduce (j := 1) (k := k)
    (by omega) (by omega) n (firstEdgePhase q k (2 * Real.pi / k))
  simp only [Nat.cast_one, mul_one, hn, Int.cast_one, firstEdgePhase_at q hk] at hh
  have he : 2 * Real.pi / (k : ℝ) - Real.pi / k = Real.pi / k := by ring
  rw [he] at hh
  rw [firstEdgePhase_at q hk]
  simpa [FareyPlateau.Edge.atom, Farey.gridFrequency] using And.intro hh.2 hh.1

theorem first_edge_curvature (q : Tuning) {k : ℕ} (hk : 3 ≤ k) :
    deriv^[2] (firstEdgeSymbol q k) (2 * Real.pi / k) =
      Real.sin (Real.pi / k) * deriv^[2] (firstEdgePhase q k) (2 * Real.pi / k) -
        ((k : ℝ) - 2 * |firstChi q k|) * |firstChi q k| * Real.cos (Real.pi / k) := by
  have hkp : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have ho : (1 : ℤ) % (k : ℤ) = 1 := Int.emod_eq_of_lt (by norm_num) (by omega)
  have hp : (1 + (k : ℤ)) % (k : ℤ) = 1 := by
    simp only [Int.add_emod, Int.emod_self, add_zero, ho]
  have hm : (1 - (k : ℤ)) % (k : ℤ) = 1 := by
    simp only [Int.sub_emod, Int.emod_self, sub_zero, ho]
  have hθ := firstEdgePhase_analytic q hk
  have hc := firstEdgePhase_at q hk
  unfold firstEdgeSymbol
  split_ifs with hsign
  · rw [abs_of_nonneg hsign]
    have hn : ((1 + (k : ℤ) : ℤ) : ℝ) = (1 : ℤ) + (k : ℝ) := by push_cast; rfl
    have hmean : 2 * deriv (firstEdgePhase q k) (2 * Real.pi / k) =
        (1 : ℤ) + (2 * firstChi q k / k) * (k : ℝ) := by
      unfold firstChi
      field_simp
      ring
    rw [FareyPlateau.Edge.symbol_second hθ hc hn hmean
      (fun n hn => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with rfl | rfl
        · exact (firstEdgePhase_trig q hk ho).1
        · exact (firstEdgePhase_trig q hk hp).1)
      (fun n hn => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with rfl | rfl
        · exact (firstEdgePhase_trig q hk ho).2
        · exact (firstEdgePhase_trig q hk hp).2)]
    field_simp
  · have hneg : firstChi q k < 0 := lt_of_not_ge hsign
    rw [abs_of_neg hneg]
    have hn : ((1 : ℤ) : ℝ) = (1 - (k : ℤ) : ℤ) + (k : ℝ) := by push_cast; ring
    have hmean : 2 * deriv (firstEdgePhase q k) (2 * Real.pi / k) =
        ((1 - (k : ℤ) : ℤ) : ℝ) + (1 + 2 * firstChi q k / k) * (k : ℝ) := by
      push_cast
      unfold firstChi
      field_simp
      ring
    rw [FareyPlateau.Edge.symbol_second hθ hc hn hmean
      (fun n hn => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with rfl | rfl
        · exact (firstEdgePhase_trig q hk hm).1
        · exact (firstEdgePhase_trig q hk ho).1)
      (fun n hn => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with rfl | rfl
        · exact (firstEdgePhase_trig q hk hm).2
        · exact (firstEdgePhase_trig q hk ho).2)]
    field_simp
    ring

end polyak.GapEdges
