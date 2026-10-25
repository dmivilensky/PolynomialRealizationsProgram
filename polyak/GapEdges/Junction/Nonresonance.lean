import polyak.GapEdges.Junction.Construction
import polyak.GapEdges.Specialization.Opening
import polyak.FareyPlateau.Edge.Existence

/-! The source resonance exclusion constructs the genuine adjacent
symbol. Every amplitude in the explicit junction interval is nonresonant. -/
noncomputable section
namespace polyak.GapEdges.Junction
open General Levels ModeLocking Set Filter
open scoped Topology

theorem junction_firstChi (q : Tuning) {k : ℕ} (hk : 4≤k) {a t₂ : ℝ}
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*(Real.pi/k))) t₂) :
    firstChi q k= -junctionG a (Real.cos (2*(Real.pi/k))) t₂ (Real.pi/k) := by
  have hs := junction_edge_shift q hk hXi
  have he := firstEdgePhase_local q (show 3≤k by omega)
  rw [hs] at he
  have hj := (junction_angle_jets q (junction_half_angle hk) hXi).2.1
  unfold firstChi
  rw [he.deriv_eq]
  unfold junctionG
  rw [show 2*(Real.pi/k)=2*Real.pi/k by ring] at *
  linear_combination hj

theorem first_adjacent_exists (q : Tuning) {k : ℕ} (hk : 3≤k)
    (hres : ∀m : ℤ,firstChi q k≠(m:ℝ)*k/2) :
    Nonempty (FareyPlateau.Edge.AdjacentData q 1 k) := by
  apply FareyPlateau.Edge.adjacentData_nonempty q hk (by norm_num) (by omega)
    1 (by norm_num) (by omega) (by simp)
  intro m hm
  have hω : (FareyPlateau.Edge.atom 1 k (by omega) (by omega):ℝ)=2*Real.pi/k := by
    dsimp [FareyPlateau.Edge.atom,Farey.gridFrequency]
    push_cast
    ring
  rw [hω] at hm
  norm_num only [Int.cast_one] at hm
  change 2*deriv (firstEdgePhase q k) (2*Real.pi/k)=(1:ℝ)+m*k at hm
  apply hres m
  unfold firstChi
  linarith

theorem first_adjacent_in_strip (q : Tuning) {k : ℕ} (hk : 3≤k)
    (hχ : -(k:ℝ)/2<firstChi q k) (hχneg : firstChi q k<0) :
    Nonempty (FareyPlateau.Edge.AdjacentData q 1 k) := by
  apply first_adjacent_exists q hk
  intro m hm
  have hkr : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  rcases le_or_gt 0 m with hm0|hm0
  · have hmR : (0:ℝ)≤m := by exact_mod_cast hm0
    have hp : 0≤(m:ℝ)*k/2 := by positivity
    linarith
  · have hmR : (m:ℝ)≤ -1 := by exact_mod_cast (show m≤ -1 by omega)
    have hp := mul_le_mul_of_nonneg_right hmR hkr.le
    linarith

theorem junction_interval_adjacent (q : Tuning) {k : ℕ} (hk : 4≤k) {a t₂ : ℝ}
    (hd : t₂<Real.cos (2*(Real.pi/k)))
    (ha : a∈Ioo (junctionLower (Real.cos (2*(Real.pi/k))) t₂)
      (junctionUpper k (Real.cos (2*(Real.pi/k))) t₂ (Real.sin (Real.pi/k))))
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*(Real.pi/k))) t₂) :
    ∃A : FareyPlateau.Edge.AdjacentData q 1 k,deriv^[2] A.function A.frequency<0 := by
  have hb := (junction_interval_edge_negative q hk hd ha hXi).2
  have hchi := junction_firstChi q hk hXi
  obtain ⟨A⟩ := first_adjacent_in_strip q (k:=k) (by omega : 3≤k) (by rw [hchi]; linarith [hb.2])
    (by rw [hchi]; linarith [hb.1])
  refine ⟨A,?_⟩
  rw [adjacent_frequency_one A]
  exact (junction_adjacent_negative_iff A hk hd ha.1 hXi).mpr ha

end polyak.GapEdges.Junction
