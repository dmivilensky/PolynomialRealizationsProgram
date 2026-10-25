import polyak.GapEdges.Junction.LargeSlope

/-! The actual adjacent-lag construction at a junction, with its original
strict convex weights, also when the slope has crossed several lag cells. -/
noncomputable section
namespace polyak.GapEdges.Junction
open General Levels ModeLocking Set Filter
open scoped Topology

theorem junction_half_angle {k : ℕ} (hk : 4≤k) :
    Real.pi/k∈Ioo (0:ℝ) (Real.pi/2) := by
  have hkr : (4:ℝ)≤k := by exact_mod_cast hk
  exact ⟨by positivity,div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by linarith)⟩

theorem adjacent_frequency_one {q : Tuning} {k : ℕ} (A : FareyPlateau.Edge.AdjacentData q 1 k) :
    (A.frequency:ℝ)=2*Real.pi/k := by
  dsimp [FareyPlateau.Edge.AdjacentData.frequency,FareyPlateau.Edge.atom,Farey.gridFrequency]
  push_cast
  ring

theorem junction_edge_shift (q : Tuning) {k : ℕ} (hk : 4≤k) {a t₂ : ℝ}
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*(Real.pi/k))) t₂) :
    FareyPlateau.Edge.shift q k (2*Real.pi/k)=0 := by
  have hh := (junction_cotangent_jets q (junction_half_angle hk) hXi).1
  rw [show 2*(Real.pi/k)=2*Real.pi/k by ring] at hh
  unfold FareyPlateau.Edge.shift
  rw [hh]
  ring

theorem junction_adjacent_phase {q : Tuning} {k : ℕ}
    (A : FareyPlateau.Edge.AdjacentData q 1 k) (hk : 4≤k) {a t₂ : ℝ}
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*(Real.pi/k))) t₂) :
    TwoLag.phase q A.edgeShift =ᶠ[𝓝 (2*Real.pi/k)] Geometry.shiftedAngle q 0 := by
  have hs : A.edgeShift=0 := by
    unfold FareyPlateau.Edge.AdjacentData.edgeShift
    rw [adjacent_frequency_one A]
    exact junction_edge_shift q hk hXi
  have hc := junction_half_angle hk
  have hω : 2*Real.pi/k∈Ioo (0:ℝ) Real.pi := by
    rw [show 2*Real.pi/k=2*(Real.pi/k) by ring]
    constructor <;> linarith [hc.1,hc.2]
  filter_upwards [Ioo_mem_nhds hω.1 hω.2] with x hx
  rw [hs,TwoLag.phase,Geometry.jointAngle_actual q 0 ⟨hx.1.le,hx.2.le⟩]

theorem junction_adjacent_slope {q : Tuning} {k : ℕ}
    (A : FareyPlateau.Edge.AdjacentData q 1 k) (hk : 4≤k) {a t₂ : ℝ}
    (hXi : Chart.coefficients q=junctionCoefficients a (Real.cos (2*(Real.pi/k))) t₂) :
    (A.lower:ℝ)+A.mix*k=1-2*junctionG a (Real.cos (2*(Real.pi/k))) t₂ (Real.pi/k) := by
  have hh := (junction_angle_jets q (junction_half_angle hk) hXi).2.1
  rw [show 2*(Real.pi/k)=2*Real.pi/k by ring] at hh
  have hs := A.slope
  change 2*deriv (TwoLag.phase q A.edgeShift) A.frequency=(A.lower:ℝ)+A.mix*k at hs
  rw [adjacent_frequency_one A,(junction_adjacent_phase A hk hXi).deriv_eq] at hs
  unfold junctionG
  rw [show 2*(Real.pi/k)=2*Real.pi/k by ring]
  linarith

theorem adjacent_inverse_one {q : Tuning} {k : ℕ}
    (A : FareyPlateau.Edge.AdjacentData q 1 k) : A.inverse=1 := by
  have hh := A.inverse_mod
  change (A.inverse*1)%(k:ℤ)=1%(k:ℤ) at hh
  rw [mul_one,Int.emod_eq_of_lt A.inverse_pos.le A.inverse_lt,
    Int.emod_eq_of_lt (by norm_num : (0:ℤ)≤1)
      (by have := A.period_ge; omega : (1:ℤ)<k)] at hh
  exact hh

theorem adjacent_lower_in_first_strip {q : Tuning} {k : ℕ}
    (A : FareyPlateau.Edge.AdjacentData q 1 k) {g : ℝ}
    (hg : 0<g) (hkg : g<(k:ℝ)/2)
    (hs : (A.lower:ℝ)+A.mix*k=1-2*g) :
    A.lower=1-(k:ℤ) ∧ A.mix=1-2*g/k := by
  have hk : (0:ℝ)<k := by exact_mod_cast (show 0<k by have := A.period_ge; omega)
  have hlow := A.lower_class
  rw [adjacent_inverse_one A] at hlow
  have hdiv := Int.emod_add_mul_ediv A.lower (k:ℤ)
  rw [hlow] at hdiv
  have hdivR : (1:ℝ)+(k:ℝ)*(A.lower/(k:ℤ):ℤ)=(A.lower:ℝ) := by exact_mod_cast hdiv
  have hmix := A.mix_pos
  have hmix' := A.mix_lt
  have hdivneg : (A.lower/(k:ℤ):ℤ)<0 := by
    by_contra hh
    have hz : (0:ℝ)≤(A.lower/(k:ℤ):ℤ) := by exact_mod_cast (le_of_not_gt hh)
    nlinarith
  have hdivgt : -2<(A.lower/(k:ℤ):ℤ) := by
    by_contra hh
    have hz : ((A.lower/(k:ℤ):ℤ):ℝ)≤ -2 := by exact_mod_cast (le_of_not_gt hh)
    nlinarith
  have hd : A.lower/(k:ℤ)= -1 := by omega
  have hl : A.lower=1-(k:ℤ) := by rw [hd] at hdiv; linear_combination -hdiv
  refine ⟨hl,?_⟩
  rw [hl] at hs
  push_cast at hs
  calc
    A.mix=((k:ℝ)-2*g)/k := (eq_div_iff hk.ne').mpr (by linarith)
    _=1-2*g/k := by field_simp

end polyak.GapEdges.Junction
