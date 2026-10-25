import polyak.Farey.Positions.Basic
import polyak.Farey.Records.Basic
import polyak.Farey.Combs.Ratio

/-! Two-atom coordinates at arbitrary anchor depth. Both finite sets of
negative positions are genuine, nonempty sets with their actual signs. -/
noncomputable section
namespace polyak.Farey

structure CombData where
  k : ℤ
  j : ℤ
  i : ℤ
  t : ℤ
  τ : ℤ
  a : ℝ
  ac : ℝ
  k_pos : 0 < k
  j_ge : 2 ≤ j
  j_half : 2*j < k
  i_pos : 0 < i
  i_half : 2*i < k
  i_ne : i≠j
  t_ge : 2 ≤ t
  t_le : t≤j
  depth_lower : (t:ℝ)-1 < a
  depth_upper : a≤t
  companion_out : (i:ℝ) < ac
  companion_le : ac≤k
  transport : k∣i-τ*j

def CombData.positions (d : CombData) : Finset ℤ := Finset.Icc 1 (d.k-1)
def CombData.anchorColumn (d : CombData) (p : ℤ) : ℝ := positionValue d.k d.a p
def CombData.companionColumn (d : CombData) (p : ℤ) : ℝ :=
  positionValue d.k d.ac (residue d.k d.τ p)
def CombData.Selection (d : CombData) : Prop :=
  ∀p : ℤ,1≤p → p < d.t → d.ac < (residue d.k d.τ p:ℝ)

theorem CombData.a_pos (d : CombData) : 0 < d.a := by
  have ht : (2:ℝ)≤d.t := by exact_mod_cast d.t_ge
  linarith [d.depth_lower]

theorem CombData.a_le (d : CombData) : d.a≤d.k := by
  have hj := d.j_half
  have ht := d.t_le
  have hj0 := d.j_ge
  have htk : d.t≤d.k := by omega
  exact d.depth_upper.trans (by exact_mod_cast htk)

theorem CombData.ac_pos (d : CombData) : 0 < d.ac :=
  (show (0:ℝ) < d.i by exact_mod_cast d.i_pos).trans d.companion_out

theorem CombData.anchor_negative (d : CombData) (p : ℤ) (hp : p∈d.positions) :
    d.anchorColumn p < 0 ↔ p < d.t := by
  obtain ⟨hp0,hpk⟩ := Finset.mem_Icc.mp hp
  have hpR : (0:ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hpkR : (p:ℝ) < d.k := by exact_mod_cast (by omega : p < d.k)
  rw [anchorColumn,positionValue_neg_iff d.k_pos d.a_pos d.a_le hpR hpkR]
  constructor
  · intro h
    have hpt : (p:ℝ) < d.t := h.trans_le d.depth_upper
    exact_mod_cast hpt
  · intro h
    have hpt : p≤d.t-1 := by omega
    have hptR : (p:ℝ)≤(d.t:ℝ)-1 := by exact_mod_cast hpt
    exact hptR.trans_lt d.depth_lower

theorem CombData.residue_bounds (d : CombData) (p : ℤ) :
    0≤residue d.k d.τ p ∧ residue d.k d.τ p < d.k :=
  ⟨Int.emod_nonneg _ d.k_pos.ne',Int.emod_lt_of_pos _ d.k_pos⟩

theorem CombData.companion_positive (d : CombData) (p : ℤ) :
    0 < d.companionColumn p ↔ d.ac < (residue d.k d.τ p:ℝ) := by
  obtain ⟨hr0,hrk⟩ := d.residue_bounds p
  by_cases hr : residue d.k d.τ p=0
  · simp only [companionColumn,hr,Int.cast_zero,positionValue_zero]
    have ha := d.ac_pos
    constructor <;> intro h <;> linarith
  · have hrp : (0:ℝ) < residue d.k d.τ p := by exact_mod_cast (by omega : 0 < residue d.k d.τ p)
    have hrkR : (residue d.k d.τ p:ℝ) < d.k := by exact_mod_cast hrk
    exact positionValue_pos_iff d.k_pos d.ac_pos d.companion_le hrp hrkR

theorem CombData.companion_negative (d : CombData) (p : ℤ) :
    d.companionColumn p < 0 ↔
      1≤residue d.k d.τ p ∧ (residue d.k d.τ p:ℝ) < d.ac := by
  obtain ⟨hr0,hrk⟩ := d.residue_bounds p
  by_cases hr : residue d.k d.τ p=0
  · simp only [companionColumn,hr,Int.cast_zero,positionValue_zero]
    norm_num
  · have hr1 : 1≤residue d.k d.τ p := by omega
    have hrp : (0:ℝ) < residue d.k d.τ p := by exact_mod_cast (by omega : 0 < residue d.k d.τ p)
    have hrkR : (residue d.k d.τ p:ℝ) < d.k := by exact_mod_cast hrk
    rw [companionColumn,positionValue_neg_iff d.k_pos d.ac_pos d.companion_le hrp hrkR]
    exact ⟨fun h=>⟨hr1,h⟩,fun h=>h.2⟩

theorem CombData.residue_anchor (d : CombData) : residue d.k d.τ d.j=d.i := by
  obtain ⟨q,hq⟩ := d.transport
  apply residue_eq_of_lattice d.i_pos.le (by have h:=d.i_half;have hp:=d.i_pos;omega) (q:= -q)
  linear_combination -hq

theorem CombData.anchor_negative_nonempty (d : CombData) :
    (negativePositions d.positions d.anchorColumn).Nonempty := by
  refine ⟨1,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
  · apply Finset.mem_Icc.mpr
    have hj := d.j_ge
    have hk := d.j_half
    omega
  · apply (d.anchor_negative 1 ?_).mpr
    · have ht := d.t_ge
      omega
    · apply Finset.mem_Icc.mpr
      have hj := d.j_ge
      have hk := d.j_half
      omega

theorem CombData.companion_negative_nonempty (d : CombData) :
    (negativePositions d.positions d.companionColumn).Nonempty := by
  refine ⟨d.j,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
  · apply Finset.mem_Icc.mpr
    have hj := d.j_ge
    have hk := d.j_half
    omega
  · apply (d.companion_negative d.j).mpr
    rw [d.residue_anchor]
    exact ⟨by have hi:=d.i_pos;omega,d.companion_out⟩

theorem CombData.selection_iff (d : CombData) :
    d.Selection ↔ ∀p∈d.positions,d.anchorColumn p < 0 → 0 < d.companionColumn p := by
  constructor
  · intro h p hp hn
    exact (d.companion_positive p).mpr (h p (Finset.mem_Icc.mp hp).1 ((d.anchor_negative p hp).mp hn))
  · intro h p hp hpt
    have hmem : p∈d.positions := by
      apply Finset.mem_Icc.mpr
      have ht := d.t_le
      have hj := d.j_half
      have hj0 := d.j_ge
      omega
    exact (d.companion_positive p).mp (h p hmem ((d.anchor_negative p hmem).mpr hpt))

end polyak.Farey
