import polyak.Farey.Combs.Source

/-! The spine multipliers are consequences of the actual companion
transport, and are not extra congruence hypotheses of the selection rule. -/
namespace polyak.Farey

theorem residue_congr_multiplier {k τ σ : ℤ} (h : k∣τ-σ) (p : ℤ) :
    residue k τ p=residue k σ p := by
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  apply Int.emod_eq_zero_of_dvd
  convert dvd_mul_of_dvd_right h p using 1
  ring

theorem record_selection_congr {k t τ σ : ℤ} {ac : ℝ} (h : k∣τ-σ) :
    RecordSelection k t τ ac ↔ RecordSelection k t σ ac := by
  constructor
  · intro hs p hp hpt
    rw [←residue_congr_multiplier h p]
    exact hs p hp hpt
  · intro hs p hp hpt
    rw [residue_congr_multiplier h p]
    exact hs p hp hpt

private theorem cancel_multiplier {k j τ σ u v : ℤ} (hbez : u*j+v*k=1)
    (hdiv : k∣j*(τ-σ)) : k∣τ-σ := by
  obtain ⟨q,hq⟩ := hdiv
  refine ⟨u*q+v*(τ-σ),?_⟩
  linear_combination -(τ-σ)*hbez+u*hq

theorem CombData.first_spine_multiplier (d : CombData) {K p : ℤ}
    (hk : d.k=p*K+1) (hj : d.j=p) (hi : d.i=p-1) : d.k∣d.τ-(K+1) := by
  have hdiv : (p*K+1)∣p*(d.τ-(K+1)) := by
    obtain ⟨q,hq⟩ := d.transport
    rw [hk,hj,hi] at hq
    refine ⟨-q-1,?_⟩
    linear_combination -hq
  rw [hk]
  exact cancel_multiplier (u:= -K) (v:=1) (by ring) hdiv

theorem CombData.first_spine_selection (d : CombData) {K p : ℤ} (hK : 2≤K)
    (hk : d.k=p*K+1) (hj : d.j=p) (hi : d.i=p-1) :
    d.Selection ↔ d.ac < (K+1:ℤ) := by
  have hτ := d.first_spine_multiplier hk hj hi
  have hsel : d.Selection ↔ RecordSelection d.k d.t (K+1) d.ac :=
    record_selection_congr hτ
  rw [hsel,hk]
  apply polyak.Farey.first_spine_selection hK
  · simpa only [hj] using d.j_ge
  · exact d.t_ge
  · simpa only [hj] using d.t_le
  · simpa only [hi] using d.companion_out

theorem CombData.first_spine_forces (d : CombData) {K p : ℤ} (hK : 2≤K)
    (hk : d.k=p*K+1) (hj : d.j=p) (hi : d.i=p-1) (hs : d.Selection) : p≤K+1 := by
  have hh := (d.first_spine_selection hK hk hj hi).mp hs
  have hcomp : (p-1:ℤ) < d.ac := by simpa only [hi] using d.companion_out
  have hR : (p:ℝ) < (K:ℝ)+2 := by push_cast at hcomp hh;linarith
  have hI : p < K+2 := by exact_mod_cast hR
  omega

theorem CombData.second_spine_multiplier (d : CombData) {K l : ℤ}
    (hk : d.k=K+l*(K+1)) (hj : d.j=l+1) (hi : d.i=l) : d.k∣d.τ-(d.k-K) := by
  have hdiv : (K+l*(K+1))∣(l+1)*(d.τ-(K+l*(K+1)-K)) := by
    obtain ⟨q,hq⟩ := d.transport
    rw [hk,hj,hi] at hq
    refine ⟨-q-l,?_⟩
    linear_combination -hq
  rw [hk]
  exact cancel_multiplier (u:=K+1) (v:= -1) (by ring) hdiv

theorem CombData.second_spine_selection (d : CombData) {K l : ℤ} (hK : 2≤K)
    (hk : d.k=K+l*(K+1)) (hj : d.j=l+1) (hi : d.i=l) :
    d.Selection ↔ d.ac < (d.k-(d.t-1)*K:ℤ) := by
  have hτ := d.second_spine_multiplier hk hj hi
  have hsel : d.Selection ↔ RecordSelection d.k d.t (d.k-K) d.ac := record_selection_congr hτ
  rw [hsel,hk]
  apply polyak.Farey.second_spine_selection hK
  · have h := d.j_ge
    rw [hj] at h
    omega
  · exact d.t_ge
  · simpa only [hj] using d.t_le

theorem CombData.second_spine_full (d : CombData) {K l : ℤ} (hK : 2≤K)
    (hk : d.k=K+l*(K+1)) (hj : d.j=l+1) (hi : d.i=l) (ht : d.t=d.j) :
    d.Selection ↔ d.ac < (K+l:ℤ) := by
  rw [d.second_spine_selection hK hk hj hi,ht,hj,hk]
  have he : K+l*(K+1)-((l+1)-1)*K=K+l := by ring
  rw [he]

end polyak.Farey
