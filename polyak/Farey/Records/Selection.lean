import polyak.Farey.Records.Theorem

/-! The full-depth Farey selection rule and its shallow restrictions. -/
noncomputable section
namespace polyak.Farey

def RecordSelection (k t τ : ℤ) (ac : ℝ) : Prop :=
  ∀p : ℤ,1≤p → p < t → ac < (residue k τ p:ℝ)

theorem record_selection_iff {k j τ i m : ℤ} {ac : ℝ}
    (hj : 2≤j) (hi : 0 < i) (hik : i < k) (he : j*τ=m*k+i)
    (hac : (i:ℝ) < ac) :
    RecordSelection k j τ ac ↔ Int.gcd m j=1 ∧
      ∃R : RightParent m j,i*R.den < k ∧
        ac < ((k:ℝ)+(R.leftDen:ℝ)*(i:ℝ))/(j:ℝ) := by
  constructor
  · intro hs
    have hr : RecordLow k j τ i := by
      intro p hp hpj
      have h := hac.trans (hs p hp hpj)
      exact_mod_cast h
    obtain ⟨hc,R,hcut⟩ := (record_low_iff hj hi hik he).mp hr
    refine ⟨hc,R,hcut,?_⟩
    have hlp : 1≤R.leftDen := by have h:=R.leftDen_pos;omega
    have hh := hs R.leftDen hlp R.leftDen_lt
    rw [(R.residue_at_left hi hik he hcut).1] at hh
    have heR : (j:ℝ)*(R.upperHeight k τ:ℝ)=(k:ℝ)+(R.leftDen:ℝ)*(i:ℝ) := by
      exact_mod_cast (R.heights he).1
    have hjR : (0:ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    rw [←heR,mul_div_cancel_left₀ _ hjR.ne']
    exact hh
  · rintro ⟨_,R,hcut,hbound⟩ p hp hpj
    have heR : (j:ℝ)*(R.upperHeight k τ:ℝ)=(k:ℝ)+(R.leftDen:ℝ)*(i:ℝ) := by
      exact_mod_cast (R.heights he).1
    have hjR : (0:ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    rw [←heR,mul_div_cancel_left₀ _ hjR.ne'] at hbound
    exact hbound.trans_le (by exact_mod_cast (R.strip_minimum hi hik he hcut p hp hpj).1)

theorem record_selection_shallow {k j t τ : ℤ} {ac : ℝ} (ht : t≤j)
    (h : RecordSelection k j τ ac) : RecordSelection k t τ ac := by
  intro p hp hpt
  exact h p hp (hpt.trans_le ht)

end polyak.Farey
