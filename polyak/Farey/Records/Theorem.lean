import polyak.Farey.Records.Minimum

/-! The full record-low equivalence, with a constructed right parent and
the exact uniquely attained minimum. -/
namespace polyak.Farey

theorem record_low_iff {k j τ i m : ℤ} (hj : 2 ≤ j) (hi : 0 < i) (hik : i < k)
    (he : j*τ=m*k+i) :
    RecordLow k j τ i  ↔  Int.gcd m j=1  ∧ 
      ∃R : RightParent m j,i*R.den < k := by
  constructor
  · intro hrec
    have hc := recordLow_coprime hj hi hik he hrec
    obtain ⟨R⟩ := exists_rightParent hj hc
    refine ⟨hc,R,?_⟩
    by_contra hn
    have hcut : k ≤ i*R.den := le_of_not_gt hn
    have hjp : 0 < j := by omega
    obtain ⟨_,hv,_⟩ := R.heights he
    have hv0 : 0 ≤ R.lowerHeight k τ := by nlinarith
    have hvi : R.lowerHeight k τ < i := by
      have hd := R.den_lt
      have hmul := mul_lt_mul_of_pos_left hd hi
      nlinarith
    have hr : residue k τ R.den=R.lowerHeight k τ :=
      residue_eq_of_lattice hv0 (hvi.trans hik) (q:=R.num)
        (by dsimp [RightParent.lowerHeight];ring)
    have hh := hrec R.den (by have hd:=R.den_pos;omega) R.den_lt
    rw [hr] at hh
    omega
  · rintro ⟨_,R,hcut⟩ p hp hpj
    have hh := R.strip_minimum hi hik he hcut p hp hpj
    exact (R.residue_at_left hi hik he hcut).2.1.trans_le hh.1

theorem record_low_iff_for_parent {k j τ i m : ℤ} (R : RightParent m j)
    (hj : 2 ≤ j) (hi : 0 < i) (hik : i < k) (he : j*τ=m*k+i) :
    RecordLow k j τ i  ↔  i*R.den < k := by
  constructor
  · intro h
    obtain ⟨_,S,hS⟩ := (record_low_iff hj hi hik he).mp h
    rwa [R.unique S]
  · intro h p hp hpj
    exact (R.residue_at_left hi hik he h).2.1.trans_le
      (R.strip_minimum hi hik he h p hp hpj).1

theorem record_minimum {k j τ i m : ℤ} (R : RightParent m j)
    (hi : 0 < i) (hik : i < k) (he : j*τ=m*k+i) (hcut : i*R.den < k) :
    residue k τ R.leftDen=(k+R.leftDen*i)/j  ∧ 
    (∀p : ℤ,1 ≤ p → p < j → residue k τ R.leftDen ≤ residue k τ p)  ∧ 
    (∀p : ℤ,1 ≤ p → p < j → (residue k τ p=residue k τ R.leftDen ↔ p=R.leftDen)) := by
  have hj : j≠0 := (R.den_pos.trans R.den_lt).ne'
  have hr := (R.residue_at_left hi hik he hcut).1
  have hu := (R.heights he).1
  refine ⟨?_,?_,?_⟩
  · rw [hr,←hu,mul_comm j,Int.mul_ediv_cancel _ hj]
  · intro p hp hpj
    rw [hr]
    exact (R.strip_minimum hi hik he hcut p hp hpj).1
  · intro p hp hpj
    rw [hr]
    exact (R.strip_minimum hi hik he hcut p hp hpj).2

end polyak.Farey
