import polyak.Farey.Records.Selection

/-! Literal source residue and quotient definitions discharge the lattice
incidence automatically. The multiplier remains an arbitrary integer. -/
namespace polyak.Farey

def recordNumerator (k j τ : ℤ) : ℤ := (j*τ-residue k τ j)/k

theorem recordNumerator_identity (k j τ : ℤ) :
    j*τ=recordNumerator k j τ*k+residue k τ j := by
  have h := Int.ediv_mul_add_emod (j*τ) k
  have hd : k∣j*τ-residue k τ j := by
    refine ⟨j*τ/k,?_⟩
    dsimp [residue]
    linear_combination -h
  have he := Int.ediv_mul_cancel hd
  change recordNumerator k j τ*k=j*τ-residue k τ j at he
  omega

theorem record_low_residue_iff {k j τ : ℤ} (hk : 0 < k) (hj : 2≤j)
    (hi : 0 < residue k τ j) :
    RecordLow k j τ (residue k τ j) ↔ Int.gcd (recordNumerator k j τ) j=1 ∧
      ∃R : RightParent (recordNumerator k j τ) j,(residue k τ j)*R.den < k :=
  record_low_iff hj hi (Int.emod_lt_of_pos _ hk) (recordNumerator_identity k j τ)

theorem record_low_unique_minimum {k j τ : ℤ} (hk : 0 < k) (hj : 2≤j)
    (hi : 0 < residue k τ j) (hrec : RecordLow k j τ (residue k τ j)) :
    ∃R : RightParent (recordNumerator k j τ) j,
      residue k τ R.leftDen=(k+R.leftDen*residue k τ j)/j ∧
      (∀p : ℤ,1≤p → p < j → residue k τ R.leftDen≤residue k τ p) ∧
      (∀p : ℤ,1≤p → p < j → (residue k τ p=residue k τ R.leftDen ↔ p=R.leftDen)) := by
  obtain ⟨_,R,hcut⟩ := (record_low_residue_iff hk hj hi).mp hrec
  exact ⟨R,record_minimum R hi (Int.emod_lt_of_pos _ hk) (recordNumerator_identity k j τ) hcut⟩

end polyak.Farey
