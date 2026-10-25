import polyak.Farey.Records.Selection

/-! The record selection rule is exactly the absence of lattice points
in the source rectangle, for every real height, including negative heights. -/
noncomputable section
namespace polyak.Farey

/-- The congruence lattice Γ={(p,y): y≡pτ mod k}. -/
def recordLattice (k τ : ℤ) : Set (ℤ×ℤ) := {z | k∣z.2-z.1*τ}

/-- The integer points of [1,t)×[0,ac]. -/
def recordBox (t : ℤ) (ac : ℝ) : Set (ℤ×ℤ) :=
  {z | 1≤z.1 ∧ z.1<t ∧ 0≤z.2 ∧ (z.2:ℝ)≤ac}

theorem recordLattice_iff_congruence (k τ p y : ℤ) :
    (p,y)∈recordLattice k τ ↔ y%k=(p*τ)%k := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero,←Int.dvd_iff_emod_eq_zero]
  rfl

theorem record_selection_iff_no_lattice_point {k t τ : ℤ} (hk : 0<k) (ac : ℝ) :
    RecordSelection k t τ ac ↔
      ¬∃p y : ℤ,1≤p ∧ p<t ∧ 0≤y ∧ (y:ℝ)≤ac ∧ k∣y-p*τ := by
  constructor
  · intro hs
    rintro ⟨p,y,hp,hpt,hy,hyac,l,hl⟩
    have he : p*τ=y+(-l)*k := by linear_combination -hl
    have hres : residue k τ p=y%k := by
      unfold residue
      rw [he,Int.add_mul_emod_self_right]
    have hq : 0≤y/k := Int.ediv_nonneg hy hk.le
    have hprod : 0≤(y/k)*k := mul_nonneg hq hk.le
    have hbound : residue k τ p≤y := by
      rw [hres]
      have hdiv:=Int.emod_add_ediv_mul y k
      omega
    have hboundR : (residue k τ p:ℝ)≤y := by exact_mod_cast hbound
    exact (not_lt_of_ge (hboundR.trans hyac)) (hs p hp hpt)
  · intro hn p hp hpt
    apply lt_of_not_ge
    intro hh
    apply hn
    refine ⟨p,residue k τ p,hp,hpt,Int.emod_nonneg _ (ne_of_gt hk),hh,?_,?_⟩
    · exact -((p*τ)/k)
    · unfold residue
      linear_combination Int.emod_add_ediv_mul (p*τ) k

theorem record_selection_iff_empty_box {k t τ : ℤ} (hk : 0<k) (ac : ℝ) :
    RecordSelection k t τ ac ↔ recordLattice k τ∩recordBox t ac=∅ := by
  rw [record_selection_iff_no_lattice_point hk ac,Set.eq_empty_iff_forall_notMem]
  constructor
  · intro hn z hz
    exact hn ⟨z.1,z.2,hz.2.1,hz.2.2.1,hz.2.2.2.1,hz.2.2.2.2,hz.1⟩
  · intro hn
    rintro ⟨p,y,hp,hpt,hy,hyac,hl⟩
    exact hn (p,y) ⟨hl,hp,hpt,hy,hyac⟩

end polyak.Farey
