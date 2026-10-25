import polyak.Levels.Lattice.Signs
import Mathlib.Data.ZMod.Basic

/-! Exact integral incidence for Farey parents, with both signed parent
lags and a modular inverse valid also for composite denominators. -/
noncomputable section
namespace polyak.Levels.Lattice

/-- Parent data are the literal unimodular Farey relations. -/
structure FareyParents (j k : ℤ) where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  numerator : j=a+c
  denominator : k=b+d
  determinant : b*c-a*d=1
  b_pos : 0<b
  d_pos : 0<d

namespace FareyParents
variable {j k : ℤ} (P : FareyParents j k)

theorem lower_bezout : P.b*j-P.a*k=1 := by
  linear_combination P.determinant+P.b*P.numerator-P.a*P.denominator

theorem upper_bezout : (-P.d)*j-(-P.c)*k=1 := by
  linear_combination P.determinant-P.d*P.numerator+P.c*P.denominator

theorem lower_other_parent : P.b*P.c-P.a*P.d=1 := P.determinant

theorem upper_other_parent : (-P.d)*P.a-(-P.c)*P.b=1 := by
  linear_combination P.determinant

include P in
theorem period_pos : 0<k := by linarith [P.denominator,P.b_pos,P.d_pos]

theorem parents_lt_period : P.b<k ∧ P.d<k := by
  constructor <;> linarith [P.denominator,P.b_pos,P.d_pos]

/-- All lines through the child point have exactly one congruence class. -/
theorem incidence_iff_dvd (n : ℤ) :
    (∃ l : ℤ,n*j-l*k=1) ↔ k∣n-P.b := by
  constructor
  · rintro ⟨l,hl⟩
    have he : n-P.b=k*(P.b*l-P.a*n) := by
      linear_combination P.b*hl-n*P.lower_bezout
    exact ⟨P.b*l-P.a*n,he⟩
  · rintro ⟨t,ht⟩
    refine ⟨P.a+t*j,?_⟩
    linear_combination P.lower_bezout+j*ht

/-- There are precisely two representatives with absolute value below the
period: the positive lower-parent denominator and negative upper one. -/
theorem small_incidence_iff (n : ℤ) (hn : |n|<k) :
    (∃ l : ℤ,n*j-l*k=1) ↔ n=P.b ∨ n= -P.d := by
  rw [P.incidence_iff_dvd]
  constructor
  · rintro ⟨t,ht⟩
    have hb:=P.parents_lt_period
    have hnp:=abs_lt.mp hn
    have hk:=P.period_pos
    have htlo : -2<t := by nlinarith
    have hthi : t<1 := by nlinarith [P.b_pos]
    have htcase : t= -1 ∨ t=0 := by omega
    rcases htcase with rfl|rfl
    · right
      linarith [P.denominator]
    · left
      linarith
  · rintro (rfl|rfl)
    · simpa only [sub_self] using dvd_zero k
    · refine ⟨-1,?_⟩
      linarith [P.denominator]

end FareyParents

/-- Inverse congruence in ZMod includes all signed integer lags. The
coprimality assumption is explicit; no primality assumption on k is used. -/
theorem incidence_iff_zmod_inverse {j k : ℕ} (hjk : j.Coprime k) (n : ℤ) :
    (∃ l : ℤ,n*(j:ℤ)-l*(k:ℤ)=1) ↔ (n : ZMod k)=(j : ZMod k)⁻¹ := by
  have hinv:=ZMod.coe_mul_inv_eq_one j hjk
  have hbez : (∃ l : ℤ,n*(j:ℤ)-l*(k:ℤ)=1) ↔
      (n : ZMod k)*(j : ZMod k)=1 := by
    constructor
    · rintro ⟨l,hl⟩
      have he:=congrArg (Int.castRingHom (ZMod k)) hl
      simpa using he
    · intro hh
      have hz : ((n*(j:ℤ)-1:ℤ):ZMod k)=0 := by
        push_cast
        rw [hh,sub_self]
      obtain ⟨l,hl⟩:=(ZMod.intCast_zmod_eq_zero_iff_dvd (n*(j:ℤ)-1) k).mp hz
      exact ⟨l,by linear_combination hl⟩
  rw [hbez]
  constructor
  · intro h
    calc
      (n : ZMod k)=(n : ZMod k)*((j:ZMod k)*(j:ZMod k)⁻¹) := by rw [hinv,mul_one]
      _=(j:ZMod k)⁻¹ := by rw [←mul_assoc,h,one_mul]
  · intro h
    rw [h,mul_comm,hinv]

end polyak.Levels.Lattice
