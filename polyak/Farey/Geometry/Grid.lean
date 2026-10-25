import polyak.Farey.Positions.Basic
import polyak.Levels.Program.FiniteAtoms
import Mathlib.Data.Int.GCD

/-! Primitive coordinates of every point on an arbitrary periodic grid. -/
noncomputable section
namespace polyak.Farey
open Levels

theorem grid_primitive_coordinates {L : ℕ} (hL : 0<L) {ω : Frequency}
    (hω : ω∈periodicGrid L) :
    ∃j k : ℕ,1≤j ∧ 0<k ∧ 2*j≤k ∧ j.Coprime k ∧ k∣L ∧
      (ω:ℝ)=2*Real.pi*j/k := by
  obtain ⟨i,hi,hik,he⟩:=(mem_periodicGrid_iff hL ω).mp hω
  let t:=i.toNat
  have ht : (t:ℤ)=i := Int.toNat_of_nonneg hi.le
  have htpos : 0<t := by omega
  let g:=Nat.gcd t L
  let j:=t/g
  let k:=L/g
  have hg : 0<g := Nat.gcd_pos_of_pos_right t hL
  have hj : 0<j := Nat.div_gcd_pos_of_pos_left L htpos
  have hk : 0<k := by simpa only [k,g,Nat.gcd_comm] using Nat.div_gcd_pos_of_pos_left t hL
  have hjg : j*g=t := Nat.div_mul_cancel (Nat.gcd_dvd_left t L)
  have hkg : k*g=L := Nat.div_mul_cancel (Nat.gcd_dvd_right t L)
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  have hLr : (0:ℝ)<L := by exact_mod_cast hL
  have hratio : (t:ℝ)/L=(j:ℝ)/k := by
    rw [div_eq_div_iff (ne_of_gt hLr) (ne_of_gt hkr)]
    have h1 : (j:ℝ)*g=t := by exact_mod_cast hjg
    have h2 : (k:ℝ)*g=L := by exact_mod_cast hkg
    rw [←h1,←h2]
    ring
  have hω' : (ω:ℝ)=2*Real.pi*j/k := by
    have hit : (i:ℝ)=(t:ℝ) := by exact_mod_cast ht.symm
    rw [hit] at he
    calc
      (ω:ℝ)=2*Real.pi*((t:ℝ)/L) := by rw [he]; ring
      _=2*Real.pi*((j:ℝ)/k) := by rw [hratio]
      _=2*Real.pi*j/k := by ring
  refine ⟨j,k,by omega,hk,?_,Nat.coprime_div_gcd_div_gcd hg,
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_right t L),hω'⟩
  have hh:=ω.property.2
  rw [hω'] at hh
  have hh' := (div_le_iff₀ hkr).mp hh
  have hr : (2:ℝ)*j≤k := by nlinarith [Real.pi_pos]
  exact_mod_cast hr

end polyak.Farey
