import polyak.FareyPlateau.Edge.Basic

/-! The inverse representative used in every Farey-edge theorem is
constructed for every reduced positive fraction. -/
noncomputable section
namespace polyak.FareyPlateau.Edge

theorem inverse_exists {j k : ℕ} (hk : 2 ≤ k) (hcop : j.Coprime k) :
    ∃b : ℤ,0<b ∧ b<k ∧ b*(j:ℤ) ≡ 1 [ZMOD (k:ℤ)] := by
  let a := Int.gcdA (j:ℤ) (k:ℤ)
  let b := a%(k:ℤ)
  have hkr : (0:ℤ)<k := by omega
  have he : (j:ℤ)*a+(k:ℤ)*Int.gcdB j k=1 := by
    simpa only [a,Int.gcd_natCast_natCast,hcop.gcd_eq_one,Nat.cast_one] using
      (Int.gcd_eq_gcd_ab (j:ℤ) (k:ℤ)).symm
  have ha : a*(j:ℤ) ≡ 1 [ZMOD (k:ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨Int.gcdB j k,by linear_combination -he⟩
  have hb : b*(j:ℤ) ≡ 1 [ZMOD (k:ℤ)] := by
    change (a%(k:ℤ)*(j:ℤ))%(k:ℤ)=1%(k:ℤ)
    rw [Int.mul_emod,Int.emod_emod,←Int.mul_emod]
    exact ha
  have hb0 : 0≤b := Int.emod_nonneg a hkr.ne'
  have hbk : b<k := Int.emod_lt_of_pos a hkr
  have hbpos : 0<b := by
    by_contra hn
    have hz : b=0 := by omega
    have hh := hb
    rw [hz,zero_mul] at hh
    change 0%(k:ℤ)=1%(k:ℤ) at hh
    rw [Int.zero_emod,Int.emod_eq_of_lt (by norm_num) (by omega)] at hh
    omega
  exact ⟨b,hbpos,hbk,hb⟩

end polyak.FareyPlateau.Edge
