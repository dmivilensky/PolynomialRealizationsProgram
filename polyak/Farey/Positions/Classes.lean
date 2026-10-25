import polyak.Farey.Positions.Source

/-! The three distinguished position classes and the explicit inverse. -/
noncomputable section
namespace polyak.Farey

theorem position_inverse_left {j k : ℕ} (hjk : j.Coprime k) :
    Function.LeftInverse (fun p : ZMod k=>(j:ZMod k)⁻¹*p) (fun p=>(j:ZMod k)*p) := by
  intro p
  have hi : (j:ZMod k)⁻¹*(j:ZMod k)=1 := by simpa only [mul_comm] using ZMod.coe_mul_inv_eq_one j hjk
  change (j:ZMod k)⁻¹*((j:ZMod k)*p)=p
  rw [←mul_assoc,hi,one_mul]

theorem position_inverse_right {j k : ℕ} (hjk : j.Coprime k) :
    Function.RightInverse (fun p : ZMod k=>(j:ZMod k)⁻¹*p) (fun p=>(j:ZMod k)*p) := by
  intro p
  change (j:ZMod k)*((j:ZMod k)⁻¹*p)=p
  rw [←mul_assoc,ZMod.coe_mul_inv_eq_one j hjk,one_mul]

theorem position_anchor_class {j k : ℤ} (P : Levels.Lattice.FareyParents j k)
    (hj : 0≤j) (hjk : j<k) (n : ℤ) : (n*j)%k=j ↔ k∣n-1 := by
  rw [←position_zero_class P (n-1)]
  have he : (n-1)*j=n*j-j := by ring
  rw [he]
  rw [←Int.emod_eq_emod_iff_emod_sub_eq_zero,Int.emod_eq_of_lt hj hjk]

theorem lower_parent_position_one {j k : ℤ} (P : Levels.Lattice.FareyParents j k)
    (hk : 1<k) : (P.b*j)%k=1 :=
  (position_one_class P hk P.b).mpr (by simp only [sub_self]; exact dvd_zero k)

theorem upper_parent_position_one {j k : ℤ} (P : Levels.Lattice.FareyParents j k)
    (hk : 1<k) : ((-P.d)*j)%k=1 := by
  apply (position_one_class P hk (-P.d)).mpr
  refine ⟨-1,?_⟩
  linear_combination P.denominator

end polyak.Farey
