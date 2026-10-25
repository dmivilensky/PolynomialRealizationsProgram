import polyak.Farey.Positions.Basic
import polyak.Levels.Lattice.Farey
import Mathlib.Data.Int.ModEq

/-! Multiplication permutes positions for every coprime period, including
composite periods. All transport statements retain signed integer lags. -/
noncomputable section
namespace polyak.Farey

theorem position_mul_bijective {j k : ℕ} (hjk : j.Coprime k) :
    Function.Bijective (fun p : ZMod k => (j:ZMod k)*p) := by
  have hi := ZMod.coe_mul_inv_eq_one j hjk
  have hi' : (j:ZMod k)⁻¹*(j:ZMod k)=1 := by simpa [mul_comm] using hi
  constructor
  · intro x y h
    have := congrArg (fun p : ZMod k => (j:ZMod k)⁻¹*p) h
    simpa only [←mul_assoc,hi',one_mul] using this
  · intro x
    refine ⟨(j:ZMod k)⁻¹*x,?_⟩
    change (j:ZMod k)*((j:ZMod k)⁻¹*x)=x
    rw [←mul_assoc,hi,one_mul]

theorem residue_transport {k i j τ : ℤ} (h : k∣i-τ*j) (n : ℤ) :
    (n*i)%k=(τ*((n*j)%k))%k := by
  have he : i ≡ τ*j [ZMOD k] := Int.modEq_iff_dvd.mpr (by simpa only [neg_sub] using dvd_neg.mpr h)
  have hh := he.mul_left n
  change (n*i)%k=(n*(τ*j))%k at hh
  rw [hh,show n*(τ*j)=τ*(n*j) by ring]
  simp only [Int.mul_emod,Int.emod_emod]

theorem residue_transport_of_inverse {k i j b : ℤ} (hb : b*j≡1 [ZMOD k]) (n : ℤ) :
    (n*i)%k=((i*b)*((n*j)%k))%k := by
  apply residue_transport
  have he : (i*b)*j ≡ i [ZMOD k] := by simpa only [mul_assoc,mul_one] using hb.mul_left i
  exact Int.modEq_iff_dvd.mp he

theorem position_one_class {j k : ℤ} (P : Levels.Lattice.FareyParents j k)
    (hk : 1<k) (n : ℤ) : (n*j)%k=1 ↔ k∣n-P.b := by
  rw [←P.incidence_iff_dvd n]
  constructor
  · intro h
    refine ⟨(n*j)/k,?_⟩
    have he := Int.emod_add_ediv_mul (n*j) k
    rw [h] at he
    linarith
  · rintro ⟨l,hl⟩
    have he : n*j=1+l*k := by linarith
    rw [he,Int.add_mul_emod_self_right,Int.emod_eq_of_lt (by omega) hk]

theorem position_zero_class {j k : ℤ} (P : Levels.Lattice.FareyParents j k)
    (n : ℤ) : (n*j)%k=0 ↔ k∣n := by
  rw [←Int.dvd_iff_emod_eq_zero]
  constructor
  · rintro ⟨l,hl⟩
    refine ⟨P.b*l-P.a*n,?_⟩
    linear_combination -n*P.lower_bezout+P.b*hl
  · intro h
    exact dvd_mul_of_dvd_left h j

theorem position_lag_one {j k : ℤ} (hj : 0≤j) (hjk : j<k) :
    ((1:ℤ)*j)%k=j := by simpa using Int.emod_eq_of_lt hj hjk

theorem signed_positions_surjective {j k : ℕ} (hjk : j.Coprime k)
    (hk : 0<k) (p : ℤ) : ∃n : ℤ,(n*(j:ℤ))%(k:ℤ)=p%(k:ℤ) := by
  let : NeZero k := ⟨ne_of_gt hk⟩
  obtain ⟨z,hz⟩ := (position_mul_bijective hjk).2 (p:ZMod k)
  refine ⟨z.val,?_⟩
  have he : (((z.val:ℤ)*(j:ℤ):ℤ):ZMod k)=(p:ZMod k) := by
    push_cast
    rw [ZMod.natCast_zmod_val,mul_comm]
    exact hz
  exact (ZMod.intCast_eq_intCast_iff ((z.val:ℤ)*(j:ℤ)) p k).mp he

end polyak.Farey
