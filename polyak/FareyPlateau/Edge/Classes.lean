import polyak.FareyPlateau.Edge.Basic

/-! Tight Farey classes independently of an adjacent-lag symbol. The
resonant slope cases are therefore included. -/
noncomputable section
namespace polyak.FareyPlateau.Edge
open Levels

theorem tight_classes_of_phase {j k : ℕ} (hk : 3≤k) (hjk : 2*j≤k)
    (Θ : Curve) (hp : Θ (atom j k (by omega) hjk)=Real.pi/k)
    (b : ℤ) (hb0 : 0<b) (hbk : b<k) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (n : ℤ) (ht : Θ.lag n (atom j k (by omega) hjk)=0) :
    n%(k:ℤ)=0 ∨ n%(k:ℤ)=b := by
  rw [lag_position_one (by omega) hjk Θ hp n] at ht
  have he := Farey.residue_transport_of_inverse (i:=1) hb n
  simp only [mul_one,one_mul] at he
  by_cases hz : (n*j)%k=0
  · left
    simpa only [hz,mul_zero,Int.zero_emod] using he
  · right
    have hkZ : (0:ℤ)<k := by omega
    have hp0 : 0<(n*j)%k := by have :=Int.emod_nonneg (n*j) hkZ.ne'; omega
    have hρ : (((n*j)%k:ℤ):ℝ)=1 :=
      (Farey.positionValue_eq_zero_iff hkZ (by norm_num)
        (by exact_mod_cast (show 1≤k by omega))
        (by exact_mod_cast hp0) (by exact_mod_cast Int.emod_lt_of_pos (n*j) hkZ)).mp ht
    have hρZ : (n*j)%k=1 := by exact_mod_cast hρ
    simpa only [hρZ,mul_one,Int.emod_eq_of_lt hb0.le hbk] using he

end polyak.FareyPlateau.Edge
