import polyak.Farey.Geometry.Fans
import polyak.Levels.Lattice.Atoms

/-! The two gap-window spines, their exact neighbours, and every signed
line through the first integer point. -/
noncomputable section
namespace polyak.Farey

def fanDenominator (K p : ℤ) : ℤ := p*K+1
def upperSpine (K m : ℤ) : ℤ×ℤ := (m+1,K+m*(K+1))

theorem fanDenominator_pos {K p : ℤ} (hK : 2≤K) (hp : 1≤p) : 0<fanDenominator K p := by
  dsimp [fanDenominator]
  nlinarith

def spineParents (K p : ℤ) (hK : 2≤K) (hp : 2≤p) : ParentData p (fanDenominator K p) where
  a:=p-1
  b:=fanDenominator K (p-1)
  c:=1
  d:=K
  numerator:=by ring
  denominator:=by dsimp [fanDenominator]; ring
  determinant:=by dsimp [fanDenominator]; ring
  b_pos:=fanDenominator_pos hK (by omega)
  d_pos:=by omega

theorem lower_spine_neighbors (K p : ℤ) :
    fanDenominator K p*(p+1)-p*fanDenominator K (p+1)=1 := by
  dsimp [fanDenominator]
  ring

theorem spine_anchor_neighbors (K p : ℤ) : fanDenominator K p-p*K=1 := by
  dsimp [fanDenominator]
  ring

theorem lower_spine_coprime (K p : ℤ) : IsCoprime p (fanDenominator K p) :=
  ⟨-K,1,by dsimp [fanDenominator]; ring⟩

theorem upper_spine_coprime (K m : ℤ) : IsCoprime (upperSpine K m).1 (upperSpine K m).2 :=
  ⟨K+1,-1,by dsimp [upperSpine]; ring⟩

theorem upper_spine_neighbors (K m : ℤ) :
    (upperSpine K m).1*(upperSpine K (m+1)).2-
      (upperSpine K m).2*(upperSpine K (m+1)).1=1 := by
  dsimp [upperSpine]
  ring

theorem lower_spine_lattice (K p : ℤ) : -K*p+fanDenominator K p=1 := by
  dsimp [fanDenominator]
  ring

theorem upper_spine_lattice (K m : ℤ) :
    (K+1)*(upperSpine K m).1-(upperSpine K m).2=1 := by
  dsimp [upperSpine]
  ring

theorem lower_spine_in_window {K p : ℤ} (hK : 2≤K) (hp : 2≤p) :
    1/((K:ℝ)+1)<(p:ℝ)/fanDenominator K p ∧ (p:ℝ)/fanDenominator K p<1/(K:ℝ) := by
  have hk : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have hd : (0:ℝ)<fanDenominator K p := by exact_mod_cast fanDenominator_pos hK (by omega : 1≤p)
  have he : (fanDenominator K p:ℝ)=p*K+1 := by simp [fanDenominator]
  constructor
  · rw [div_lt_div_iff₀ (by linarith : (0:ℝ)<K+1) hd]
    nlinarith
  · rw [div_lt_div_iff₀ hd hk]
    nlinarith

theorem upper_spine_in_window {K m : ℤ} (hK : 2≤K) (hm : 1≤m) :
    1/((K:ℝ)+1)<((upperSpine K m).1:ℝ)/(upperSpine K m).2 ∧
      ((upperSpine K m).1:ℝ)/(upperSpine K m).2<1/(K:ℝ) := by
  have hk : (2:ℝ)≤K := by exact_mod_cast hK
  have hm' : (1:ℝ)≤m := by exact_mod_cast hm
  have hd : (0:ℝ)<K+m*(K+1) := by nlinarith
  simp only [upperSpine,Int.cast_add,Int.cast_one,Int.cast_mul]
  constructor
  · rw [div_lt_div_iff₀ (by linarith : (0:ℝ)<K+1) hd]
    nlinarith
  · rw [div_lt_div_iff₀ hd (by linarith : (0:ℝ)<K)]
    nlinarith

theorem fan_anchor_inverse {K p : ℤ} (hK : 2≤K) (hp : 2≤p) :
    ((-K)*p)%fanDenominator K p=1 := by
  have hd : 1<fanDenominator K p := by dsimp [fanDenominator]; nlinarith
  rw [show (-K)*p=1+(-1)*fanDenominator K p by dsimp [fanDenominator]; ring,
    Int.add_mul_emod_self_right,Int.emod_eq_of_lt (by omega) hd]

theorem fan_companion_position {K p : ℤ} (hK : 2≤K) (hp : 2≤p) :
    ((-K)*(p-1))%fanDenominator K p=K+1 := by
  have hd : K+1<fanDenominator K p := by dsimp [fanDenominator]; nlinarith
  rw [show (-K)*(p-1)=(K+1)+(-1)*fanDenominator K p by dsimp [fanDenominator]; ring,
    Int.add_mul_emod_self_right,Int.emod_eq_of_lt (by omega) hd]

theorem fan_previous_den_congruence (K p : ℤ) :
    fanDenominator K (p-1) ≡ -K [ZMOD fanDenominator K p] := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-1,?_⟩
  dsimp [fanDenominator]
  ring

theorem line_through_first_point (K n ℓ : ℤ) : n-ℓ*K=1 ↔ n=ℓ*K+1 := by omega

theorem first_point_line_fan (K m : ℤ) :
    (m*K+1)*(m+1)-m*fanDenominator K (m+1)=1 := by dsimp [fanDenominator]; ring

theorem lower_spine_phase (K p : ℤ) (hd : fanDenominator K p≠0) :
    Real.pi-(K:ℝ)*(2*Real.pi*p/fanDenominator K p)/2=Real.pi/fanDenominator K p := by
  have hd' : (fanDenominator K p:ℝ)≠0 := by exact_mod_cast hd
  have he : (fanDenominator K p:ℝ)=(p:ℝ)*K+1 := by simp [fanDenominator]
  generalize (fanDenominator K p:ℝ)=d at *
  field_simp [hd']
  linear_combination he

theorem upper_spine_phase (K m : ℤ) (hd : (upperSpine K m).2≠0) :
    ((K:ℝ)+1)*(2*Real.pi*(upperSpine K m).1/(upperSpine K m).2)/2-Real.pi=
      Real.pi/(upperSpine K m).2 := by
  have hd' : ((upperSpine K m).2:ℝ)≠0 := by exact_mod_cast hd
  have he : ((upperSpine K m).2:ℝ)=(K:ℝ)+(m:ℝ)*(K+1) := by simp [upperSpine]
  have hn : ((upperSpine K m).1:ℝ)=(m:ℝ)+1 := by simp [upperSpine]
  rw [hn]
  generalize ((upperSpine K m).2:ℝ)=d at *
  field_simp [hd']
  linear_combination -he

end polyak.Farey
