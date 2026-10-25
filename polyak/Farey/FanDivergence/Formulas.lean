import polyak.Farey.Positions.Basic
import polyak.Farey.FanDivergence.TwoLag

/-! The four exact lag values at consecutive fan harmonics. -/
noncomputable section
namespace polyak.Farey
open polyak.Levels Set

structure FanParameters where
  K : ℤ
  p : ℤ
  K_ge_two : 2≤K
  p_ge_two : 2≤p

namespace FanParameters

def k (P : FanParameters) : ℤ := P.p*P.K+1

theorem k_pos (P : FanParameters) : 0<P.k := by
  dsimp [k]
  nlinarith [P.K_ge_two,P.p_ge_two]

theorem p_pos (P : FanParameters) : 0<P.p := by linarith [P.p_ge_two]
theorem companion_pos (P : FanParameters) : 0<P.p-1 := by linarith [P.p_ge_two]

theorem two_p_lt_k (P : FanParameters) : 2*P.p<P.k := by
  have hh := mul_nonneg P.p_pos.le (sub_nonneg.mpr P.K_ge_two)
  dsimp [k]
  nlinarith

theorem p_lt_k (P : FanParameters) : P.p<P.k := by linarith [P.two_p_lt_k,P.p_pos]

theorem companion_le (P : FanParameters) : 2*(P.p-1)≤P.k := by linarith [P.two_p_lt_k]

theorem K_add_one_lt_k (P : FanParameters) : P.K+1<P.k := by
  have hh := mul_nonneg (sub_nonneg.mpr P.p_ge_two) (show 0≤P.K by linarith [P.K_ge_two])
  dsimp [k]
  nlinarith [P.K_ge_two]

def anchor (P : FanParameters) : Frequency :=
  gridFrequency P.k P.p P.k_pos P.p_pos.le P.two_p_lt_k.le

def companion (P : FanParameters) : Frequency :=
  gridFrequency P.k (P.p-1) P.k_pos P.companion_pos.le P.companion_le

def halfAnchor (P : FanParameters) : ℝ := Real.pi*P.p/P.k
def halfCompanion (P : FanParameters) : ℝ := Real.pi*(P.p-1)/P.k
def firstAngle (P : FanParameters) : ℝ := Real.pi/P.k
def companionAngle (P : FanParameters) : ℝ := Real.pi*(P.K+1)/P.k

theorem angle_pos_lt_pi {k i : ℤ} (hk : 0<k) (hi : 0 < i) (hik : i < k) :
    0<Real.pi*i/k ∧ Real.pi*i/k<Real.pi := by
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hiR : (0:ℝ)< i := by exact_mod_cast hi
  have hikR : (i:ℝ)<k := by exact_mod_cast hik
  exact ⟨by positivity,(div_lt_iff₀ hkR).mpr (by nlinarith [Real.pi_pos])⟩

theorem firstAngle_bounds (P : FanParameters) : 0<P.firstAngle ∧ P.firstAngle<Real.pi := by
  simpa only [firstAngle,mul_one,Int.cast_one] using angle_pos_lt_pi P.k_pos
    (show (0:ℤ)<1 by norm_num) (by linarith [P.p_lt_k,P.p_ge_two])

theorem halfAnchor_bounds (P : FanParameters) : 0<P.halfAnchor ∧ P.halfAnchor<Real.pi/2 := by
  have hkR : (0:ℝ)<P.k := by exact_mod_cast P.k_pos
  have hpR : (0:ℝ)<P.p := by exact_mod_cast P.p_pos
  have h2R : (2:ℝ)*P.p<P.k := by exact_mod_cast P.two_p_lt_k
  exact ⟨by dsimp [halfAnchor]; positivity,by
    dsimp [halfAnchor]
    apply (div_lt_iff₀ hkR).mpr
    nlinarith [Real.pi_pos]⟩

theorem halfCompanion_bounds (P : FanParameters) :
    0<P.halfCompanion ∧ P.halfCompanion<Real.pi := by
  simpa only [halfCompanion,Int.cast_sub,Int.cast_one] using
    angle_pos_lt_pi P.k_pos P.companion_pos (by linarith [P.p_lt_k])

theorem companionAngle_bounds (P : FanParameters) :
    0<P.companionAngle ∧ P.companionAngle<Real.pi := by
  simpa only [companionAngle,Int.cast_add,Int.cast_one] using angle_pos_lt_pi P.k_pos
    (show 0<P.K+1 by linarith [P.K_ge_two]) P.K_add_one_lt_k

theorem anchor_parent_position (P : FanParameters) : (-P.K*P.p)%P.k=1 := by
  have he : -P.K*P.p=1-P.k := by dsimp [k];ring
  rw [he,Int.sub_emod,Int.emod_self,sub_zero,Int.emod_emod]
  exact Int.emod_eq_of_lt (by norm_num) (by linarith [P.p_lt_k,P.p_ge_two])

theorem companion_parent_position (P : FanParameters) : (-P.K*(P.p-1))%P.k=P.K+1 := by
  have he : -P.K*(P.p-1)=(P.K+1)-P.k := by dsimp [k];ring
  rw [he,Int.sub_emod,Int.emod_self,sub_zero,Int.emod_emod]
  exact Int.emod_eq_of_lt (by linarith [P.K_ge_two]) P.K_add_one_lt_k

end FanParameters

theorem grid_lag_sine_of_position (Θ : Curve) (k i n ρ : ℤ)
    (hk : 0<k) (hi : 0 ≤ i) (hik : 2*i ≤ k) (hρ : (n*i)%k=ρ) :
    Θ.lag n (gridFrequency k i hk hi hik)=
      2*Real.sin (Real.pi*ρ/k)*
        Real.sin (Real.pi*ρ/k-Θ (gridFrequency k i hk hi hik)) := by
  rw [lag_at_grid_eq_positionValue,hρ]
  have hkR : (k:ℝ)≠0 := by exact_mod_cast (ne_of_gt hk)
  have he : Real.pi*((ρ:ℝ)-gridPhase Θ k i hk hi hik)/k=
      Real.pi*ρ/k-Θ (gridFrequency k i hk hi hik) := by
    unfold gridPhase
    field_simp
  exact congrArg (fun t=>2*Real.sin (Real.pi*ρ/k)*Real.sin t) he

namespace FanParameters

theorem anchor_lag_one (P : FanParameters) (Θ : Curve) :
    Θ.lag 1 P.anchor=2*Real.sin P.halfAnchor*Real.sin (P.halfAnchor-Θ P.anchor) := by
  exact grid_lag_sine_of_position Θ P.k P.p 1 P.p P.k_pos P.p_pos.le P.two_p_lt_k.le
    (by rw [one_mul]; exact Int.emod_eq_of_lt P.p_pos.le P.p_lt_k)

theorem anchor_lag_parent (P : FanParameters) (Θ : Curve) :
    Θ.lag (-P.K) P.anchor=2*Real.sin P.firstAngle*Real.sin (P.firstAngle-Θ P.anchor) := by
  simpa only [anchor,firstAngle,Int.cast_one,mul_one] using
    grid_lag_sine_of_position Θ P.k P.p (-P.K) 1 P.k_pos P.p_pos.le P.two_p_lt_k.le P.anchor_parent_position

theorem companion_lag_one (P : FanParameters) (Θ : Curve) :
    Θ.lag 1 P.companion=2*Real.sin P.halfCompanion*Real.sin (P.halfCompanion-Θ P.companion) := by
  simpa only [companion,halfCompanion,Int.cast_sub,Int.cast_one] using
    grid_lag_sine_of_position Θ P.k (P.p-1) 1 (P.p-1) P.k_pos P.companion_pos.le P.companion_le
      (by rw [one_mul]; exact Int.emod_eq_of_lt P.companion_pos.le (by linarith [P.p_lt_k]))

theorem companion_lag_parent (P : FanParameters) (Θ : Curve) :
    Θ.lag (-P.K) P.companion=2*Real.sin P.companionAngle*Real.sin (P.companionAngle-Θ P.companion) := by
  simpa only [companion,companionAngle,Int.cast_add,Int.cast_one] using
    grid_lag_sine_of_position Θ P.k (P.p-1) (-P.K) (P.K+1) P.k_pos P.companion_pos.le P.companion_le
      P.companion_parent_position

end FanParameters
end polyak.Farey
