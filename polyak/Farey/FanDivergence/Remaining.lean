import polyak.Farey.FanDivergence.Determinant

/-! At depth at most two, the only bad position is one. For the
two-harmonic fan p=2 this proves every remaining lag automatically. -/
noncomputable section
namespace polyak.Farey
open polyak.Levels

theorem grid_lag_nonneg_unless_position_one (Θ : Curve) (k i n : ℤ)
    (hk : 0<k) (hi : 0≤ i) (hik : 2*i≤k)
    (hθ : Θ (gridFrequency k i hk hi hik)≤2*Real.pi/k)
    (hne : (n*i)%k≠1) : 0≤Θ.lag n (gridFrequency k i hk hi hik) := by
  rw [lag_at_grid_eq_positionValue]
  have hr0 : 0≤(n*i)%k := Int.emod_nonneg _ (ne_of_gt hk)
  have hrk : (n*i)%k<k := Int.emod_lt_of_pos _ hk
  by_cases hz : (n*i)%k=0
  · simp only [hz,Int.cast_zero,positionValue_zero,le_refl]
  have hr2 : 2≤(n*i)%k := by omega
  have ha2 : gridPhase Θ k i hk hi hik≤2 := by
    have hkR : (0:ℝ)<k := by exact_mod_cast hk
    dsimp [gridPhase]
    apply (div_le_iff₀ Real.pi_pos).mpr
    have hh := (le_div_iff₀ hkR).mp hθ
    nlinarith
  apply le_of_not_gt
  intro hneg
  have hh := (positionValue_neg_iff hk (gridPhase_pos Θ k i hk hi hik)
    (gridPhase_le Θ k i hk hi hik) (by exact_mod_cast (by omega : 0<(n*i)%k))
    (by exact_mod_cast hrk)).mp hneg
  have hr2R : (2:ℝ)≤((n*i)%k:ℤ) := by exact_mod_cast hr2
  linarith

theorem doubled_residue_one_iff {K n : ℤ} (hK : 2≤K)
    (hn : 0<n) (hnk : n<2*K+1) : (2*n)%(2*K+1)=1 ↔ n=K+1 := by
  have hk : 0<2*K+1 := by omega
  constructor
  · intro hr
    let d := (2*n)/(2*K+1)
    have hd0 : 0≤d := Int.ediv_nonneg (by omega) hk.le
    have hd2 : d<2 := (Int.ediv_lt_iff_lt_mul hk).mpr (by omega)
    have he : (2*n)%(2*K+1)+(2*K+1)*d=2*n := by
      simpa only [d,mul_comm] using Int.emod_add_ediv_mul (2*n) (2*K+1)
    rw [hr] at he
    have hd : d=0 ∨ d=1 := by omega
    rcases hd with hd|hd <;> rw [hd] at he <;> omega
  · rintro rfl
    have he : 2*(K+1)=1+(2*K+1) := by ring
    rw [he,Int.add_emod,Int.emod_self,add_zero,Int.emod_emod]
    exact Int.emod_eq_of_lt (by norm_num) (by omega)

namespace FanParameters

theorem p2_halfAnchor (P : FanParameters) (hp : P.p=2) :
    P.halfAnchor=2*Real.pi/P.k := by
  simp only [halfAnchor,hp,Int.cast_ofNat,mul_comm Real.pi (2:ℝ)]

theorem p2_remaining_nonneg (P : FanParameters) (hp : P.p=2) (Θ : Curve)
    (hcomp : Θ P.companion≤P.halfAnchor) (hmain : Θ P.anchor≤P.halfAnchor)
    {n : ℤ} (hn : 2≤n) (hnk : n<P.k) (hne : n≠P.K+1) :
    0≤Θ.lag n P.companion ∧ 0≤Θ.lag n P.anchor := by
  rw [P.p2_halfAnchor hp] at hcomp hmain
  have hk : P.k=2*P.K+1 := by simp only [k,hp]
  constructor
  · apply grid_lag_nonneg_unless_position_one Θ P.k (P.p-1) n P.k_pos
      P.companion_pos.le P.companion_le hcomp
    have he : P.p-1=1 := by omega
    rw [he,mul_one,Int.emod_eq_of_lt (by omega) hnk]
    omega
  · apply grid_lag_nonneg_unless_position_one Θ P.k P.p n P.k_pos
      P.p_pos.le P.two_p_lt_k.le hmain
    rw [hp,hk,mul_comm n 2]
    exact fun h=>hne ((doubled_residue_one_iff P.K_ge_two (by omega) (by simpa only [hk] using hnk)).mp h)

theorem p2_remaining_weights (P : FanParameters) (hp : P.p=2) (Θ : Curve)
    (hcomp : Θ P.companion≤P.halfAnchor) (hmain : Θ P.anchor≤P.halfAnchor)
    {u v : ℝ} (hu : 0≤u) (hv : 0≤v)
    {n : ℤ} (hn : 2≤n) (hnk : n<P.k) (hne : n≠P.K+1) :
    0≤u*Θ.lag n P.companion+v*Θ.lag n P.anchor := by
  have h := P.p2_remaining_nonneg hp Θ hcomp hmain hn hnk hne
  exact add_nonneg (mul_nonneg hu h.1) (mul_nonneg hv h.2)

end FanParameters
end polyak.Farey
