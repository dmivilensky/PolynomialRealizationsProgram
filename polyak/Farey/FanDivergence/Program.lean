import polyak.Farey.FanDivergence.Trigonometric

/-! The literal finite fan program. The remaining residues are explicit
for arbitrary p, and disappear by proof, not assumption, for p=2. -/
noncomputable section
namespace polyak.Farey
open polyak.Levels

def fanLagSum (P : FanParameters) (Θ : Curve) (u v : ℝ) (n : ℤ) : ℝ :=
  u*Θ.lag n P.companion+v*Θ.lag n P.anchor

def FanFiniteProgram (P : FanParameters) (Θ : Curve) : Prop :=
  ∃u v : ℝ,0≤u ∧ 0≤v ∧ 0<u+v ∧
    0≤u*Θ.minimizer P.companion+v*Θ.minimizer P.anchor ∧
    ∀n : ℤ,0<n→n<P.k→0≤fanLagSum P Θ u v n

theorem grid_lag_add_period (Θ : Curve) (k i n : ℤ)
    (hk : 0<k) (hi : 0≤ i) (hik : 2*i≤k) :
    Θ.lag (n+k) (gridFrequency k i hk hi hik)=Θ.lag n (gridFrequency k i hk hi hik) := by
  rw [lag_at_grid_eq_positionValue,lag_at_grid_eq_positionValue]
  have he : (n+k)*i=n*i+k*i := by ring
  rw [he,Int.add_mul_emod_self_left]

namespace FanParameters

def parentResidue (P : FanParameters) : ℤ := (P.p-1)*P.K+1

theorem parentResidue_eq (P : FanParameters) : P.parentResidue= -P.K+P.k := by
  unfold parentResidue k
  ring

theorem parentResidue_bounds (P : FanParameters) : 1<P.parentResidue ∧ P.parentResidue<P.k := by
  rw [P.parentResidue_eq]
  have hh := mul_nonneg (sub_nonneg.mpr P.p_ge_two) (show 0≤P.K by linarith [P.K_ge_two])
  dsimp [k]
  constructor <;> nlinarith [P.K_ge_two]

theorem parentResidue_lag_anchor (P : FanParameters) (Θ : Curve) :
    Θ.lag P.parentResidue P.anchor=Θ.lag (-P.K) P.anchor := by
  rw [P.parentResidue_eq]
  exact grid_lag_add_period Θ P.k P.p (-P.K) P.k_pos P.p_pos.le P.two_p_lt_k.le

theorem parentResidue_lag_companion (P : FanParameters) (Θ : Curve) :
    Θ.lag P.parentResidue P.companion=Θ.lag (-P.K) P.companion := by
  rw [P.parentResidue_eq]
  exact grid_lag_add_period Θ P.k (P.p-1) (-P.K) P.k_pos P.companion_pos.le P.companion_le

theorem p2_parentResidue (P : FanParameters) (hp : P.p=2) : P.parentResidue=P.K+1 := by
  simp only [parentResidue,hp]
  ring

end FanParameters

theorem fan_finiteProgram_implies_pair (P : FanParameters) (Θ : Curve)
    (h : FanFiniteProgram P Θ) : FanPairFeasible P Θ := by
  obtain ⟨u,v,hu,hv,hne,_hmin,hlag⟩ := h
  apply (fanPairFeasible_iff_weights P Θ).mpr
  refine ⟨u,v,hu,hv,hne,hlag 1 (by norm_num) (by linarith [P.p_lt_k,P.p_ge_two]),?_⟩
  have hh := hlag P.parentResidue (by linarith [P.parentResidue_bounds.1]) P.parentResidue_bounds.2
  simpa only [fanLagSum,P.parentResidue_lag_companion,P.parentResidue_lag_anchor] using hh

theorem fan_finiteProgram_of_ratio (P : FanParameters) (Θ : Curve)
    (hmain : P.firstAngle<Θ P.anchor ∧ Θ P.anchor≤P.halfAnchor)
    (hcomp : P.halfCompanion<Θ P.companion ∧ Θ P.companion<P.companionAngle)
    (hcompHalf : Θ P.companion≤Real.pi/2) {r : ℝ}
    (hr : FanRatioAdmissible P Θ r)
    (hremaining : ∀n : ℤ,2≤n→n<P.k→n≠P.parentResidue→0≤fanLagSum P Θ r 1 n) :
    FanFiniteProgram P Θ := by
  have hrp := fan_admissible_ratio_pos P Θ hmain.1 hcomp.2 hr
  have hpair := (fan_ratio_constraints_iff P Θ hcomp r).mpr hr
  refine ⟨r,1,hrp.le,by norm_num,by linarith,P.minimizer_nonneg Θ hmain.2 hcompHalf hrp.le (by norm_num),?_⟩
  intro n hn hnk
  by_cases h1 : n=1
  · subst n
    simpa only [fanLagSum,one_mul] using hpair.1
  by_cases hpar : n=P.parentResidue
  · subst n
    simpa only [fanLagSum,P.parentResidue_lag_companion,P.parentResidue_lag_anchor,one_mul] using hpair.2
  · exact hremaining n (by omega) hnk hpar

theorem p2_finiteProgram_iff_determinant (P : FanParameters) (hp : P.p=2) (Θ : Curve)
    (hcomp : P.firstAngle<Θ P.companion ∧ Θ P.companion≤P.halfAnchor)
    (hmain : P.firstAngle<Θ P.anchor ∧ Θ P.anchor≤P.halfAnchor) :
    FanFiniteProgram P Θ ↔ 0≤fanDeterminant P Θ := by
  have hcompBounds : P.halfCompanion<Θ P.companion ∧ Θ P.companion<P.companionAngle := by
    refine ⟨by rw [P.p2_halfCompanion hp];exact hcomp.1,?_⟩
    have ha : P.halfAnchor<P.companionAngle := by
      have hkR : (0:ℝ)<P.k := by exact_mod_cast P.k_pos
      have hK : (2:ℝ)≤P.K := by exact_mod_cast P.K_ge_two
      rw [P.p2_halfAnchor hp]
      unfold FanParameters.companionAngle
      apply (div_lt_div_iff_of_pos_right hkR).mpr
      nlinarith [Real.pi_pos]
    exact hcomp.2.trans_lt ha
  constructor
  · intro h
    exact (fan_pair_determinant_iff P Θ hmain.1 hcompBounds).mp (fan_finiteProgram_implies_pair P Θ h)
  · intro hd
    obtain ⟨u,v,hu,hv,hne,h1,h2⟩ := (fanPairFeasible_iff_weights P Θ).mp
      ((fan_pair_determinant_iff P Θ hmain.1 hcompBounds).mpr hd)
    have hmin := P.minimizer_nonneg Θ hmain.2
      (hcomp.2.trans P.halfAnchor_bounds.2.le) hu hv
    refine ⟨u,v,hu,hv,hne,hmin,?_⟩
    intro n hn hnk
    by_cases h1n : n=1
    · subst n
      exact h1
    by_cases hpar : n=P.parentResidue
    · subst n
      simpa only [fanLagSum,P.parentResidue_lag_companion,P.parentResidue_lag_anchor] using h2
    · exact P.p2_remaining_weights hp Θ hcomp.2 hmain.2 hu hv (by omega) hnk
        (by simpa only [P.p2_parentResidue hp] using hpar)

theorem p2_finiteProgram_iff_displayed (P : FanParameters) (hp : P.p=2) (Θ : Curve)
    (hcomp : P.firstAngle<Θ P.companion ∧ Θ P.companion≤P.halfAnchor)
    (hmain : P.firstAngle<Θ P.anchor ∧ Θ P.anchor≤P.halfAnchor) :
    FanFiniteProgram P Θ ↔ 0≤fanP2Expression P Θ :=
  (p2_finiteProgram_iff_determinant P hp Θ hcomp hmain).trans (P.p2_determinant_iff_displayed hp Θ)

end polyak.Farey
