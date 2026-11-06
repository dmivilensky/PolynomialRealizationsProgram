import nesterov.Corner.Algebra

/-! The exact arithmetic gap in the source example (theta,a,b)=(3,2,1). -/
namespace nesterov.Corner
noncomputable section
open Set

theorem rationalXi_antitone {K L : ℕ} (hK : 3≤K) (hKL : K≤L) :
    rationalXi L≤rationalXi K := by
  have hk : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
  have hl : (0:ℝ)<L := by exact_mod_cast (by omega : 0<L)
  have hkl : (K:ℝ)≤L := by exact_mod_cast hKL
  have hk3 : (3:ℝ)≤K := by exact_mod_cast hK
  have harg : 2*Real.pi/(L:ℝ)≤2*Real.pi/(K:ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hk hkl
  have haπ : 2*Real.pi/(K:ℝ)≤Real.pi := by
    apply (div_le_iff₀ hk).mpr
    nlinarith [Real.pi_pos]
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity : 0≤2*Real.pi/(L:ℝ)) haπ harg
  unfold rationalXi
  linarith

theorem rationalXi_six : rationalXi 6=1/2 := by
  unfold rationalXi
  norm_num only [Nat.cast_ofNat]
  rw [show 2*Real.pi/(6:ℝ)=Real.pi/3 by ring,Real.cos_pi_div_three]
  norm_num

theorem rationalXi_five : rationalXi 5=(5-Real.sqrt 5)/4 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤5)
  unfold rationalXi
  norm_num only [Nat.cast_ofNat]
  rw [show 2*Real.pi/(5:ℝ)=2*(Real.pi/5) by ring,Real.cos_two_mul,Real.cos_pi_div_five]
  nlinarith

theorem rationalXi_five_ge : (3:ℝ)/5≤rationalXi 5 := by
  rw [rationalXi_five]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤5)
  have hp := Real.sqrt_nonneg (5:ℝ)
  nlinarith

theorem example_numerator (ξ : ℝ) : N 3 2 1 ξ=6*ξ^2-10*ξ+12 := by unfold N;ring

theorem example_difference (ξ : ℝ) :
    N 3 2 1 ξ-4*(3*Real.sqrt 6-13/2)*(3-ξ)=6*(ξ-(3-Real.sqrt 6))^2 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤6)
  unfold N
  nlinarith

theorem example_minimizer_between :
    rationalXi 6<3-Real.sqrt 6 ∧ 3-Real.sqrt 6<rationalXi 5 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤6)
  have hp := Real.sqrt_nonneg (6:ℝ)
  rw [rationalXi_six]
  constructor
  · nlinarith
  · have := rationalXi_five_ge
    nlinarith

theorem example_cLag : cLag 3 2 1=3*Real.sqrt 6-13/2 := by
  have hx : 3-Real.sqrt 6∈Icc (0:ℝ) 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤6)
    have hp := Real.sqrt_nonneg (6:ℝ)
    constructor <;> nlinarith
  have hl : 3*Real.sqrt 6-13/2≤cLag 3 2 1 := by
    apply le_cLag_iff.mpr
    intro ξ hξ
    have h := example_difference ξ
    nlinarith [sq_nonneg (ξ-(3-Real.sqrt 6))]
  have he : ratio 3 2 1 (3-Real.sqrt 6)=3*Real.sqrt 6-13/2 := by
    apply (div_eq_iff (by nlinarith [hx.2] : 4*(3-(3-Real.sqrt 6))≠0)).mpr
    have h := example_difference (3-Real.sqrt 6)
    simp only [sub_self,zero_pow (by omega : 2≠0),mul_zero] at h
    linarith
  exact le_antisymm (he ▸ cLag_le hx) hl

theorem example_discrete_difference (ξ : ℝ) :
    N 3 2 1 ξ-4*(17/20)*(3-ξ)=(3/5)*(5*ξ-3)*(2*ξ-1) := by unfold N;ring

theorem example_discrete_bound {K : ℕ} (hK : 3≤K) : 17/20≤ratio 3 2 1 (rationalXi K) := by
  apply (le_ratio_iff (rationalXi_mem K).2).mpr
  have hprod : 0≤(5*rationalXi K-3)*(2*rationalXi K-1) := by
    by_cases h6 : 6≤K
    · have h := rationalXi_antitone (K:=6) (L:=K) (by omega) h6
      rw [rationalXi_six] at h
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · have h := (rationalXi_antitone hK (show K≤5 by omega)).trans' rationalXi_five_ge
      exact mul_nonneg (by linarith) (by linarith)
  have h := example_discrete_difference (rationalXi K)
  nlinarith

theorem example_cDisc : cDisc 3 2 1=17/20 := by
  have hl : 17/20≤cDisc 3 2 1 := by
    apply le_cDisc
    intro ξ hξ
    rcases discreteSet_iff.mp hξ with rfl|rfl|⟨K,hK,rfl⟩
    · rw [ratio_zero]
      norm_num
    · rw [ratio_two,cpi]
      norm_num
    · exact example_discrete_bound hK
  have he : ratio 3 2 1 (rationalXi 6)=17/20 := by
    rw [rationalXi_six]
    norm_num [ratio,N]
  exact le_antisymm (he ▸ cDisc_le (rationalXi_mem_discreteSet (by omega : 3≤6))) hl

theorem example_strict_gap : cLag 3 2 1<cDisc 3 2 1 := by
  rw [example_cLag,example_cDisc]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤6)
  have hp := Real.sqrt_nonneg (6:ℝ)
  nlinarith

end
end nesterov.Corner
