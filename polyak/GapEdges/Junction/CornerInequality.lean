import polyak.GapEdges.Junction.TrigonometricBounds

/-! The strict junction inequality for all periods. The analytic tail uses
concavity rather than a truncated numerical search. -/
noncomputable section
namespace polyak.GapEdges.Junction
open Real

def junctionU (m : ℝ) : ℝ :=
  1-Real.sin (Real.pi/m)^2/Real.sin (Real.pi/(m-1))^2

def tailLower (m : ℝ) : ℝ :=
  (2*m-1)*(2*(m-1)^2-987/100)/(2*m^2*(m-1)^2)

theorem pi_sq_upper : Real.pi^2 < (987:ℝ)/100 := by
  nlinarith [Real.pi_lt_d4,Real.pi_pos]

theorem tailLower_pos {m : ℝ} (hm : 6 ≤ m) : 0<tailLower m := by
  have hm1 : 5 ≤ m-1 := by linarith
  have hs : 25 ≤ (m-1)^2 := by nlinarith
  unfold tailLower
  exact div_pos (mul_pos (by linarith) (by nlinarith)) (by positivity)

theorem corner_tail_algebra {m u : ℝ} (hm : 6 ≤ m)
    (hl : tailLower m ≤ u) (hu : u ≤ 2/m) :
    4*u+2/u+1/2 < m+4 := by
  have hmp : 0<m := by linarith
  have hm1 : 0<m-1 := by linarith
  have hb := tailLower_pos hm
  have hup : 0<u := hb.trans_le hl
  have hdiv : 2/u ≤ 2/tailLower m := by
    exact div_le_div_of_nonneg_left (by norm_num) hb hl
  have hpoly : 0<(3007:ℝ)/100+422981/200*(m-6)+57473/50*(m-6)^2+
      10263/50*(m-6)^3+12*(m-6)^4 := by positivity
  have he : (m+7/2-8/m)*tailLower m-2 =
      (3007/100+422981/200*(m-6)+57473/50*(m-6)^2+
        10263/50*(m-6)^3+12*(m-6)^4)/(2*m^3*(m-1)^2) := by
    unfold tailLower
    field_simp
    ring
  have hg : 2/tailLower m < m+7/2-8/m := by
    apply (div_lt_iff₀ hb).mpr
    have hp : 0< (m+7/2-8/m)*tailLower m-2 := by
      rw [he]
      exact div_pos hpoly (by positivity)
    linarith
  have hfour : 4*u ≤ 8/m := by calc
    _ ≤ 4*(2/m) := mul_le_mul_of_nonneg_left hu (by norm_num)
    _ = _ := by ring
  linarith

theorem junctionU_tail_bounds {m : ℝ} (hm : 6 ≤ m) :
    tailLower m ≤ junctionU m ∧ junctionU m ≤ 2/m := by
  have hmp : 0<m := by linarith
  have hm1 : 0<m-1 := by linarith
  have hx : 0<Real.pi/m := div_pos Real.pi_pos hmp
  have hy : 0<Real.pi/(m-1) := div_pos Real.pi_pos hm1
  have hxy : Real.pi/m ≤ Real.pi/(m-1) :=
    div_le_div_of_nonneg_left Real.pi_pos.le hm1 (by linarith)
  have hyhalf : Real.pi/(m-1)<Real.pi/2 := by
    exact div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by linarith)
  have h := sine_ratio_square_bounds hx.le hxy hy hyhalf
  have he : (Real.pi/m)/(Real.pi/(m-1)) = (m-1)/m := by field_simp
  rw [he,div_pow] at h
  have hone : 0 ≤ 1-((m-1)/m)^2 := by
    have ht : (m-1)/m≤1 := (div_le_one hmp).mpr (by linarith)
    have ht0 : 0≤(m-1)/m := div_nonneg hm1.le hmp.le
    nlinarith
  have hcos : 1-(987/100)/(2*(m-1)^2) ≤ Real.cos (Real.pi/(m-1)) := by
    have hp := pi_sq_upper.le
    have hh := div_le_div_of_nonneg_right hp (by positivity : 0≤2*(m-1)^2)
    have heq : (Real.pi/(m-1))^2/2=Real.pi^2/(2*(m-1)^2) := by field_simp
    have hc := Real.one_sub_sq_div_two_le_cos (x:=Real.pi/(m-1))
    rw [heq] at hc
    linarith
  constructor
  · have hp := mul_le_mul_of_nonneg_left hcos hone
    have heq : (1-((m-1)/m)^2)*(1-(987/100)/(2*(m-1)^2))=tailLower m := by
      unfold tailLower
      field_simp
      ring
    rw [heq] at hp
    exact hp.trans (by simpa only [div_pow,junctionU] using h.1)
  · have hh : 1-((m-1)/m)^2 ≤ 2/m := by
      have hid : 2/m-(1-((m-1)/m)^2)=1/m^2 := by field_simp; ring
      have hp : 0≤1/m^2 := by positivity
      linarith
    exact (show junctionU m ≤ 1-((m-1)/m)^2 from by
      simpa only [div_pow,junctionU] using h.2).trans hh

def junctionT (m : ℝ) : ℝ := Real.cos (2*Real.pi/m)

theorem corner_inequality_tail {m : ℝ} (hm : 6 ≤ m) :
    4*junctionU m+2/junctionU m+junctionT m/(1+junctionT m) < m+4 := by
  have hmp : 0<m := by linarith
  have htpos : 0<2*Real.pi/m := by positivity
  have htpi : 2*Real.pi/m < Real.pi := by
    apply (div_lt_iff₀ hmp).mpr
    nlinarith [Real.pi_pos]
  have ht : junctionT m<1 := by
    simpa only [junctionT,Real.cos_zero] using
      Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0) htpi.le htpos
  have ht0 : 0≤junctionT m := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · linarith
    · apply (div_le_iff₀ hmp).mpr
      nlinarith [Real.pi_pos]
  have hfrac : junctionT m/(1+junctionT m)<1/2 := by
    apply (div_lt_iff₀ (by linarith : 0<1+junctionT m)).mpr
    linarith
  obtain ⟨hl,hu⟩ := junctionU_tail_bounds hm
  linarith [corner_tail_algebra hm hl hu]

theorem junctionU_four : junctionU 4=1/3 := by
  unfold junctionU
  norm_num only [show (4:ℝ)-1=3 by norm_num]
  rw [Real.sin_pi_div_four,Real.sq_sin_pi_div_three,div_pow,
    Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  norm_num

theorem junctionT_four : junctionT 4=0 := by
  unfold junctionT
  rw [show 2*Real.pi/4=Real.pi/2 by ring,Real.cos_pi_div_two]

theorem junctionT_five : junctionT 5=(Real.sqrt 5-1)/4 := by
  have he := Real.cos_two_mul (Real.pi/5)
  rw [Real.cos_pi_div_five] at he
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤5)
  dsimp [junctionT]
  rw [show 2*Real.pi/5=2*(Real.pi/5) by ring,he]
  nlinarith

theorem junctionU_five : junctionU 5=junctionT 5 := by
  have he := Real.cos_two_mul (Real.pi/5)
  have hs := Real.sin_sq_add_cos_sq (Real.pi/5)
  have hr := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  dsimp [junctionU,junctionT]
  norm_num only [show (5:ℝ)-1=4 by norm_num]
  rw [Real.sin_pi_div_four,div_pow,hr]
  rw [show 2*Real.pi/5=2*(Real.pi/5) by ring]
  nlinarith

/-- Appendix I, lemma cornerineq, with the article's original quantifier. -/
theorem corner_inequality (m : ℕ) (hm : 4≤m) :
    4*junctionU m+2/junctionU m+junctionT m/(1+junctionT m) < (m:ℝ)+4 := by
  rcases (show m=4 ∨ m=5 ∨ 6≤m by omega) with rfl|rfl|h6
  · norm_num [junctionU_four,junctionT_four]
  · norm_num only [Nat.cast_ofNat]
    rw [junctionU_five,junctionT_five]
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤5)
    have hp := Real.sqrt_nonneg (5:ℝ)
    have hlow : 1<Real.sqrt 5 := by nlinarith
    have hupp : Real.sqrt 5<5/2 := by nlinarith
    have hlow2 : (223:ℝ)/100<Real.sqrt 5 := by nlinarith
    have ht : 0<(Real.sqrt 5-1)/4 := by linarith
    have hd : 2/((Real.sqrt 5-1)/4)<800/123 := by
      apply (div_lt_iff₀ ht).mpr
      linarith
    have hf : ((Real.sqrt 5-1)/4)/(1+(Real.sqrt 5-1)/4)<1/2 := by
      apply (div_lt_iff₀ (by linarith : 0<1+(Real.sqrt 5-1)/4)).mpr
      linarith
    linarith
  · exact corner_inequality_tail (by exact_mod_cast h6)

end polyak.GapEdges.Junction
