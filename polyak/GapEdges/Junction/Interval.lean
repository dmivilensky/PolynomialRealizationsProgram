import polyak.GapEdges.Junction.CornerInequality

/-! Nonemptiness of the explicit junction interval for every K≥3. -/
noncomputable section
namespace polyak.GapEdges.Junction
open Set Real

def junctionLower (t₁ t₂ : ℝ) : ℝ := 2/((1-t₁)*(1-t₂))
def junctionUpper (m t₁ t₂ s : ℝ) : ℝ :=
  (m+2-2*(1-t₁)/(t₁-t₂)-t₁/(1+t₁))/(4*(t₁-t₂)*s^2)

theorem junction_trig_bounds {m : ℝ} (hm : 4≤m) :
    0≤junctionT m ∧ junctionT m<1 ∧ junctionT (m-1)<junctionT m ∧
    junctionU m=(junctionT m-junctionT (m-1))/(1-junctionT (m-1)) := by
  have hmp : 0<m := by linarith
  have hm1 : 0<m-1 := by linarith
  have hp : 0<2*Real.pi/m := by positivity
  have hp1 : 0<2*Real.pi/(m-1) := by positivity
  have hpπ : 2*Real.pi/(m-1)<Real.pi := by
    apply (div_lt_iff₀ hm1).mpr
    nlinarith [Real.pi_pos]
  have hh : 2*Real.pi/m≤Real.pi/2 := by
    apply (div_le_iff₀ hmp).mpr
    nlinarith [Real.pi_pos]
  have hlt : 2*Real.pi/m<2*Real.pi/(m-1) :=
    div_lt_div_of_pos_left (by positivity) hm1 (by linarith)
  refine ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith,hh⟩,?_,?_,?_⟩
  · simpa [junctionT] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (by norm_num : (0:ℝ)≤0) (hlt.le.trans hpπ.le) hp
  · exact Real.cos_lt_cos_of_nonneg_of_le_pi hp.le hpπ.le hlt
  · have hy : 0<Real.pi/(m-1) := by positivity
    have hyπ : Real.pi/(m-1)<Real.pi := by
      apply (div_lt_iff₀ hm1).mpr
      nlinarith [Real.pi_pos]
    have hs := Real.sin_pos_of_pos_of_lt_pi hy hyπ
    have ht₁ : junctionT m=1-2*Real.sin (Real.pi/m)^2 := by
      unfold junctionT
      rw [show 2*Real.pi/m=2*(Real.pi/m) by ring,Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi/m)]
    have ht₂ : junctionT (m-1)=1-2*Real.sin (Real.pi/(m-1))^2 := by
      unfold junctionT
      rw [show 2*Real.pi/(m-1)=2*(Real.pi/(m-1)) by ring,Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi/(m-1))]
    rw [ht₁,ht₂,show 1-(1-2*Real.sin (Real.pi/(m-1))^2)=2*Real.sin (Real.pi/(m-1))^2 by ring]
    unfold junctionU
    generalize Real.sin (Real.pi/m)=X
    generalize Real.sin (Real.pi/(m-1))=Y at *
    field_simp
    ring

theorem junction_interval_nonempty (m : ℕ) (hm : 4≤m) :
    junctionLower (junctionT m) (junctionT ((m:ℝ)-1)) <
      junctionUpper m (junctionT m) (junctionT ((m:ℝ)-1)) (Real.sin (Real.pi/m)) := by
  have hmr : (4:ℝ)≤m := by exact_mod_cast hm
  obtain ⟨ht0,ht1,ht₂,hu⟩ := junction_trig_bounds hmr
  have hd : 0<junctionT m-junctionT ((m:ℝ)-1) := sub_pos.mpr ht₂
  have h1 : 0<1-junctionT m := by linarith
  have h2 : 0<1-junctionT ((m:ℝ)-1) := by linarith
  have hs : 0<Real.sin (Real.pi/m) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    apply (div_lt_iff₀ (by linarith : (0:ℝ)<m)).mpr
    nlinarith [Real.pi_pos]
  have hsin : 2*Real.sin (Real.pi/m)^2=1-junctionT m := by
    unfold junctionT
    rw [show 2*Real.pi/m=2*(Real.pi/m) by ring,Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi/m)]
  have he₁ : 4*junctionLower (junctionT m) (junctionT ((m:ℝ)-1))*
      (junctionT m-junctionT ((m:ℝ)-1))*Real.sin (Real.pi/m)^2=4*junctionU m := by
    rw [hu,junctionLower]
    field_simp
    nlinarith [hsin]
  have he₂ : 2*(1-junctionT m)/(junctionT m-junctionT ((m:ℝ)-1))=2/junctionU m-2 := by
    rw [hu]
    field_simp
    ring
  have hineq := corner_inequality m hm
  apply (lt_div_iff₀ (by positivity : 0<4*(junctionT m-junctionT ((m:ℝ)-1))*Real.sin (Real.pi/m)^2)).mpr
  change junctionLower (junctionT m) (junctionT ((m:ℝ)-1))*
    (4*(junctionT m-junctionT ((m:ℝ)-1))*Real.sin (Real.pi/m)^2)<_
  have he₁' := he₁
  rw [show 4*junctionLower (junctionT m) (junctionT ((m:ℝ)-1))*
    (junctionT m-junctionT ((m:ℝ)-1))*Real.sin (Real.pi/m)^2=
      junctionLower (junctionT m) (junctionT ((m:ℝ)-1))*
        (4*(junctionT m-junctionT ((m:ℝ)-1))*Real.sin (Real.pi/m)^2) by ring] at he₁'
  linarith

end polyak.GapEdges.Junction
