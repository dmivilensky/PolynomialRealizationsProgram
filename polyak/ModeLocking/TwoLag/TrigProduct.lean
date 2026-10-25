import polyak.ModeLocking.TwoLag.Factor

/-! The all-degree trigonometric sign product in part (d). -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General Levels
open Spectral (chebT chebU chebT_cos chebU_sin)

def signProduct (K : ℕ) (u : ℝ) : ℝ :=
  Real.sin ((K : ℝ)*u/2)*Real.sin (((K : ℝ)+1)*u/2)

theorem U_add_W_product {K : ℕ} (hK : 1≤K) (u : ℝ) :
    (chebU (K-1) (Real.cos u)+W K (Real.cos u))*
      (Real.sin (u/2)^2*Real.cos (u/2))=signProduct K u := by
  have hU : chebU (K-1) (Real.cos u)*Real.sin u = Real.sin ((K : ℝ)*u) := by
    have h := chebU_sin (K-1) u
    have hn : (((K-1 : ℕ) : ℝ)+1)=(K : ℝ) := by rw [Nat.cast_sub hK]; ring
    simpa only [hn] using h
  have hW := W_identity K (Real.cos u)
  rw [chebT_cos] at hW
  have hsin : Real.sin u=2*Real.sin (u/2)*Real.cos (u/2) := by
    convert Real.sin_two_mul (u/2) using 1
    congr 1
    ring
  have hKsin : Real.sin ((K : ℝ)*u)=
      2*Real.sin ((K : ℝ)*u/2)*Real.cos ((K : ℝ)*u/2) := by
    convert Real.sin_two_mul ((K : ℝ)*u/2) using 1
    congr 1
    ring
  have hcos : 1-Real.cos u=2*Real.sin (u/2)^2 := by
    have h := Real.cos_two_mul (u/2)
    rw [show 2*(u/2)=u by ring] at h
    nlinarith [Real.sin_sq_add_cos_sq (u/2)]
  have hKcos : 1-Real.cos ((K : ℝ)*u)=2*Real.sin ((K : ℝ)*u/2)^2 := by
    have h := Real.cos_two_mul ((K : ℝ)*u/2)
    rw [show 2*((K : ℝ)*u/2)=(K : ℝ)*u by ring] at h
    nlinarith [Real.sin_sq_add_cos_sq ((K : ℝ)*u/2)]
  have hw : W K (Real.cos u)*Real.sin (u/2)^2 = Real.sin ((K : ℝ)*u/2)^2 := by
    rw [hcos, hKcos] at hW
    nlinarith [hW]
  have hu' : chebU (K-1) (Real.cos u)*Real.sin (u/2)*Real.cos (u/2)=
      Real.sin ((K : ℝ)*u/2)*Real.cos ((K : ℝ)*u/2) := by
    rw [hsin, hKsin] at hU
    nlinarith [hU]
  unfold signProduct
  rw [show ((K : ℝ)+1)*u/2=(K : ℝ)*u/2+u/2 by ring, Real.sin_add]
  linear_combination Real.sin (u/2)*hu'+Real.cos (u/2)*hw


theorem half_den_pos {u : ℝ} (hu : 0<u ∧ u<Real.pi) :
    0<Real.sin (u/2)^2*Real.cos (u/2) := by
  apply mul_pos
  · exact sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
  · exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩

theorem signProduct_window {K : ℕ} (hK : 2≤K) {u : ℝ}
    (hlo : 2*Real.pi/((K : ℝ)+1)<u) (hhi : u<2*Real.pi/(K : ℝ)) :
    signProduct K u<0 := by
  have hk : (0 : ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hku : (K : ℝ)*u<2*Real.pi := by
    have h := (lt_div_iff₀ hk).mp hhi
    nlinarith [h]
  have hlu : 2*Real.pi<((K : ℝ)+1)*u := by
    have h := (div_lt_iff₀ (by linarith : (0 : ℝ)<(K : ℝ)+1)).mp hlo
    nlinarith [h]
  have hu : 0<u := by nlinarith [Real.pi_pos]
  have hfirst : 0<Real.sin ((K : ℝ)*u/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hlast : ((K : ℝ)+1)*u/2<2*Real.pi := by
    have hK1 : (1 : ℝ)≤K := by exact_mod_cast (show 1≤K by omega)
    nlinarith [mul_nonneg (sub_nonneg.mpr hK1) hu.le]
  have hsecond : Real.sin (((K : ℝ)+1)*u/2)<0 := by
    have h := Real.sin_pos_of_pos_of_lt_pi (show 0<((K : ℝ)+1)*u/2-Real.pi by linarith)
      (show ((K : ℝ)+1)*u/2-Real.pi<Real.pi by linarith)
    rw [Real.sin_sub_pi] at h
    linarith
  exact mul_neg_of_pos_of_neg hfirst hsecond

theorem signProduct_below {K : ℕ} (hK : 1≤K) {u : ℝ} (hu : 0<u)
    (hhi : u<2*Real.pi/((K : ℝ)+1)) : 0<signProduct K u := by
  have hk : (0 : ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hku : ((K : ℝ)+1)*u<2*Real.pi := by
    have h := (lt_div_iff₀ (by linarith : (0 : ℝ)<(K : ℝ)+1)).mp hhi
    nlinarith [h]
  exact mul_pos (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith))
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith))

end polyak.ModeLocking.TwoLag
