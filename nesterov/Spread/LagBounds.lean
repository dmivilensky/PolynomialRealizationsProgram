import nesterov.Spread.Hyperbolic

/-! The short/long upper-lag split and the lower-lag Fourier margin. -/
namespace nesterov.Spread
noncomputable section

theorem upper_lag_bound {m d x G₀ G F η Q : ℝ}
    (hm : 0<m) (hm4 : m≤1/4) (hd : 0≤d) (hdm : d≤m/2)
    (hx : 0≤x) (hG₀ : 1/4≤G₀) (hG₀1 : G₀≤1) (hG : G₀-d/2≤G)
    (hη : 0<η) (hη1 : η<1) (hsmall : Q+d<Real.sqrt η/8)
    (hshort : x≤m/4 → F≤G₀-m+d/2)
    (hlong : m/4<x → F≤Q+d/2) : F<eMinus η x*G := by
  have hd8 : d≤1/8 := by linarith
  have hGpos : 0<G := by linarith
  have hbase : 0≤G₀-d/2 := by linarith
  have hE : 0≤eMinus η x := (Real.sqrt_nonneg η).trans (eMinus_ge_sqrt hη.le hη1.le)
  by_cases hxm : x≤m/4
  · have hf := hshort hxm
    have hex : 1-x≤Real.exp (-x) := by
      have hh := Real.add_one_le_exp (-x)
      linarith
    have hEx := hex.trans (eMinus_ge_exp hη.le hx)
    have hprod := mul_le_mul hEx hG hbase hE
    have hbase1 : G₀-d/2≤1 := by linarith
    have hrem := mul_nonneg hx (sub_nonneg.mpr hbase1)
    nlinarith
  · have hf := hlong (lt_of_not_ge hxm)
    have hprod := mul_le_mul (eMinus_ge_sqrt hη.le hη1.le)
      (show 1/8≤G by linarith) (by norm_num : (0:ℝ)≤1/8) hE
    nlinarith

theorem lower_lag_bound {m d x G₀ G F η : ℝ}
    (hm : 0<m) (hm4 : m≤1/4) (_hd : 0≤d) (hdm : d≤m/2)
    (hx : 0≤x) (hG₀ : 1/4≤G₀) (hG : G₀-d/2≤G)
    (hη1 : η<1) (hF : F≤G₀-m+d/2) : F<ePlus η x*G := by
  have hGpos : 0<G := by linarith
  have hprod := mul_le_mul_of_nonneg_right (ePlus_ge_one hη1.le hx) hGpos.le
  nlinarith

end
end nesterov.Spread
