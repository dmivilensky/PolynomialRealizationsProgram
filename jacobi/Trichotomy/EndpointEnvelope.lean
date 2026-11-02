import jacobi.Trichotomy.EndpointWaveComparison

/-!
Article: jacobi, Proposition C.4.
Use: endpoint_profile_difference_bound yields one summable inverse-cube plus inverse-square majorant for the genuine difference divided by t.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set jacobi.Reference

/-- The true index-normalized squared endpoint envelope has both bounds required to sum the profile comparison uniformly down to zero.
Use: endpoint_profile_difference_bound yields one summable inverse-cube plus inverse-square majorant for the genuine difference divided by t.
Article: jacobi, Proposition C.4.
Proof: the inverse-index branch gives the bound one. If (k+1)*t<=1, use the physical-power branch and x^(2*gamma)<=x; otherwise the bound one already implies the linear bound. -/
theorem waveEnvelope_normalized_bounds {a : ℝ} (hg : 1/2<gamma a) (k : ℕ)
    {t : ℝ} (ht : 0≤t) :
    (k+1:ℝ)^(2*gamma a)*(waveEnvelope a k t)^2≤1 ∧
      (k+1:ℝ)^(2*gamma a)*(waveEnvelope a k t)^2≤(k+1:ℝ)*t := by
  -- The two branches avoid any loss of the original small physical scale.
  have hn : 0<(k+1:ℝ) := by positivity
  have hm : 0≤waveEnvelope a k t := le_min (Real.rpow_nonneg ht _) (Real.rpow_nonneg hn.le _)
  have hp : 0<(k+1:ℝ)^(2*gamma a) := Real.rpow_pos_of_pos hn _
  have hpow (x : ℝ) (hx : 0≤x) : (x^(gamma a))^2=x^(2*gamma a) := by
    rw [show 2*gamma a=gamma a*2 by ring,Real.rpow_mul hx,Real.rpow_two]
  have hone : (k+1:ℝ)^(2*gamma a)*(waveEnvelope a k t)^2≤1 := by
    have hsq := pow_le_pow_left₀ hm (min_le_right (t^(gamma a)) ((k+1:ℝ)^(-gamma a))) 2
    apply (mul_le_mul_of_nonneg_left hsq hp.le).trans_eq
    rw [← Real.rpow_two ((k+1:ℝ)^(-gamma a)),← Real.rpow_mul hn.le,← Real.rpow_add hn]
    simp only [show 2*gamma a+(-gamma a)*2=0 by ring,Real.rpow_zero]
  refine ⟨hone,?_⟩
  by_cases hs : (k+1:ℝ)*t≤1
  · have hsq := pow_le_pow_left₀ hm (min_le_left (t^(gamma a)) ((k+1:ℝ)^(-gamma a))) 2
    calc
      _ ≤ (k+1:ℝ)^(2*gamma a)*(t^(gamma a))^2 := mul_le_mul_of_nonneg_left hsq hp.le
      _ = ((k+1:ℝ)*t)^(2*gamma a) := by rw [hpow t ht,Real.mul_rpow hn.le ht]
      _ ≤ (k+1:ℝ)*t := Real.rpow_le_self_of_le_one (mul_nonneg hn.le ht) hs (by linarith)
  · exact hone.trans (not_le.mp hs).le

end
end jacobi.Trichotomy
