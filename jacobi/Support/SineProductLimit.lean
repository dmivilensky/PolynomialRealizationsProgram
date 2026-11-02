import jacobi.Support.SineCorrectionLimit
import jacobi.Support.SineGamma

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The actual arbitrary-shift sine products have the exact printed limit
along all moving mesh indices and nonintegral growing frequencies.
The original Gamma constant and sine power are both identified.
Use: compact uniform sine-product convergence and the actual top-node normalization use this same original product, Gamma constant and sine power.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter chebyshev1.SineJacobi
open scoped Topology

/-- The genuine original sine products have the exact normalized edge limit along every moving interior mesh sequence.
Use: compact uniform sine-product convergence and the actual top-node normalization use this same original product, Gamma constant and sine power.
Article: jacobi, Appendix C.3 (sine-product estimates).
Proof: the original mesh ratio tends to a positive t, so its true degree tends to infinity. Combine the actual Gamma quotient limit with the proved smooth correction limit and real-power continuity. The exponential correction is sinc(pi*t)^(s-1), which combines with the genuine mesh power to give precisely the printed sine power. -/
theorem sineProduct_limit {ι : Type*} {l : Filter ι} {N : ι→ℝ} {m : ι→ℕ}
    {s t : ℝ} (hs:0<s) (ht:t∈Ioo (0:ℝ) 1)
    (hN:Tendsto N l atTop) (hm:Tendsto (fun i => (m i:ℝ)/N i) l (𝓝 t)) :
    Tendsto (fun i => (N i)^(1-s)*sineProduct (π/N i) s (m i)) l
      (𝓝 ((Gamma s)⁻¹*(sin (π*t)/π)^(s-1))) := by
  -- Every asymptotic factor comes from the actual finite product; the original Gamma and endpoint normalizations are retained.
  have hmR : Tendsto (fun i => (m i:ℝ)) l atTop := by
    apply (tendsto_congr' ?_).mp (hm.pos_mul_atTop ht.1 hN)
    filter_upwards [hN.eventually (eventually_gt_atTop (0:ℝ))] with i hi
    exact div_mul_cancel₀ _ hi.ne'
  have hmNat : Tendsto m l atTop := tendsto_natCast_atTop_iff.mp hmR
  have hG := (risingRatio_limit hs).comp hmNat
  have hP := hm.rpow_const (p:=s-1) (Or.inl ht.1.ne')
  have hE := Real.continuous_exp.continuousAt.tendsto.comp (sineCorrection_limit hs.le ht hN hm)
  have hlim := (hG.mul hP).mul hE
  have hsc : 0<sinc (π*t) := sinc_pi_pos ⟨by linarith [ht.1],ht.2⟩
  have hconstant : t^(s-1)*exp ((s-1)*logSinc t)=(sin (π*t)/π)^(s-1) := by
    rw [logSinc,show (s-1)*log (sinc (π*t))=log (sinc (π*t))*(s-1) by ring,
      ← Real.rpow_def_of_pos hsc,← Real.mul_rpow ht.1.le hsc.le,
      sinc_of_ne_zero (mul_pos pi_pos ht.1).ne']
    congr 1
    field_simp [ht.1.ne']
  rw [mul_assoc,hconstant] at hlim
  apply (tendsto_congr' ?_).mpr hlim
  have hmesh := hm.add (hN.const_div_atTop (max s 1))
  simp only [add_zero] at hmesh
  filter_upwards [hN.eventually (eventually_gt_atTop (0:ℝ)),
    hmNat.eventually (eventually_gt_atTop (0:ℕ)),hmesh.eventually (Iio_mem_nhds ht.2)] with i hni hmi hi
  have hmiR : (0:ℝ)<m i := by exact_mod_cast hmi
  have hcell (j : ℕ) (hj:j<m i) : (j:ℝ)+s<N i ∧ (j:ℝ)+1<N i := by
    have hjm : (j:ℝ)≤m i := by exact_mod_cast hj.le
    have hupper : (m i:ℝ)+max s 1<N i := (div_lt_one hni).mp (by simpa only [add_div] using hi)
    exact ⟨lt_of_le_of_lt (add_le_add hjm (le_max_left _ _)) hupper,
      lt_of_le_of_lt (add_le_add hjm (le_max_right _ _)) hupper⟩
  dsimp [Function.comp_def]
  rw [sineProduct_correction hni hs _ (fun j hj => (hcell j hj).1) (fun j hj => (hcell j hj).2),
    Real.div_rpow hmiR.le hni.le,
    show (1-s:ℝ)= -(s-1) by ring,Real.rpow_neg hni.le,Real.rpow_neg hmiR.le]
  field_simp [(Real.rpow_pos_of_pos hmiR (s-1)).ne',(Real.rpow_pos_of_pos hni (s-1)).ne']

end
end jacobi.Support
