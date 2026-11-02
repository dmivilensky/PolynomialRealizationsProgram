import jacobi.Support.SineCorrectionError

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The genuine arbitrary-shift smooth correction converges along every
moving mesh index and every real frequency tending to infinity. All
compact-domain and growing-index error conditions are discharged from
the actual mesh ratio limit, rather than being additional certificates.
Use: sineProduct_limit combines this with the genuine normalized Gamma quotient to identify the original sine-product edge constant.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter chebyshev1.SineJacobi
open scoped Topology

/-- The original smooth sine-product correction has its exact limit along arbitrary moving original indices and real growing frequencies.
Use: sineProduct_limit combines this with the genuine normalized Gamma quotient to identify the original sine-product edge constant.
Article: jacobi, Appendix C.3 (sine-product estimates).
Proof: the actual mesh ratios eventually lie in a fixed compact interval strictly below one. The proved quantitative error is a constant times (m/N)*(1/N), hence tends to zero. Continuity of the genuine log-sinc function evaluates the remaining original term. -/
theorem sineCorrection_limit {ι : Type*} {l : Filter ι} {N : ι→ℝ} {m : ι→ℕ}
    {s t : ℝ} (hs:0≤s) (ht:t∈Ioo (0:ℝ) 1)
    (hN:Tendsto N l atTop) (hm:Tendsto (fun i => (m i:ℝ)/N i) l (𝓝 t)) :
    Tendsto (fun i => sineCorrection (N i) s (m i)) l (𝓝 ((s-1)*logSinc t)) := by
  -- The genuine real frequency may be nonintegral; only its actual divergence and original mesh ratio are used.
  let b : ℝ := (t+1)/2
  have hb0 : 0≤b := by dsimp [b]; linarith [ht.1]
  have hb1 : b<1 := by dsimp [b]; linarith [ht.2]
  have htb : t<b := by dsimp [b]; linarith [ht.2]
  obtain ⟨M,hM,herr⟩ := sineCorrection_error hb0 hb1
  have hmesh := hm.add (hN.const_div_atTop (max s 1))
  simp only [add_zero] at hmesh
  have hemesh := hmesh.eventually (Iio_mem_nhds htb)
  have heN := hN.eventually (eventually_ge_atTop (1:ℝ))
  have hzero := tendsto_inv_atTop_zero.comp hN
  have hmajor := (hm.mul hzero).const_mul (M*(s^2+s))
  simp only [mul_zero] at hmajor
  have he : Tendsto (fun i => sineCorrection (N i) s (m i)-
      (s-1)*logSinc ((m i:ℝ)/N i)) l (𝓝 (0:ℝ)) := by
    apply squeeze_zero_norm' ?_ hmajor
    filter_upwards [hemesh,heN] with i hi hni
    have hni0 : 0<N i := by linarith
    have hc (j : ℕ) (hj:j<m i) : ((j:ℝ)+s)/N i≤b ∧ ((j:ℝ)+1)/N i≤b := by
      have hjm : (j:ℝ)≤m i := by exact_mod_cast hj.le
      constructor
      · exact (div_le_div_of_nonneg_right (add_le_add hjm (le_max_left _ _)) hni0.le).trans (by
          simpa only [add_div] using hi.le)
      · exact (div_le_div_of_nonneg_right (add_le_add hjm (le_max_right _ _)) hni0.le).trans (by
          simpa only [add_div] using hi.le)
    calc
      _ = |sineCorrection (N i) s (m i)-(s-1)*logSinc ((m i:ℝ)/N i)| := Real.norm_eq_abs _
      _ ≤ M*(s^2+s)*(m i:ℝ)/(N i)^2 := herr _ _ hni0 hs _ hc
      _ = _ := by dsimp [Function.comp_def]; ring
  have hg : Tendsto (fun i => logSinc ((m i:ℝ)/N i)) l (𝓝 (logSinc t)) :=
    ((logSinc_contDiff.continuousOn t ⟨by linarith [ht.1],ht.2⟩).continuousAt
      (isOpen_Ioo.mem_nhds ⟨by linarith [ht.1],ht.2⟩)).tendsto.comp hm
  simpa only [sub_add_cancel,zero_add] using he.add (hg.const_mul (s-1))

end
end jacobi.Support
