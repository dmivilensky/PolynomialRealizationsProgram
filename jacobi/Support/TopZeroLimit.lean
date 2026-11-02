import jacobi.Support.TopProfile

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The genuine degree-normalized top-node solution tends to its actual
zero endpoint along every moving mesh ratio tending to zero. The proof
uses the full original power bound, including the genuine small-index
prefix, rather than a nonuniform interior asymptotic.
Use: topValue_uniform extends the proved actual positive-mesh limit to the entire original closed half chain, including every small mesh index.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The actual normalized support top-node solution tends to zero along every genuine moving mesh index whose ratio tends to the source endpoint zero.
Use: topValue_uniform extends the proved actual positive-mesh limit to the entire original closed half chain, including every small mesh index.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: the proved actual top-node bound controls the absolute normalized wave by C*((m+1)/n)^gamma. The true mesh ratio and 1/n both tend to zero, and the original exponent gamma is strictly positive. -/
theorem topValue_zero_limit {a b : ℝ} (ha:-1<a) (hb:-1<b)
    {ι : Type*} {l : Filter ι} {n m : ι→ℕ} (hn:Tendsto n l atTop)
    (hm:Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) l (𝓝 (0:ℝ))) :
    Tendsto (fun i => (n i:ℝ)^(-gamma a)*topValue a b ha hb (n i) (m i)) l (𝓝 (0:ℝ)) := by
  -- The original uniform bound covers actual bounded indices and growing indices simultaneously.
  have hg := (parameter_pos ha hb).1
  obtain ⟨c,C,hc,hC,hbound⟩ := topValue_bounds ha hb
  have hratio : Tendsto (fun i => ((m i:ℝ)+1)/(n i:ℝ)) l (𝓝 (0:ℝ)) := by
    simpa only [zero_add,add_div,one_div,Function.comp_def] using hm.add
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hn))
  have hmajor := (hratio.rpow_const (p:=gamma a) (Or.inr hg.le)).const_mul C
  simp only [Real.zero_rpow hg.ne',mul_zero] at hmajor
  apply squeeze_zero_norm' ?_ hmajor
  filter_upwards [hn.eventually hbound,hn.eventually (eventually_ge_atTop (8:ℕ)),
    hm.eventually (Iio_mem_nhds (show (0:ℝ)<1/2 by norm_num))] with i hi hni hmi
  have hni0 : (0:ℝ)<n i := by exact_mod_cast (show 0<n i by omega)
  have hmi' : 2*(m i)≤n i := by
    have hh := (div_lt_iff₀ hni0).mp hmi
    have hh' : (2:ℝ)*(m i:ℝ)≤n i := by linarith
    exact_mod_cast hh'
  have hm' : m i≤n i := by omega
  have hT : 0≤topValue a b ha hb (n i) (m i) := (naturalPolynomial_top_pos ha hb hm').le
  have hscale : 0≤(n i:ℝ)^(-gamma a) := (rpow_pos_of_pos hni0 _).le
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hscale hT)]
  calc
    _ ≤ (n i:ℝ)^(-gamma a)*(C*((m i:ℝ)+1)^gamma a) :=
      mul_le_mul_of_nonneg_left (hi (m i) (by omega)).2 hscale
    _ = _ := by
      rw [Real.div_rpow (by positivity : (0:ℝ)≤(m i:ℝ)+1) hni0.le,Real.rpow_neg hni0.le]
      ring

end
end jacobi.Support
