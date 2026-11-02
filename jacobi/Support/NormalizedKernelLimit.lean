import jacobi.Support.NormalizedVolterra

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
The actual ground-normalized two-index finite kernel converges to
twice the ratio of the actual sine-power ground squares. Both mesh
indices and the degree may vary along any cofinal filter; all matrix
couplings, normalizations and parameter premises are discharged.
Use: normalizedKernel_limit passes the original matrix coefficient in the reduction-of-order denominator to its genuine continuum value.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The actual support coupling converges to one half along every positive interior moving mesh index.
Use: normalizedKernel_limit passes the original matrix coefficient in the reduction-of-order denominator to its genuine continuum value.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: a positive mesh ratio and a cofinal degree force the original index to infinity. The actual coefficient lemma bounds its deviation by C/(m+1)^2 on the eventual physical half chain, which tends to zero. -/
theorem coupling_mesh_limit {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {ι:Type*} {l:Filter ι} {n m:ι→ℕ} {t:ℝ} (ht:t∈Ioo (0:ℝ) (1/2))
    (hn:Tendsto n l atTop) (hm:Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) l (𝓝 t)) :
    Tendsto (fun i => sqrt ((naturalChain a b ha hb (n i+1)).data.aSq (m i+1))) l (𝓝 (1/2:ℝ)) := by
  -- The original coefficient estimate is used at the same moving physical edge as the mesh limit.
  have hnR : Tendsto (fun i => (n i:ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hn
  have hmR : Tendsto (fun i => (m i:ℝ)) l atTop := by
    apply (tendsto_congr' ?_).mp (hm.pos_mul_atTop ht.1 hnR)
    filter_upwards [hn.eventually_gt_atTop 0] with i hi
    exact div_mul_cancel₀ _ (by exact_mod_cast hi.ne')
  have hmNat : Tendsto m l atTop := tendsto_natCast_atTop_iff.mp hmR
  obtain ⟨c,C,hc,hC,hcoeff⟩ := coefficient_bounds ha hb
  have hzero := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp
    ((tendsto_add_atTop_nat 1).comp hmNat)).pow 2
  have hbound : Tendsto (fun i => C/((m i+1:ℕ):ℝ)^2) l (𝓝 0) := by
    simpa [Function.comp_def,div_pow,div_eq_mul_inv] using hzero.const_mul C
  have herr : Tendsto (fun i => sqrt ((naturalChain a b ha hb (n i+1)).data.aSq (m i+1))-(1/2:ℝ)) l (𝓝 0) := by
    apply squeeze_zero_norm' _ hbound
    filter_upwards [((tendsto_add_atTop_nat 1).comp hn).eventually hcoeff,
      hn.eventually_gt_atTop 0,hm.eventually (Iio_mem_nhds ht.2)] with i he hni hmi
    dsimp only [Function.comp_def] at he
    have hniR : (0:ℝ)<n i := by exact_mod_cast hni
    have hmid : 2*m i≤n i := by
      have h := (div_lt_iff₀ hniR).mp hmi
      have : 2*(m i:ℝ)<n i := by linarith
      exact_mod_cast this.le
    have h := (he.2 (m i+1) (by omega) (by omega)).2
    simp only [Real.norm_eq_abs]
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans h
  simpa only [sub_add_cancel,zero_add] using herr.add_const (1/2:ℝ)

/-- The original support top profile is its exact positive Gamma amplitude times the actual reference ground weight.
Use: normalizedKernel_limit cancels that same genuine amplitude from both original kernel indices, proving independence of the second Jacobi parameter in the limiting normalized kernel.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: divide the positive original sine power by its exact pi power and use the printed definition of kappa_U. -/
theorem topProfile_weight {a b:ℝ} {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2)) :
    topProfile a b t=sqrt (topAmplitudeSquare a b)*weight a t := by
  have hs : 0≤sin (π*t) := sin_nonneg_of_nonneg_of_le_pi
    (mul_nonneg pi_pos.le ht.1) (by nlinarith [ht.2,pi_pos])
  rw [weight,Real.div_rpow hs pi_pos.le]
  dsimp [topProfile,topConstant]
  ring

/-- The original normalized finite kernel has its exact moving two-index continuum limit at every positive point of the physical half triangle.
Use: bounded two-variable mesh convergence passes the actual finite normalized Volterra operator to groundVolterra; the original complex support polynomials are then compared with its genuine reference solution.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the actual top values at j, m and m+1 have their already proved positive moving-mesh limits. The original coupling tends to one half. Cancel the identical finite degree powers before taking the quotient limit, and cancel the identical positive Gamma amplitudes afterwards. -/
theorem normalizedKernel_limit {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {ι:Type*} {l:Filter ι} {n m j:ι→ℕ} {r s:ℝ}
    (hr:r∈Ioo (0:ℝ) (1/2)) (hs:s∈Ioo (0:ℝ) r)
    (hn:Tendsto n l atTop)
    (hm:Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) l (𝓝 r))
    (hj:Tendsto (fun i => (j i:ℝ)/(n i:ℝ)) l (𝓝 s)) :
    Tendsto (fun i => normalizedKernel a b ha hb (n i) (m i) (j i)) l
      (𝓝 (2*(weight a s)^2/(weight a r)^2)) := by
  -- Both adjacent original ground values retain exactly the same degree normalization.
  have hm' : Tendsto (fun i => ((m i+1:ℕ):ℝ)/(n i:ℝ)) l (𝓝 r) := by
    simpa only [Nat.cast_add,Nat.cast_one,add_div,add_zero,Function.comp_def] using
      hm.add ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn)
  have hu := topValue_limit ha hb ⟨hr.1,by linarith [hr.2]⟩ hn hm
  have hu' := topValue_limit ha hb ⟨hr.1,by linarith [hr.2]⟩ hn hm'
  have hv := topValue_limit ha hb ⟨hs.1,by linarith [hs.2,hr.2]⟩ hn hj
  have hac := coupling_mesh_limit ha hb hr hn hm
  have hU : 0<topProfile a b r := by
    rw [topProfile_weight ⟨hr.1.le,hr.2.le⟩]
    exact mul_pos (sqrt_pos.mpr (topAmplitudeSquare_pos ha hb))
      (weight_pos a ⟨hr.1,by linarith [hr.2]⟩)
  have hlim := (hv.pow 2).div ((hac.mul hu).mul hu') (by positivity : (1/2:ℝ)*topProfile a b r*topProfile a b r≠0)
  have hvalue : (topProfile a b s)^2/((1/2:ℝ)*topProfile a b r*topProfile a b r)=
      2*(weight a s)^2/(weight a r)^2 := by
    rw [topProfile_weight ⟨hs.1.le,by linarith [hs.2,hr.2]⟩,
      topProfile_weight ⟨hr.1.le,hr.2.le⟩]
    field_simp [(sqrt_pos.mpr (topAmplitudeSquare_pos ha hb)).ne',
      (weight_pos a ⟨hr.1,by linarith [hr.2]⟩).ne']
  rw [hvalue] at hlim
  apply (tendsto_congr' ?_).mpr hlim
  filter_upwards [hn.eventually_gt_atTop 0] with i hi
  have hn0 : (0:ℝ)<n i := by exact_mod_cast hi
  dsimp [normalizedKernel]
  field_simp [(rpow_pos_of_pos hn0 (-gamma a)).ne']

end
end jacobi.Support
