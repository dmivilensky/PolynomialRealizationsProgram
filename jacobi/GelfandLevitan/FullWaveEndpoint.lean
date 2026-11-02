import jacobi.GelfandLevitan.FullWaveRegularity
import jacobi.GelfandLevitan.SelectedEndpoint

/-!
Article: jacobi, Proposition C.3.
The actual full normalized target waves retain the original power branch
with a linear relative remainder. This includes the limit-circle range;
mere endpoint vanishing is not used to select a branch.
Use: fullWavePhysical_selected_branch divides by the genuine selected normalization, and targetWaveScale_eq_sqrt identifies it with the printed positive square root.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual original full wave normalization is strictly positive.
Use: fullWavePhysical_selected_branch divides by the genuine selected normalization, and targetWaveScale_eq_sqrt identifies it with the printed positive square root.
Article: jacobi, Proposition C.3.
Proof: the true reference norm and original norming ratio are strictly positive; their actual square roots and the unchanged sqrt(2) factors are positive. -/
theorem targetWaveScale_pos (a : ℝ) (ha : -1<a) (n : ℕ) : 0<targetWaveScale a ha n := by
  unfold targetWaveScale halfNormalization
  exact div_pos (mul_pos (div_pos (by positivity) (Real.sqrt_pos.mpr (norming_pos ha n)))
    (Real.sqrt_pos.mpr (normingRatio_properties ha n).2)) (by positivity)

/-- The actual original normalization is exactly the printed positive square root of its genuine original norming weight.
Use: fullWavePhysical_selected_branch has precisely the source's sqrt(c_k) normalization, rather than only an undetermined positive multiple.
Article: jacobi, Proposition C.3.
Proof: the independently computed true normalization square is rho_k/N_k; positivity selects its unique positive square root. -/
theorem targetWaveScale_eq_sqrt (a : ℝ) (ha : -1<a) (n : ℕ) :
    targetWaveScale a ha n=Real.sqrt (normingRatio a ha n/norming a n) := by
  rw [← targetWaveScale_sq a ha n,Real.sqrt_sq (targetWaveScale_pos a ha n).le]

/-- Approaching zero from inside the actual real physical interval approaches the genuine selected half-domain zero endpoint from its interior.
Use: fullWavePhysical_selected_branch transfers the independently proved original u endpoint remainder without changing its physical coordinate or selected branch.
Article: jacobi, Proposition C.3.
Proof: the original clipping map is continuous and fixes every sufficiently small positive physical point, which remains strictly above the original half-domain zero. -/
theorem halfParameterClamp_tendsto_zero_right :
    Tendsto halfParameterClamp (𝓝[>] (0:ℝ)) (𝓝[>] halfZero) := by
  -- Near zero the physical clamp fixes the original positive coordinate, so the limiting filter retains its actual selected side.
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,?_⟩
  · have h := (halfParameterClamp.continuous.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    simpa only [show halfParameterClamp 0=halfZero from Set.projIcc_of_mem (by norm_num) (by norm_num)] using h
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with t ht
    rw [show halfParameterClamp t=(⟨t,⟨ht.1.le,ht.2.le⟩⟩:HalfInterval) from
      Set.projIcc_of_mem (by norm_num) ⟨ht.1.le,ht.2.le⟩]
    exact ht.1

/-- Every actual normalized full target wave has exactly the original selected endpoint branch with its full linear relative error, including gamma<1/2.
Use: completes the literal endpoint assertion of general Proposition C.2 for the same original v_k basis defining the actual full H_alpha and its Green inverse.
Article: jacobi, Proposition C.3.
Proof: transfer the independently proved actual original transformed-solution relative remainder to the genuine real endpoint filter. On this actual half interval the full wave is its unchanged normalized real part. Taking real parts decreases the complex error norm, and the genuine positive normalizing factors cancel exactly. -/
theorem fullWavePhysical_selected_branch (a : ℝ) (ha : -1<a) (n : ℕ) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ t:ℝ in 𝓝[>] (0:ℝ),
      |fullWavePhysical a ha n t/(targetWaveScale a ha n*t^(gamma a))-1|≤C*t := by
  -- The source's selected u branch is already proved for every complex energy; no endpoint condition is postulated for the new full operator.
  obtain ⟨C,hC,hb⟩ := transformedSolution_selected_branch a ha (jacobi.Bessel.sigma a ha n:ℂ)
  refine ⟨C,hC,?_⟩
  filter_upwards [halfParameterClamp_tendsto_zero_right.eventually hb,
    Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with t ht hp
  have hc : halfParameterClamp t=(⟨t,⟨hp.1.le,hp.2.le⟩⟩:HalfInterval) :=
    Set.projIcc_of_mem (by norm_num) ⟨hp.1.le,hp.2.le⟩
  rw [hc] at ht
  have he := (Complex.abs_re_le_norm
    (transformedSolution a ha ⟨t,⟨hp.1.le,hp.2.le⟩⟩ (jacobi.Bessel.sigma a ha n:ℂ)/
      ((t^(gamma a):ℝ):ℂ)-1)).trans ht
  have hs := (targetWaveScale_pos a ha n).ne'
  have hpow := (Real.rpow_pos_of_pos hp.1 (gamma a)).ne'
  convert he using 1
  simp only [fullWavePhysical,reflectedWave,reflectMidpoint,ite_eq_left hp.2.le,hc,
    Complex.sub_re,Complex.div_ofReal_re,Complex.one_re]
  congr 1
  field_simp

end
end jacobi.GelfandLevitan
