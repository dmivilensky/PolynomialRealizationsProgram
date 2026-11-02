import jacobi.GelfandLevitan.FiniteEndpointOperators

/-!
Article: jacobi, Proposition C.2.
The actual finite product primitives gain their genuine extra physical
integration power at the selected endpoint. This estimate is used in
the actual finite transformed solution and slope corrections before
the singular Wronskian boundary term is removed.
Use: finiteFeaturePrimitive_endpoint_bigO bounds the original finite selected-solution product primitives, retaining the actual interval measure and integration length.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory Asymptotics jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A genuine zero-endpoint primitive gains one physical power from an integrand with nonnegative endpoint power growth.
Use: finiteFeaturePrimitive_endpoint_bigO bounds the original finite selected-solution product primitives, retaining the actual interval measure and integration length.
Article: jacobi, Proposition C.2.
Source: the standard Bochner integral uniform norm bound.
Proof: the actual positive-endpoint Landau bound holds on an entire small positive interval. On (0,t] monotonicity of the nonnegative power bounds the original integrand by C*t^p; the genuine physical integration length contributes the additional factor t. -/
theorem endpointPrimitive_bigO {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ→E} {p : ℝ} (hp : 0≤p) (hf : f=O[𝓝[>] 0](fun t : ℝ => t^p)) :
    (fun t => ∫ r in (0:ℝ)..t,f r)=O[𝓝[>] 0](fun t : ℝ => t^(p+1)) := by
  -- The interval norm bound uses (0,t], so no artificial value or derivative at the singular endpoint is required.
  obtain ⟨C,hC,hbound⟩ := hf.exists_nonneg
  obtain ⟨ε,hε,hI⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hbound.bound
  apply IsBigO.of_bound C
  filter_upwards [Ioo_mem_nhdsGT hε] with t ht
  have hInt : ‖∫ r in (0:ℝ)..t,f r‖≤C*t^p*|t-(0:ℝ)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun r hr => by
      have hr' : r∈Ioc (0:ℝ) t := by simpa only [uIoc_of_le ht.1.le] using hr
      have hb := hI ⟨hr'.1,hr'.2.trans_lt ht.2⟩
      change ‖f r‖≤C*‖r^p‖ at hb
      rw [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hr'.1 _)] at hb
      exact hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr'.1.le hr'.2 hp) hC))
  rw [sub_zero,abs_of_pos ht.1] at hInt
  rw [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos ht.1 _),Real.rpow_add_one ht.1.ne']
  exact hInt.trans_eq (by ring)

/-- The actual original finite selected-solution product primitives have their genuine double-selected-power plus one endpoint bound.
Use: the original finite transformed solution and slope corrections have the printed O(t^(3*gamma+1)) and O(t^(3*gamma)) bounds needed for the genuine Green endpoint cancellation.
Article: jacobi, Proposition C.2.
Proof: both original selected solutions have their independently proved true gamma power bounds. Their continuous physical extensions agree with them on the actual small positive interval. The proved original primitive estimate adds the genuine integration power one. -/
theorem finiteFeaturePrimitive_endpoint_bigO (a : ℝ) (ha : -1<a) {N : ℕ} (i : FeatureIndex N) (z : ℂ) :
    finiteFeaturePrimitive a ha i z=O[𝓝[>] 0](fun t : ℝ => t^(2*gamma a+1)) := by
  -- Both factors are the same original selected functions used in the actual finite GL transform, including their normalization.
  have hProd := endpointBigO_mul (solution_endpoint_bigO a (finiteFeatureEnergy a ha i:ℂ)) (solution_endpoint_bigO a z)
  have hSource : (fun r => (finiteFeatureWave a ha i r:ℂ)*finiteReferenceWave a ha z r)=O[𝓝[>] 0]
      (fun t : ℝ => t^(gamma a+gamma a)) := by
    apply hProd.congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with r hr
    rw [finiteFeatureWave_value ha i ⟨hr.1.le,hr.2.le⟩,
      finiteReferenceWave_value ha z ⟨hr.1.le,hr.2.le⟩,realSolution_cast]
  have h := endpointPrimitive_bigO (by linarith [(parameters ha).1] : 0≤gamma a+gamma a) hSource
  change (fun t => ∫ r in (0:ℝ)..t,(finiteFeatureWave a ha i r:ℂ)*finiteReferenceWave a ha z r)=O[𝓝[>] 0] _
  simpa only [two_mul] using h

end
end jacobi.GelfandLevitan
