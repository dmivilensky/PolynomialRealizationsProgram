import jacobi.Trichotomy.EndpointProfileDifference
import jacobi.Trichotomy.EndpointModeLimits

/-!
Article: jacobi, Proposition C.4.
The proof sums the actual profile-minus-reference-Green comparison by
dominated convergence and then uses the fully proved zero-energy
Green diagonal. All spectral bounds concern the original index list.
Use: supercritical_profile_limit combines this actual error with the exact independently proved reference diagonal constant.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology

/-- The original persymmetric profile differs from twice the genuine zero-energy reference Green diagonal by o(t) throughout the supercritical order range.
Use: supercritical_profile_limit combines this actual error with the exact independently proved reference diagonal constant.
Article: jacobi, Proposition C.4.
Proof: every fixed original spectral error divided by t tends to zero. The complete original-index inverse-cube plus inverse-square majorant is summable and uniform over every positive physical t. Apply dominated convergence to the actual difference series. -/
theorem supercritical_profile_difference_limit {a : ℝ} (ha : -1<a) (hsuper : -(1/2:ℝ)<a) :
    Tendsto (fun t : HalfInterval =>
      (persymmetricProfile a ha (halfInclusion t)-2*energyGreenKernel a 0 t t)/(t:ℝ))
      (𝓝[>] halfZero) (𝓝 0) := by
  -- The original source range itself supplies positivity of the first reference eigenvalue.
  have hg : 1/2<gamma a := by dsimp only [gamma]; linarith
  have h0 := reference_first_pos_supercritical hsuper
  obtain ⟨A,B,_hA,_hB,hbound⟩ := endpoint_profile_difference_bound ha hg h0
  have h2 : Summable (fun k : ℕ => B/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left B
  have h3 : Summable (fun k : ℕ => A/(k+1:ℝ)^3) := by
    have hs := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1<3)).comp_injective
      (fun i j h => Nat.add_right_cancel h : Function.Injective (fun k : ℕ => k+1))
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one,mul_one_div] using hs.mul_left A
  have h := tendsto_tsum_of_dominated_convergence (h3.add h2)
    (endpoint_difference_mode_limit ha hg) (by
      filter_upwards [self_mem_nhdsWithin] with t ht k
      simpa only [Real.norm_eq_abs] using hbound k t ht)
  simpa only [← endpoint_profile_difference_series ha h0,tsum_zero] using h

/-- The actual original persymmetric profile has exactly the printed linear endpoint constant at every alpha>-1/2.
Use: the intrinsic packing support and exponential tails in Proposition C.4, and the persymmetric-versus-Young comparison in Proposition C.4, start from this genuine source asymptotic.
Article: jacobi, Proposition C.4.
Proof: add the proved o(t) actual difference to twice the genuine zero-energy reference Green quotient. Its exact limit is 2/(2*gamma-1)=1/(alpha/2+1/4). -/
theorem supercritical_profile_limit {a : ℝ} (ha : -1<a) (hsuper : -(1/2:ℝ)<a) :
    Tendsto (fun t : HalfInterval => persymmetricProfile a ha (halfInclusion t)/(t:ℝ))
      (𝓝[>] halfZero) (𝓝 (1/(a/2+1/4))) := by
  -- The same original physical coordinate is used for both the true transformed profile and the reference diagonal.
  have hg : 1/2<gamma a := by dsimp only [gamma]; linarith
  have h := (supercritical_profile_difference_limit ha hsuper).add
    (((energyGreen_diagonal_limit ha (reference_first_pos_supercritical hsuper) hg).comp half_endpoint_tendsto).const_mul 2)
  have hval : (0:ℝ)+2*(1/(2*gamma a-1))=1/(a/2+1/4) := by
    dsimp only [gamma]
    field_simp
    ring
  rw [hval] at h
  apply h.congr'
  exact Eventually.of_forall (fun t => by dsimp only [Function.comp_def]; ring)

end
end jacobi.Trichotomy
