import jacobi.Trichotomy.SupercriticalCoordinate
import jacobi.Trichotomy.InfinitePacking
import jacobi.Analysis.LogarithmicPower

/-!
Article: jacobi, Proposition C.4.
The genuine density constructed in the original centered intrinsic
coordinate is positive on the entire real line. Its actual logarithmic
tail exponent is -2/nu at both ends, not only along a chosen physical
sequence. The genuine inverse coordinate transfers the endpoint limit.
Use: supercritical_density_tail transfers the true physical endpoint limit through the original inverse at spatial infinity.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The actual supercritical packing coordinate maps the whole physical interior onto the whole real line.
Use: supercritical_density_tail transfers the true physical endpoint limit through the original inverse at spatial infinity.
Article: jacobi, Proposition C.4.
Proof: the actual logarithmic coordinate has a proved infinite left endpoint, and the common centered-interval image theorem gives full surjectivity. -/
theorem supercritical_packingImage {a : ℝ} (ha : -1<a) (hs : -(1/2:ℝ)<a) :
    packingImage a ha=univ :=
  packingImage_eq_univ_of_atBot a ha (supercritical_coordinate_atBot ha hs)

/-- The original packed density is strictly positive at every real point throughout the supercritical order range.
Use: the logarithmic density tail is the actual positive full-support source density, with no zero-extension points at finite coordinates.
Article: jacobi, Proposition C.4.
Proof: the source density is positive exactly on the actual packing image, already proved to be the entire real line. -/
theorem supercritical_packedDensity_pos {a : ℝ} (ha : -1<a) (hs : -(1/2:ℝ)<a) (x : ℝ) :
    0<packedDensity a ha x := by
  apply (packedDensity_pos_iff a ha x).mpr
  rw [supercritical_packingImage ha hs]
  trivial

/-- The actual squared original profile has exactly the supercritical logarithmic tail exponent in its genuine packing coordinate.
Use: supercritical_density_tail_atBot passes this endpoint limit to ordinary spatial infinity using the same actual inverse coordinate.
Article: jacobi, Proposition C.4.
Proof: the actual profile has logarithmic exponent one and its actual coordinate has ratio nu to log(t). Divide these two proved limits and use the genuine eventual negative sign of the coordinate. -/
theorem supercritical_density_coordinate_tail {a : ℝ} (ha : -1<a) (hs : -(1/2:ℝ)<a) :
    Tendsto (fun t : ℝ => log ((physicalProfile a ha t)^2)/|packingCoordinate a ha t|)
      (𝓝[>] (0:ℝ)) (𝓝 (-2/(a/2+1/4))) := by
  -- The two independent original asymptotics use precisely the same real physical coordinate t.
  have hnu : 0<a/2+1/4 := by linarith
  have hp : Tendsto (fun t : ℝ => physicalProfile a ha t/t^(1:ℝ))
      (𝓝[>] (0:ℝ)) (𝓝 (1/(a/2+1/4))) := by
    simpa only [Real.rpow_one] using physicalProfile_supercritical_limit ha hs
  have hl := jacobi.Analysis.logarithmic_power_limit (one_div_pos.mpr hnu) hp
  have h := (((hl.const_mul 2).div (supercritical_coordinate_limit ha hs) hnu.ne').neg)
  simp only [mul_one,← neg_div] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1),
    (supercritical_coordinate_atBot ha hs).eventually (eventually_lt_atBot (0:ℝ))] with t ht hx
  have hlog := Real.log_ne_zero_of_pos_of_ne_one ht.1 ht.2.ne
  dsimp only [Pi.div_apply]
  rw [Real.log_pow,abs_of_neg hx]
  field_simp [hlog,hx.ne]
  ring

/-- The actual supercritical packed density has the printed exponential tail at minus infinity in the ordinary spatial coordinate.
Use: supercritical_density_tail uses exact evenness to obtain the same original tail exponent at both ends.
Article: jacobi, Proposition C.4.
Proof: the genuine inverse tends to the physical endpoint and exactly inverts the genuine coordinate. Its original squared-profile density identity transfers the independently proved coordinate tail to ordinary spatial infinity. -/
theorem supercritical_density_tail_atBot {a : ℝ} (ha : -1<a) (hs : -(1/2:ℝ)<a) :
    Tendsto (fun x : ℝ => log (packedDensity a ha x)/|x|) atBot (𝓝 (-2/(a/2+1/4))) := by
  have hfull := supercritical_packingImage ha hs
  have h := (supercritical_density_coordinate_tail ha hs).comp (packingInverse_atBot a ha hfull)
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro x
  have hx : x∈packingImage a ha := by rw [hfull]; trivial
  dsimp only [Function.comp_def]
  rw [packingCoordinate_inverse a ha hx,← packedDensity_on_image a ha hx]

/-- The actual centered packed density is unchanged by replacing x with its absolute value.
Use: supercritical_density_tail turns a positive-end limit into the source's single cocompact both-end assertion.
Article: jacobi, Proposition C.4.
Proof: split according to the sign of x and use the already proved genuine density evenness. -/
theorem packedDensity_abs (a : ℝ) (ha : -1<a) (x : ℝ) :
    packedDensity a ha |x|=packedDensity a ha x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx,packedDensity_even]

/-- The genuine original supercritical packed density has exactly the printed logarithmic tail exponent at both spatial ends.
Use: Proposition C.4 compares this actual exponent with the forced Young exponent four; the Nesterov application substitutes alpha=b/2.
Article: jacobi, Proposition C.4.
Proof: negate spatial infinity in the actual left-tail limit and use the proved density evenness. Compose the resulting positive-end limit with absolute value tending to infinity outside real compact sets. -/
theorem supercritical_density_tail {a : ℝ} (ha : -1<a) (hs : -(1/2:ℝ)<a) :
    Tendsto (fun x : ℝ => log (packedDensity a ha x)/|x|)
      (cocompact ℝ) (𝓝 (-2/(a/2+1/4))) := by
  have hpos := (supercritical_density_tail_atBot ha hs).comp tendsto_neg_atTop_atBot
  simp only [Function.comp_def,packedDensity_even,abs_neg] at hpos
  have h := hpos.comp (tendsto_norm_cocompact_atTop (E := ℝ))
  simpa only [Function.comp_def,Real.norm_eq_abs,abs_abs,packedDensity_abs] using h

end
end jacobi.Trichotomy
