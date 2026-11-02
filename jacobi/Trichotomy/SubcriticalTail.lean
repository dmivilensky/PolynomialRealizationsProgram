import jacobi.Trichotomy.SubcriticalPacking
import jacobi.Trichotomy.SubcriticalDensityPower
import jacobi.Trichotomy.SupercriticalTail

/-!
Article: jacobi, Proposition C.4.
The actual inverse coordinate tends to the physical endpoint at the
genuine finite support end. The proved profile and gap powers then
give precisely the printed density coefficient and exponent, including
the same source radius. Evenness gives both compact support ends.
Use: subcritical_density_tail_atLeft transfers the proved original physical density power law to the ordinary spatial finite endpoint.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The actual subcritical inverse packing coordinate tends to zero from inside at its genuine finite left support endpoint.
Use: subcritical_density_tail_atLeft transfers the proved original physical density power law to the ordinary spatial finite endpoint.
Article: jacobi, Proposition C.4.
Proof: the exact genuine coordinate image is the finite source interval. For every small positive physical point its strictly larger coordinate supplies a neighborhood threshold; actual coordinate monotonicity forces the genuine inverse below that point there. -/
theorem subcritical_inverse_atLeft {a : ℝ} (ha : -1<a) (hs : a < -(1/2:ℝ)) :
    Tendsto (packingInverse a ha) (𝓝[>] (-packingRadius a ha)) (𝓝[>] (0:ℝ)) := by
  -- Only values in the actual open packing image are used near its genuine finite left end.
  have hr := subcritical_radius_pos ha hs
  have hnear : ∀ᶠ x : ℝ in 𝓝[>] (-packingRadius a ha),x∈packingImage a ha := by
    rw [subcritical_packingImage ha hs]
    exact Ioo_mem_nhdsGT (by linarith)
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_order.mpr ⟨?_,?_⟩,?_⟩
  · intro b hb
    filter_upwards [hnear] with x hx
    exact hb.trans (packingInverse_mem a ha hx).1
  · intro b hb
    let t := min b (1/2)/2
    have ht : t∈Ioo (0:ℝ) 1 := by
      have hmin : 0<min b (1/2) := lt_min hb (by norm_num)
      dsimp only [t]
      constructor <;> linarith [min_le_right b (1/2)]
    have htb : t<b := by dsimp only [t]; linarith [min_le_left b (1/2)]
    have hthreshold := subcritical_coordinate_lower ha hs ht
    filter_upwards [hnear,nhdsWithin_le_nhds (Iio_mem_nhds hthreshold)] with x hx hxt
    apply lt_trans _ htb
    apply ((packingCoordinate_strictMono a ha).lt_iff_lt (packingInverse_mem a ha hx) ht).mp
    rwa [packingCoordinate_inverse a ha hx]
  · filter_upwards [hnear] with x hx
    exact (packingInverse_mem a ha hx).1

/-- The genuine compact packed density has the exact printed power and coefficient at its actual finite left support end.
Use: subcritical_density_tail combines reflection with this actual spatial endpoint limit to obtain both ends in the printed absolute-value form.
Article: jacobi, Proposition C.4.
Proof: compose the proved original profile/gap power limit with the genuine inverse endpoint limit. On its actual image the density is the original profile square and the gap equals x+x_star; near the genuine left end x<0, so this is precisely x_star-|x|. -/
theorem subcritical_density_tail_atLeft {a : ℝ} (ha : -1<a) (hs : a < -(1/2:ℝ)) :
    Tendsto (fun x : ℝ => packedDensity a ha x/(packingRadius a ha-|x|)^(compactDensityExponent a))
      (𝓝[>] (-packingRadius a ha)) (𝓝 (compactDensityCoefficient a ha)) := by
  -- The physical inverse is the actual one defining the original source density and finite packing gap.
  have hr := subcritical_radius_pos ha hs
  have hi := subcritical_inverse_atLeft ha hs
  have h := (subcritical_density_power_limit ha hs).comp hi
  apply h.congr'
  have hnear : ∀ᶠ x : ℝ in 𝓝[>] (-packingRadius a ha),x∈packingImage a ha := by
    rw [subcritical_packingImage ha hs]
    exact Ioo_mem_nhdsGT (by linarith)
  filter_upwards [hnear,nhdsWithin_le_nhds (Iio_mem_nhds (show -packingRadius a ha<0 by linarith)),
    (tendsto_nhds_of_tendsto_nhdsWithin hi).eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))] with x hx hxneg ht
  dsimp only [Function.comp_def]
  have he := subcritical_coordinate_gap ha hs ⟨(packingInverse_mem a ha hx).1.le,ht.le⟩
  rw [packingCoordinate_inverse a ha hx] at he
  rw [← he,← packedDensity_on_image a ha hx,abs_of_neg hxneg]
  congr 2
  ring

/-- The actual original compact density has the exact printed power law at both genuine support endpoints.
Use: completes the compact-tail clause of Proposition C.4, with the actual source C_alpha, x_star and exponent rather than unspecified asymptotic constants.
Article: jacobi, Proposition C.4.
Proof: negate the absolute spatial coordinate to map both actual support ends to the genuine left endpoint. The true density is even, and the ordinary continuous negation map sends the left-hand radius filter to the right-hand negative-radius filter. -/
theorem subcritical_density_tail {a : ℝ} (ha : -1<a) (hs : a < -(1/2:ℝ)) :
    Tendsto (fun x : ℝ => packedDensity a ha x/(packingRadius a ha-|x|)^(compactDensityExponent a))
      (Filter.comap (fun x : ℝ => |x|) (𝓝[<] (packingRadius a ha)))
      (𝓝 (compactDensityCoefficient a ha)) := by
  -- Absolute value records approach to either genuine finite endpoint from within the actual support interval.
  have hneg : Tendsto (fun r : ℝ => -r) (𝓝[<] (packingRadius a ha)) (𝓝[>] (-packingRadius a ha)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact neg_lt_neg (show r<packingRadius a ha from hr)
  have h := (subcritical_density_tail_atLeft ha hs).comp (hneg.comp (Filter.tendsto_comap (f := fun x : ℝ => |x|)))
  simpa only [Function.comp_def,packedDensity_even,packedDensity_abs,abs_neg,abs_abs] using h

end
end jacobi.Trichotomy
