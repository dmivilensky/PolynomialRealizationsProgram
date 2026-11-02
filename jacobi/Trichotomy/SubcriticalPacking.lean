import jacobi.Trichotomy.SubcriticalGap
import jacobi.Trichotomy.PackedDensity
import Mathlib.Topology.Algebra.Support

/-!
Article: jacobi, Proposition C.4.
The genuine finite radius and vanishing endpoint primitive determine
both ends of the original intrinsic-coordinate image. The constructed
source density is positive precisely on that open centered interval,
so its actual topological support is the printed closed interval.
Use: subcritical_packingImage identifies the complete true coordinate interval, and the compact density tail uses its literal endpoint gap.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology

/-- The actual subcritical intrinsic coordinate tends to minus its genuine finite packing radius at the left physical endpoint.
Use: subcritical_packingImage identifies the complete true coordinate interval, and the compact density tail uses its literal endpoint gap.
Article: jacobi, Proposition C.4.
Proof: the genuine endpoint primitive tends to zero and equals x_alpha(t)+x_star on the physical left half interval. -/
theorem subcritical_coordinate_endpoint {a : ℝ} (ha : -1<a) (hs : a < -(1/2:ℝ)) :
    Tendsto (packingCoordinate a ha) (𝓝[>] (0:ℝ)) (𝓝 (-packingRadius a ha)) := by
  have h := (subcritical_gap_zero ha hs).sub_const (packingRadius a ha)
  simp only [zero_sub] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with t ht
  have he := subcritical_coordinate_gap ha hs ⟨ht.1.le,ht.2.le⟩
  linarith

/-- Every genuine subcritical physical interior coordinate lies strictly above the actual finite left packing endpoint.
Use: subcritical_coordinate_bounds obtains both exact interval bounds by the original midpoint reflection.
Article: jacobi, Proposition C.4.
Proof: before the midpoint, the true gap is the integral of a strictly positive original reciprocal profile on a positive-length interval. After the midpoint, strict coordinate increase and the positive radius give the same strict bound. -/
theorem subcritical_coordinate_lower {a : ℝ} (ha : -1<a) (hs : a < -(1/2:ℝ))
    {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) : -packingRadius a ha<packingCoordinate a ha t := by
  -- Positivity concerns the actual entire endpoint segment, whose integrability was independently proved.
  by_cases hh : t≤1/2
  · have hsub : uIcc (0:ℝ) t⊆uIcc (0:ℝ) (1/2) := by
      rw [uIcc_of_le ht.1.le,uIcc_of_le (by norm_num : (0:ℝ)≤1/2)]
      exact Icc_subset_Icc le_rfl hh
    have hg := intervalIntegral.intervalIntegral_pos_of_pos_on
      ((subcritical_reciprocal_integrable ha hs).mono_set hsub)
      (fun s hst => one_div_pos.mpr (physicalProfile_pos a ha ⟨hst.1,hst.2.trans ht.2⟩)) ht.1
    have he := subcritical_coordinate_gap ha hs ⟨ht.1.le,hh⟩
    dsimp only [packingGap] at he
    linarith
  · have hx := packingCoordinate_strictMono a ha
      (show (1/2:ℝ)∈Ioo 0 1 by constructor <;> norm_num) ht (lt_of_not_ge hh)
    rw [packingCoordinate_midpoint] at hx
    linarith [subcritical_radius_pos ha hs]

/-- The actual original subcritical coordinate lies in the exact printed finite centered interval.
Use: the complete packing image and compact support statements have their literal genuine source endpoints.
Article: jacobi, Proposition C.4.
Proof: the actual lower bound and its physical reflection give both strict endpoint bounds. -/
theorem subcritical_coordinate_bounds {a : ℝ} (ha : -1<a) (hs : a < -(1/2:ℝ))
    {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    packingCoordinate a ha t∈Ioo (-packingRadius a ha) (packingRadius a ha) := by
  have hr := subcritical_coordinate_lower ha hs (t := 1-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
  rw [packingCoordinate_reflection] at hr
  exact ⟨subcritical_coordinate_lower ha hs ht,by linarith⟩

/-- The genuine subcritical packing image is exactly the entire printed finite centered open interval.
Use: the source compact support and finite-end inverse limits concern the actual density constructed from the original profile.
Article: jacobi, Proposition C.4.
Proof: the actual coordinate bounds give one inclusion. For every target in that interval, the proved left endpoint limit supplies a smaller actual coordinate than both the target and its negative. Reflection and order-connectedness of the actual image fill the target. -/
theorem subcritical_packingImage {a : ℝ} (ha : -1<a) (hs : a < -(1/2:ℝ)) :
    packingImage a ha=Ioo (-packingRadius a ha) (packingRadius a ha) := by
  -- Surjectivity is proved for every actual interior target, without enlarging the genuine coordinate image.
  apply subset_antisymm
  · rintro _ ⟨t,ht,rfl⟩
    exact subcritical_coordinate_bounds ha hs ht
  · intro y hy
    have hmin : -packingRadius a ha<min y (-y) := lt_min hy.1 (by linarith [hy.2])
    have hnear : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),t∈Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
    obtain ⟨t,ht,hsmall⟩ := (hnear.and
      ((subcritical_coordinate_endpoint ha hs).eventually (Iio_mem_nhds hmin))).exists
    have hmem : packingCoordinate a ha t∈packingImage a ha := ⟨t,ht,rfl⟩
    apply (packingImage_ordConnected a ha).out hmem (packingImage_neg a ha hmem)
    constructor <;> linarith [min_le_left y (-y),min_le_right y (-y)]

/-- The actual topological support of the original subcritical packed density is exactly the printed closed centered interval.
Use: completes the compact-support clause of Proposition C.4 with the genuine positive finite radius, rather than only an upper bound on support.
Article: jacobi, Proposition C.4.
Proof: the density is positive exactly on its actual coordinate image and is nonnegative everywhere. Thus its nonzero support is the proved open centered interval, whose closure is the printed closed interval because the true radius is positive. -/
theorem subcritical_packedDensity_support {a : ℝ} (ha : -1<a) (hs : a < -(1/2:ℝ)) :
    tsupport (packedDensity a ha)=Icc (-packingRadius a ha) (packingRadius a ha) := by
  -- Both support inclusions follow from the genuine density positivity equivalence, including every interior point.
  have hsup : Function.support (packedDensity a ha)=packingImage a ha := by
    ext x
    constructor
    · intro hx
      exact (packedDensity_pos_iff a ha x).mp
        (lt_of_le_of_ne (packedDensity_nonneg a ha x) (Ne.symm hx))
    · intro hx
      exact ((packedDensity_pos_iff a ha x).mpr hx).ne'
  change closure (Function.support (packedDensity a ha))=_
  rw [hsup,subcritical_packingImage ha hs,closure_Ioo (by linarith [subcritical_radius_pos ha hs])]

end
end jacobi.Trichotomy
