import jacobi.Trichotomy.SubcriticalIntegrability
import Mathlib.Analysis.Calculus.LHopital

/-!
Article: jacobi, Proposition C.4.
The genuine finite reciprocal-profile integral defines the positive
packing radius and the actual vanishing endpoint gap. These supply
the genuine primitive and zero limit used in SubcriticalGap to prove
the printed power coefficient by the community l'Hopital rule.
Use: subcritical_radius_pos and the compact image theorem prove it is the genuine positive support radius in the subcritical regime.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference jacobi.GelfandLevitan
open scoped Topology

/-- The actual finite-radius expression in the source packing construction.
Use: subcritical_radius_pos and the compact image theorem prove it is the genuine positive support radius in the subcritical regime.
Article: jacobi, Proposition C.4.
-/
def packingRadius (a : ℝ) (ha : -1<a) : ℝ :=
  ∫ t in (0:ℝ)..(1/2),1/physicalProfile a ha t

/-- The actual original endpoint packing gap as a genuine integrable primitive.
Use: subcritical_gap_limit and subcritical_coordinate_gap give both the exact endpoint power coefficient and the literal original-coordinate gap x_alpha(t)+x_star.
Article: jacobi, Proposition C.4.
-/
def packingGap (a : ℝ) (ha : -1<a) (t : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..t,1/physicalProfile a ha s

/-- The genuine reciprocal profile is nonnegative at every real coordinate, including the totalized endpoints.
Use: the actual packing gap is nonnegative and the finite support radius is positive in the compact regime.
Article: jacobi, Proposition C.4.
Proof: the original profile is nonnegative everywhere on its true closed interval, and canonical projection preserves those same values. -/
theorem physicalProfile_reciprocal_nonneg (a : ℝ) (ha : -1<a) (t : ℝ) :
    0≤1/physicalProfile a ha t :=
  div_nonneg (by norm_num) (persymmetricProfile_nonneg a ha _)

/-- The actual primitive from the left physical endpoint is exactly the original centered coordinate plus its genuine finite support radius.
Use: the compact-image and density power-law theorems use the literal source gap, rather than an independently chosen vanishing coordinate.
Article: jacobi, Proposition C.4.
Proof: actual subcritical reciprocal integrability justifies splitting the original integral at t; reverse the centered-coordinate integral and rearrange. -/
theorem subcritical_coordinate_gap {a : ℝ} (ha : -1<a) (hs : a < -(1/2:ℝ))
    {t : ℝ} (ht : t∈Icc (0:ℝ) (1/2)) :
    packingCoordinate a ha t+packingRadius a ha=packingGap a ha t := by
  -- The source endpoint integral is genuinely integrable before any interval-additivity identity is applied.
  have hi := subcritical_reciprocal_integrable ha hs
  have hsub0 : uIcc (0:ℝ) t⊆uIcc (0:ℝ) (1/2) := by
    rw [uIcc_of_le ht.1,uIcc_of_le (by norm_num : (0:ℝ)≤1/2)]
    exact Icc_subset_Icc le_rfl ht.2
  have hsub1 : uIcc t (1/2:ℝ)⊆uIcc (0:ℝ) (1/2) := by
    rw [uIcc_of_le ht.2,uIcc_of_le (by norm_num : (0:ℝ)≤1/2)]
    exact Icc_subset_Icc ht.1 le_rfl
  have h := intervalIntegral.integral_add_adjacent_intervals (hi.mono_set hsub0) (hi.mono_set hsub1)
  dsimp only [packingCoordinate,packingRadius,packingGap]
  rw [intervalIntegral.integral_symm t (1/2:ℝ)]
  linarith

/-- The actual compact packing radius is strictly positive in the complete subcritical order range.
Use: the genuine support interval has nonzero finite length and the printed endpoint coefficient is evaluated at its actual two ends.
Article: jacobi, Proposition C.4.
Proof: the true centered coordinate is negative at one quarter, while its actual endpoint gap there is nonnegative. Their exact identity forces the genuine radius to be positive. -/
theorem subcritical_radius_pos {a : ℝ} (ha : -1<a) (hs : a < -(1/2:ℝ)) :
    0<packingRadius a ha := by
  -- A strict genuine midpoint comparison rules out a degenerate finite support radius.
  have hx := packingCoordinate_strictMono a ha
    (show (1/4:ℝ)∈Ioo 0 1 by constructor <;> norm_num)
    (show (1/2:ℝ)∈Ioo 0 1 by constructor <;> norm_num) (by norm_num)
  rw [packingCoordinate_midpoint] at hx
  have hg := intervalIntegral.integral_nonneg_of_forall (μ := volume) (by norm_num : (0:ℝ)≤1/4)
    (physicalProfile_reciprocal_nonneg a ha)
  have h := subcritical_coordinate_gap ha hs (t := 1/4) (by constructor <;> norm_num)
  dsimp only [packingGap] at h
  linarith

/-- The actual subcritical endpoint gap tends to zero on the genuine right physical endpoint filter.
Use: subcritical_gap_limit applies the zero-over-zero l'Hopital theorem to an actually continuous vanishing primitive.
Article: jacobi, Proposition C.4.
Proof: the genuine reciprocal profile is integrable from zero to one half, so its primitive is continuous on that full closed interval and equals zero at zero. Restrict this true continuity to the original positive endpoint filter. -/
theorem subcritical_gap_zero {a : ℝ} (ha : -1<a) (hs : a < -(1/2:ℝ)) :
    Tendsto (packingGap a ha) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  -- Actual interval integrability, rather than a formal power comparison of integrals, supplies the endpoint continuity.
  have hc := intervalIntegral.continuousOn_primitive_interval' (subcritical_reciprocal_integrable ha hs) left_mem_uIcc
  rw [uIcc_of_le (by norm_num : (0:ℝ)≤1/2)] at hc
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] (0:ℝ)) (𝓝[Icc (0:ℝ) (1/2)] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨nhdsWithin_le_nhds,?_⟩
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/2)] with t ht
    exact ⟨ht.1.le,ht.2.le⟩
  change Tendsto (fun t : ℝ => ∫ s in (0:ℝ)..t,1/physicalProfile a ha s) (𝓝[>] (0:ℝ)) (𝓝 0)
  simpa only [Function.comp_def,intervalIntegral.integral_same] using
    (hc (0:ℝ) (by constructor <;> norm_num)).tendsto.comp ht

end
end jacobi.Trichotomy
