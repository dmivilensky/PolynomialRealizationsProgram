import jacobi.Trichotomy.PhysicalProfile
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue

/-!
Article: jacobi, Proposition 2.2.
The reciprocal of the actual positive profile defines the centered
coordinate. Its derivative, strict increase, continuity, exact reflection
and open interval image hold for every original alpha>-1, without
assuming any of the three possible endpoint support regimes.
Use: packingImage and packingInverse construct the actual source density, while the endpoint limits determine whether this coordinate has finite or infinite ends.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference jacobi.GelfandLevitan
open scoped Topology

/-- The genuine centered intrinsic coordinate of the original persymmetric profile.
Use: packingImage and packingInverse construct the actual source density, while the endpoint limits determine whether this coordinate has finite or infinite ends.
Article: jacobi, Proposition 2.2.
-/
def packingCoordinate (a : ℝ) (ha : -1<a) (t : ℝ) : ℝ :=
  ∫ s in (1/2:ℝ)..t,1/physicalProfile a ha s

/-- The actual centered packing coordinate has derivative exactly the positive reciprocal of the original profile at every physical interior point.
Use: strict increase, inverse differentiability and all density integral substitutions use this genuine Jacobian.
Article: jacobi, Proposition 2.2.
Proof: every closed segment from the midpoint to an interior point stays in the physical interior, where the genuine reciprocal is continuous. Apply the fundamental theorem of calculus using its globally measurable real representative. -/
theorem packingCoordinate_hasDerivAt (a : ℝ) (ha : -1<a) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (packingCoordinate a ha) (1/physicalProfile a ha t) t := by
  -- Local interior integrability suffices in every support regime; no endpoint integral is assumed finite.
  have hseg : uIcc (1/2:ℝ) t⊆Ioo (0:ℝ) 1 :=
    (ordConnected_Ioo : OrdConnected (Ioo (0:ℝ) 1)).uIcc_subset (by constructor <;> norm_num) ht
  have hc := physicalProfile_reciprocal_continuousOn a ha
  have hm : AEStronglyMeasurable (fun s : ℝ => 1/physicalProfile a ha s) volume :=
    (measurable_const.div (physicalProfile_continuous a ha).measurable).aestronglyMeasurable
  exact intervalIntegral.integral_hasDerivAt_right
    ((hc.mono hseg).intervalIntegrable) hm.stronglyMeasurableAtFilter
    (hc.continuousAt (isOpen_Ioo.mem_nhds ht))

/-- The genuine intrinsic packing coordinate is continuous throughout the physical interior.
Use: packingImage_open and the actual inverse coordinate require continuity on the whole original domain.
Article: jacobi, Proposition 2.2.
Proof: its independently proved actual derivative exists at every physical interior point. -/
theorem packingCoordinate_continuousOn (a : ℝ) (ha : -1<a) :
    ContinuousOn (packingCoordinate a ha) (Ioo (0:ℝ) 1) :=
  fun _ ht => (packingCoordinate_hasDerivAt a ha ht).continuousAt.continuousWithinAt

/-- The actual intrinsic packing coordinate is strictly increasing on the entire open physical interval.
Use: the original packing inverse is unique, and its image is one genuine open interval.
Article: jacobi, Proposition C.4.
Proof: apply the real mean value theorem to the convex physical interval; the exact genuine derivative is positive because the original profile is positive. -/
theorem packingCoordinate_strictMono (a : ℝ) (ha : -1<a) :
    StrictMonoOn (packingCoordinate a ha) (Ioo (0:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0:ℝ) 1) (packingCoordinate_continuousOn a ha)
  intro t ht
  have hti : t∈Ioo (0:ℝ) 1 := by simpa only [interior_Ioo] using ht
  rw [(packingCoordinate_hasDerivAt a ha hti).deriv]
  exact one_div_pos.mpr (physicalProfile_pos a ha hti)

/-- The original intrinsic coordinate is centered exactly at the original physical midpoint.
Use: together with strict increase and reflection, fixes the centered rather than a translated packed density.
Article: jacobi, Proposition 2.2.
Proof: the defining interval integral has equal endpoints. -/
theorem packingCoordinate_midpoint (a : ℝ) (ha : -1<a) : packingCoordinate a ha (1/2)=0 := by
  simp only [packingCoordinate,intervalIntegral.integral_same]

/-- The actual intrinsic coordinate changes sign under the original physical reflection.
Use: packingInverse_reflection and the packed density inherit exact evenness, for both finite and infinite support.
Article: jacobi, Proposition 2.2.
Proof: use the ordinary affine-reflection substitution in the actual reciprocal-profile integral, then reverse its endpoints. The original profile reflection preserves the integrand exactly. -/
theorem packingCoordinate_reflection (a : ℝ) (ha : -1<a) (t : ℝ) :
    packingCoordinate a ha (1-t)= -packingCoordinate a ha t := by
  have h := intervalIntegral.integral_comp_sub_left (a := t) (b := (1/2:ℝ))
    (fun s : ℝ => 1/physicalProfile a ha s) 1
  simp only [physicalProfile_reflection,show (1:ℝ)-1/2=1/2 by ring] at h
  exact h.symm.trans (intervalIntegral.integral_symm _ _)

/-- The actual intrinsic packing image, without prematurely choosing finite or infinite endpoint coordinates.
Use: packingIso and packingInverse define the source density on exactly the coordinate range; Proposition C.4's endpoint asymptotics identify its support.
Article: jacobi, Proposition 2.2.
-/
def packingImage (a : ℝ) (ha : -1<a) : Set ℝ :=
  packingCoordinate a ha '' Ioo (0:ℝ) 1

/-- The actual coordinate image is one interval.
Use: the canonical order isomorphism to packingImage has a continuous inverse in its ordinary real subspace topology.
Article: jacobi, Proposition 2.2.
Proof: the physical interval is preconnected and the true coordinate is continuous there; its image is preconnected and therefore order-connected in the real line. -/
theorem packingImage_ordConnected (a : ℝ) (ha : -1<a) : OrdConnected (packingImage a ha) :=
  ((isPreconnected_Ioo).image (packingCoordinate a ha) (packingCoordinate_continuousOn a ha)).ordConnected

/-- Every actual coordinate value is an interior point of the true packing image.
Use: inverse-coordinate derivatives and density Jacobians apply on this genuine open image for every original order.
Article: jacobi, Proposition 2.2.
Proof: choose two physical neighbors of a preimage. Strict increase brackets its coordinate value between theirs, and the intermediate value theorem fills that whole coordinate neighborhood. -/
theorem packingImage_open (a : ℝ) (ha : -1<a) : IsOpen (packingImage a ha) := by
  -- The argument constructs the neighborhood from finite interior physical points and works independently of endpoint behavior.
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨t,ht,rfl⟩
  let l := t/2
  let r := (t+1)/2
  have hl : l∈Ioo (0:ℝ) 1 := by dsimp only [l]; constructor <;> linarith [ht.1,ht.2]
  have hr : r∈Ioo (0:ℝ) 1 := by dsimp only [r]; constructor <;> linarith [ht.1,ht.2]
  have hlt : l<t := by dsimp only [l]; linarith [ht.1]
  have htr : t<r := by dsimp only [r]; linarith [ht.2]
  have hm := packingCoordinate_strictMono a ha
  refine mem_of_superset (Ioo_mem_nhds (hm hl ht hlt) (hm ht hr htr)) ?_
  intro y hy
  have hseg : Icc l r⊆Ioo (0:ℝ) 1 := (convex_Ioo (0:ℝ) 1).ordConnected.out hl hr
  obtain ⟨s,hs,hsy⟩ := intermediate_value_Icc (hlt.trans htr).le
    ((packingCoordinate_continuousOn a ha).mono hseg) ⟨hy.1.le,hy.2.le⟩
  exact ⟨s,hseg hs,hsy⟩

end
end jacobi.Trichotomy
