import jacobi.GelfandLevitan.ProfilePositivity
import jacobi.GelfandLevitan.ProfileMass

/-!
Article: jacobi, Proposition 2.2.
Use: packingCoordinate is an ordinary real interval integral of its reciprocal; physicalProfile_eq identifies every physical point with the source profile.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set jacobi.Reference jacobi.GelfandLevitan
open scoped Topology

/-- The original continuous persymmetric profile in real coordinates, using the canonical projection onto its closed physical interval.
Use: packingCoordinate is an ordinary real interval integral of its reciprocal; physicalProfile_eq identifies every physical point with the source profile.
Article: jacobi, Proposition 2.2.
-/
def physicalProfile (a : ℝ) (ha : -1<a) (t : ℝ) : ℝ :=
  persymmetricProfile a ha (projIcc 0 1 (by norm_num) t)

/-- The real-coordinate actual profile is continuous on the whole real line.
Use: its reciprocal is continuous on the physical interior, providing the genuine packing-coordinate derivative and Jacobian.
Article: jacobi, Proposition 2.2.
Proof: compose the original continuous profile with the community continuous closed-interval projection. -/
theorem physicalProfile_continuous (a : ℝ) (ha : -1<a) : Continuous (physicalProfile a ha) :=
  (persymmetricProfile a ha).continuous.comp continuous_projIcc

/-- The real-coordinate profile equals the original source profile at every original physical point, including both endpoints.
Use: all endpoint limits, source integrals and later density substitutions retain precisely the original phi_alpha normalization.
Article: jacobi, Proposition 2.2.
Proof: the canonical projection fixes every point already in the closed physical interval. -/
theorem physicalProfile_eq (a : ℝ) (ha : -1<a) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    physicalProfile a ha t=persymmetricProfile a ha ⟨t,ht⟩ := by
  unfold physicalProfile
  congr 1
  exact projIcc_of_mem (by norm_num) ht

/-- The actual real-coordinate profile is strictly positive at every physical interior point.
Use: the intrinsic coordinate derivative is positive and its reciprocal has no internal singularities for any alpha>-1.
Article: jacobi, Proposition 2.2.
Proof: identify the actual original physical profile and use its already proved spectral positivity. -/
theorem physicalProfile_pos (a : ℝ) (ha : -1<a) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    0<physicalProfile a ha t := by
  rw [physicalProfile_eq a ha ⟨ht.1.le,ht.2.le⟩]
  exact persymmetricProfile_pos a ha _ ht

/-- The genuine reciprocal profile is continuous on the open physical interval for every original order.
Use: packingCoordinate_hasDerivAt applies the fundamental theorem of calculus on each actual interior integration segment.
Article: jacobi, Proposition 2.2.
Proof: the original profile is continuous and strictly positive there, so division by it is continuous on the same open interval. -/
theorem physicalProfile_reciprocal_continuousOn (a : ℝ) (ha : -1<a) :
    ContinuousOn (fun t : ℝ => 1/physicalProfile a ha t) (Ioo (0:ℝ) 1) :=
  continuousOn_const.div (physicalProfile_continuous a ha).continuousOn
    (fun _ ht => (physicalProfile_pos a ha ht).ne')

/-- The genuine real-coordinate profile has the original midpoint reflection on the whole real line.
Use: packingCoordinate_reflection proves the actual centered intrinsic coordinate is odd under t to 1-t, giving an even packed density.
Article: jacobi, Proposition 2.2.
Proof: the canonical projection commutes with reflection about one half. Apply the proved original profile reflection to that same projected physical point. -/
theorem physicalProfile_reflection (a : ℝ) (ha : -1<a) (t : ℝ) :
    physicalProfile a ha (1-t)=physicalProfile a ha t := by
  -- Projection preserves the same physical reflection even for real points outside the original interval.
  unfold physicalProfile
  rw [← persymmetricProfile_reflection a ha (projIcc 0 1 (by norm_num) t)]
  congr 1
  apply Subtype.ext
  change max 0 (min 1 (1-t))=1-max 0 (min 1 t)
  by_cases ht : t≤0
  · rw [min_eq_left (by linarith : (1:ℝ)≤1-t),max_eq_right (by norm_num : (0:ℝ)≤1),
      min_eq_right (by linarith : t≤1),max_eq_left ht]
    ring
  by_cases h1 : 1≤t
  · rw [min_eq_right (by linarith : 1-t≤(1:ℝ)),max_eq_left (by linarith : 1-t≤0),
      min_eq_left h1,max_eq_right (by norm_num : (0:ℝ)≤1)]
    ring
  · rw [min_eq_right (by linarith : 1-t≤(1:ℝ)),max_eq_right (by linarith : 0≤1-t),
      min_eq_right (by linarith : t≤1),max_eq_right (by linarith : 0≤t)]

end
end jacobi.Trichotomy
