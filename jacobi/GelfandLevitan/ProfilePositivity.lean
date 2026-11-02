import jacobi.GelfandLevitan.ProfileFrequency
import jacobi.GelfandLevitan.ProfileSeries

/-!
Article: jacobi, Proposition 2.2.
The actual persymmetric profile is strictly positive at every original
interior point. The argument uses one nonzero genuine spectral wave,
proved by the source's entire-function uniqueness argument, and the
positive original norming and edge weights in the unchanged series.
Use: Proposition C.4's intrinsic coordinate has a genuine positive continuous reciprocal on (0,1), so no internal zero can obstruct packing or its inverse.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference

/-- The actual source profile is strictly positive at every original physical interior point.
Use: Proposition C.4's intrinsic coordinate has a genuine positive continuous reciprocal on (0,1), so no internal zero can obstruct packing or its inverse.
Article: jacobi, Proposition 2.2.
Proof: the original folded coordinate is positive in the physical
interior. Jensen uniqueness and the actual negative-energy lower bound
give a nonzero genuine target wave there. Its positive edge/norming
multiple is a strictly positive term of the true nonnegative summable
profile series, hence is at most its positive sum. -/
theorem persymmetricProfile_pos (a:ℝ) (ha:-1<a) (t:Interval)
    (ht:(t:ℝ)∈Ioo (0:ℝ) 1) : 0<persymmetricProfile a ha t := by
  -- Reflection is already built into the same actual folded profile, including the midpoint.
  have hfold : 0<(physicalFold t:ℝ) := lt_min ht.1 (by linarith [ht.2])
  obtain ⟨k,hk⟩ := transformed_spectral_nonvanishing a ha (physicalFold t) hfold
  have hu : realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) (physicalFold t)≠0 := by
    intro hz
    apply hk
    rw [← realTransformedSolution_cast,hz,Complex.ofReal_zero]
  have hPhi : 0<spectralProfile a ha k t := mul_pos
    (div_pos (normingRatio_properties ha k).2 (norming_pos ha k)) (sq_pos_of_ne_zero hu)
  have hs := (ContinuousMap.evalCLM ℝ t).hasSum (profileSeries_summable a ha).hasSum
  have hn (i:ℕ) : 0≤ jacobi.Bessel.edgeValue a ha i*spectralProfile a ha i t :=
    mul_nonneg ((jacobi.Bessel.edgeValue_properties ha).1 i).le (spectralProfile_nonneg a ha i t)
  rw [persymmetricProfile_apply]
  exact (mul_pos ((jacobi.Bessel.edgeValue_properties ha).1 k) hPhi).trans_le
    (hs.summable.le_tsum k (fun i _ => hn i))

end
end jacobi.GelfandLevitan
