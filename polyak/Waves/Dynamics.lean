import polyak.Waves.Mixture
import polyak.Dynamics.Normalization

/-!
Article: waves and spectra, eq:m and eq:normrec.
Use: the arbitrary-tuning multiplier and its actual Hilbert-space recurrence.
-/

namespace polyak.Waves
noncomputable section
open Spectral

/-- Article: eq:m. Use: a continuous multiplier for arbitrary tuning on cosine frequencies. -/
def multiplierMap (A B β t : ℝ) : C(Frequency, ℂ) where
  toFun c := multiplier A B β t (Real.arccos c)
  continuous_toFun := by
    unfold multiplier z
    fun_prop (disch := intro c; exact Complex.exp_ne_zero _)

/-- Article: eq:normrec. Use: the actual continuous maps already obey the recurrence. -/
theorem positionMap_recurrence (A B β t : ℝ) (hB : B ≠ 0) (k : ℕ) :
    positionMap t (some (k+2)) = A • positionMap t (some (k+1)) +
      B • gradientMap (multiplierMap A B β t) t (some (k+1)) -
        β • positionMap t (some k) := by
  ext c
  change z t (Real.arccos c) ^ (k+2) =
    A • z t (Real.arccos c) ^ (k+1) +
    B • (multiplier A B β t (Real.arccos c) * z t (Real.arccos c) ^ (k+1)) -
    β • z t (Real.arccos c) ^ k
  simpa only [Complex.real_smul] using recurrence A B β t (Real.arccos c) hB k

/-- Article: eq:normrec. Use: arbitrary probability spectra give genuine Hilbert trajectories.
Proof: apply the real linear L² realization map to the pointwise wave recurrence. -/
theorem mixture_recurrence (ν : Spectrum) (A B β t : ℝ) (hB : B ≠ 0) (k : ℕ) :
    mixturePosition ν t (some (k+2)) = A • mixturePosition ν t (some (k+1)) +
      B • mixtureGradient ν (multiplierMap A B β t) t (some (k+1)) -
        β • mixturePosition ν t (some k) := by
  unfold mixturePosition mixtureGradient
  rw [positionMap_recurrence A B β t hB k, map_sub, map_add, map_smul, map_smul, map_smul]

end
end polyak.Waves
