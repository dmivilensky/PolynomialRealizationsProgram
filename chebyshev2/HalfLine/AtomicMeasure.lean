import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
Article: chebyshev2, Theorem 3.3.
A countable weighted atomic measure; zero weights and repeated atoms are allowed.
Use: `chebyshev2.HalfLine.atomicMeasure_integral` feeds
`chebyshev2.HalfLine.commonMeasure_response` (A single measure represents every nonnegative
scale, including s=0).
Proof chain: `chebyshev2.HalfLine.commonMeasure_filter` — chebyshev2, Theorem 3.3; A common
compact probability measure for all scales.
-/
namespace chebyshev2.HalfLine
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/--
A countable weighted atomic measure; zero weights and repeated atoms are allowed.

Use: `chebyshev2.HalfLine.atomicMeasure_integral` rewrites with this definition to
establish exact identity `(∫ t, F t ∂atomicMeasure w z)=∑' i, w i*F (z i)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.
-/
def atomicMeasure {ι : Type*} (w z : ι → ℝ) : Measure ℝ :=
  Measure.sum (fun i => ENNReal.ofReal (w i) • Measure.dirac (z i))

/--
The precise assertion is `IsProbabilityMeasure (atomicMeasure w z)`.

Use: `chebyshev2.HalfLine.commonMeasure_probability` uses this assertion to establish the
precise assertion is `IsProbabilityMeasure (commonMeasure G x)`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem atomicMeasure_probability {ι : Type*} {w z : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) : IsProbabilityMeasure (atomicMeasure w z) := by
  constructor
  simp only [atomicMeasure,Measure.sum_apply _ MeasurableSet.univ,Measure.smul_apply,
    measure_univ,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg hw hs.summable,hs.tsum_eq,ENNReal.ofReal_one]

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ t ∂atomicMeasure w z, t ∈
A`.

Use: `chebyshev2.HalfLine.commonMeasure_supported` uses this assertion to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ z ∂commonMeasure G x, z ∈
Ico (0:ℝ) 1`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_defect`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem atomicMeasure_supported {ι : Type*} [Countable ι] {w z : ι → ℝ} {A : Set ℝ}
    (hA : MeasurableSet A) (hz : ∀ i, z i ∈ A) : ∀ᵐ t ∂atomicMeasure w z, t ∈ A := by
  apply Measure.ae_sum_iff.mpr
  intro i
  exact Measure.ae_smul_measure ((ae_dirac_iff hA).mpr (hz i)) _

/--
Exact identity `(∫ t, F t ∂atomicMeasure w z)=∑' i, w i*F (z i)`.

Use: `chebyshev2.HalfLine.commonMeasure_response` rewrites with this identity to establish
the precise assertion is `(∫ z, (1-z)/(1+(s/groundParameter hm hn)*z) ∂commonMeasure G x)=
groundParameter hm hn/groundQuadratic G x*responseQuadratic (hm := hm) (hn := hn) x s hs`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_filter`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem atomicMeasure_integral {ι : Type*} [Countable ι] {w z : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (F : ℝ → ℝ) :
    (∫ t, F t ∂atomicMeasure w z)=∑' i, w i*F (z i) := by
  rw [atomicMeasure,integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (hw _),smul_eq_mul]

end
end chebyshev2.HalfLine
