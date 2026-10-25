import chebyshev2.PrescribedSpeed.ChangeVariables
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
Article: chebyshev2, Theorem 5.1.
The actual derivative of the global inverse; endpoint values are immaterial.
Use: `chebyshev2.PrescribedSpeed.SpeedData.speed_bound` feeds
`chebyshev2.PrescribedSpeed.SpeedData.density_bound` (density bound).
Proof chain: `chebyshev2.PrescribedSpeed.SpeedData.density_integrable` — chebyshev2, Theorem
5.1; General measurable speed gives a density with the prescribed ground parameter.
-/
namespace chebyshev2.PrescribedSpeed
noncomputable section
open Set MeasureTheory Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace SpeedData
variable (S : SpeedData)

/--
Membership in the specified domain/enclosure: `S.q x ∈ Ioo (0:ℝ) 2`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.q_derivative_of_X` uses this assertion to
establish the actual derivative at the stated point: `HasDerivAt S.q (S.D (S.q x)) x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem q_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (S.X 0) (S.X 2)) :
    S.q x ∈ Ioo (0:ℝ) 2 := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  have hmem := S.q_mem x
  have he := S.X_q ⟨hx.1.le,hx.2.le⟩
  constructor
  · by_contra hn
    have hz : S.q x=0 := le_antisymm (le_of_not_gt hn) hmem.1
    rw [hz] at he
    exact (ne_of_lt hx.1) he
  · by_contra hn
    have ht : S.q x=2 := le_antisymm hmem.2 (le_of_not_gt hn)
    rw [ht] at he
    exact (ne_of_gt hx.2) he

/--
The actual derivative at the stated point: `HasDerivAt S.q (S.D (S.q x)) x`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.q_derivative_inside` uses this derivative
formula to prove the eventual or almost-everywhere assertion `∀ᵐ x
∂volume.restrict (Ioo (S.X 0) (S.X 2)), HasDerivAt S.q (S.D (S.q x)) x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem q_derivative_of_X {x : ℝ} (hx : x ∈ Ioo (S.X 0) (S.X 2))
    (hX : HasDerivAt S.X (S.reciprocal (S.q x)) (S.q x)) :
    HasDerivAt S.q (S.D (S.q x)) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hqin := S.q_mem_Ioo hx
  rw [reciprocal,indicator_of_mem hqin] at hX
  have hlocal : ∀ᶠ y in 𝓝 x, S.X (S.q y)=y := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact S.X_q ⟨hy.1.le,hy.2.le⟩
  simpa only [inv_inv] using HasDerivAt.of_local_left_inverse S.q_continuous.continuousAt hX
    (inv_ne_zero (ne_of_gt (S.positive _ hqin))) hlocal

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x ∂volume.restrict (Ioo (S.X
0) (S.X 2)), HasDerivAt S.q (S.D (S.q x)) x`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae` uses this assertion to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x ∂volume,
HasDerivAt S.q (S.speed x) x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem q_derivative_inside :
    ∀ᵐ x ∂volume.restrict (Ioo (S.X 0) (S.X 2)), HasDerivAt S.q (S.D (S.q x)) x := by
  have hX := S.q_ae_transfer S.X_derivative_ae
  have hXi := hX.filter_mono (MeasureTheory.ae_mono (Measure.restrict_mono Ioo_subset_Icc_self le_rfl))
  filter_upwards [hXi,ae_restrict_mem measurableSet_Ioo] with x hx hi
  exact S.q_derivative_of_X hi hx

/--
The actual derivative at the stated point: `HasDerivAt S.q 0 x`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae` uses this derivative formula to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x ∂volume,
HasDerivAt S.q (S.speed x) x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem q_derivative_left {x : ℝ} (hx : x < S.X 0) : HasDerivAt S.q 0 x := by
  apply (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
  exact S.q_zero_left hy.le

/--
The actual derivative at the stated point: `HasDerivAt S.q 0 x`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae` uses this derivative formula to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x ∂volume,
HasDerivAt S.q (S.speed x) x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem q_derivative_right {x : ℝ} (hx : S.X 2 < x) : HasDerivAt S.q 0 x := by
  apply (hasDerivAt_const x (2:ℝ)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact S.q_two_right hy.le

/--
The actual derivative of the global inverse; endpoint values are immaterial.

Use: `chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae` rewrites with this definition
to prove the eventual or almost-everywhere assertion `∀ᵐ x ∂volume,
HasDerivAt S.q (S.speed x) x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.
-/
def speed (x : ℝ) : ℝ := (Ioo (S.X 0) (S.X 2)).indicator (fun x => S.D (S.q x)) x

/--
Measurability of the displayed map: `Measurable S.speed`.

Use: a standalone supporting measurability result for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 5.1.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_continuous`
with the arguments shown in the proof.
-/
theorem speed_measurable : Measurable S.speed :=
  (S.measurable.comp S.q_continuous.measurable).indicator measurableSet_Ioo

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x ∂volume, HasDerivAt S.q
(S.speed x) x`.

Use: `chebyshev2.Calibration.Data.comparisonCoordinate_derivative` uses this assertion to
establish the actual derivative at the stated point: `HasDerivAt (C.comparisonSpeed hκ).q
(κ*C.comparisonDensity hκ x-chebyshev2.Calibration.Q ((C.comparisonSpeed hκ).q x)) x`.

Article: chebyshev2, Theorem 5.1.

Proof: Separate `x ∈ Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then
prove the asserted relation at an arbitrary point in that intersection.
-/
theorem q_derivative_ae : ∀ᵐ x ∂volume, HasDerivAt S.q (S.speed x) x := by
  -- Separate `x ∈ Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  have hi := ae_imp_of_ae_restrict S.q_derivative_inside
  have hleft : ∀ᵐ x ∂volume, x ≠ S.X 0 := by simp [ae_iff]
  have hright : ∀ᵐ x ∂volume, x ≠ S.X 2 := by simp [ae_iff]
  filter_upwards [hi,hleft,hright] with x hi hl hr
  by_cases hx : x ∈ Ioo (S.X 0) (S.X 2)
  · simpa only [speed,indicator_of_mem hx] using hi hx
  · rw [speed,indicator_of_notMem hx]
    rcases le_or_gt x (S.X 0) with h | h
    · exact S.q_derivative_left (lt_of_le_of_ne h hl)
    · have hxright : S.X 2 < x := lt_of_le_of_ne (not_lt.mp (fun hc => hx ⟨h,hc⟩)) hr.symm
      exact S.q_derivative_right hxright

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x ∂volume, S.speed x ≤ S.B`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.density_bound` uses this bound to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ x ∂volume, S.density κ x ≤
(S.B+1)/κ`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`.

Proof: Separate `x ∈ Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then
prove the asserted relation at an arbitrary point in that intersection.
-/
theorem speed_bound : ∀ᵐ x ∂volume, S.speed x ≤ S.B := by
  -- Separate `x ∈ Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  have hbound := S.q_ae_transfer (ae_imp_of_ae_restrict S.bound)
  have hi := ae_imp_of_ae_restrict hbound
  filter_upwards [hi] with x hi
  by_cases hx : x ∈ Ioo (S.X 0) (S.X 2)
  · rw [speed,indicator_of_mem hx]
    exact hi ⟨hx.1.le,hx.2.le⟩ (S.q_mem_Ioo hx)
  · rw [speed,indicator_of_notMem hx]
    exact S.bound_positive.le

/--
The stated quantitative bound `0 ≤ S.speed x`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 5.1.

Proof: Separate `x ∈ Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem speed_nonneg (x : ℝ) : 0 ≤ S.speed x := by
  by_cases hx : x ∈ Ioo (S.X 0) (S.X 2)
  · rw [speed,indicator_of_mem hx]
    exact (S.positive _ (S.q_mem_Ioo hx)).le
  · simp only [speed,indicator_of_notMem hx,le_refl]

end SpeedData
end
end chebyshev2.PrescribedSpeed
