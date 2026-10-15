import «2610.05164v2».DualCertificate.CenteredCoefficients
import «2610.05164v2».Residual.RegularPrice

/-!
Article: 2610.05164v2, Lemma 16.
The actual two-sided affine-cell price of Definition 7(iv), its bounded piecewise continuous
extension, and the price cost before cell subdivision.
Use: `«2610.05164v2».DualCertificate.Data.price_cost` feeds
`«2610.05164v2».DualCertificate.Data.price_cost_cells` (price cost cells).
Proof chain: `«2610.05164v2».DualCertificate.Data.uniform_finite_lower_bound` — 2610.05164v2,
Theorem 3.6; admissible certificates imply continuum, finite-fiber and gain bounds.
-/
namespace «2610.05164v2».DualCertificate.Data
noncomputable section
open Set Filter Real MeasureTheory «2610.05164v2».Calculus «2610.05164v2».Residual
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (D : «2610.05164v2».DualCertificate.Data)

/--
Defines `cellPrice` of type `ℝ` by `cubicSides (D.cells Side.left).value (D.cells
Side.right).value q`.

Use: `«2610.05164v2».DualCertificate.Data.cellPriceData` uses this definition in the displayed
construction of `cellPriceData`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def cellPrice (q : ℝ) : ℝ := cubicSides (D.cells Side.left).value (D.cells Side.right).value q

/--
Defines `priceBreaks` of type `Finset ℝ` by `insert 0 (insert 1 (insert 2 (((D.cells
Side.left).endpoints.image (Side.q Side.left)) ∪ ((D.cells Side.right).endpoints.image (Side.q
Side.right)))))`.

Use: `«2610.05164v2».DualCertificate.Data.cellPriceData` uses this definition in the displayed
construction of `cellPriceData`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def priceBreaks : Finset ℝ := insert 0 (insert 1 (insert 2
  (((D.cells Side.left).endpoints.image (Side.q Side.left)) ∪
    ((D.cells Side.right).endpoints.image (Side.q Side.right)))))

/--
The stated quantitative bound `‖D.cellPrice q‖≤(D.cells Side.left).bound+(D.cells
Side.right).bound`.

Use: `«2610.05164v2».DualCertificate.Data.cellPriceData` uses this bound in the displayed
construction of `cellPriceData`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.Cells.value_bound`,
`«2610.05164v2».DualCertificate.Cells.bound_nonneg` with the arguments shown in the proof.
-/
theorem cellPrice_bound (q : ℝ) : ‖D.cellPrice q‖≤(D.cells Side.left).bound+(D.cells Side.right).bound := by
  unfold cellPrice cubicSides
  split_ifs
  · exact ((D.cells Side.left).value_bound _).trans
      (le_add_of_nonneg_right (D.cells Side.right).bound_nonneg)
  · exact ((D.cells Side.right).value_bound _).trans
      (le_add_of_nonneg_left (D.cells Side.left).bound_nonneg)

/--
Continuity at the stated point: `ContinuousAt D.cellPrice q`.

Use: `«2610.05164v2».DualCertificate.Data.cellPriceData` uses this continuity result in the
displayed construction of `cellPriceData`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem cellPrice_continuousAt {q : ℝ} (hq : q∈Icc (0:ℝ) 2) (he : q∉D.priceBreaks) :
    ContinuousAt D.cellPrice q := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have h₁ : q≠1 := fun h => he (by simp [priceBreaks,h])
  rcases lt_or_gt_of_ne h₁ with hl | hr
  · have hne : cubeRoot q∉(D.cells Side.left).endpoints := by
      intro h
      apply he
      have hi : q∈(D.cells Side.left).endpoints.image (Side.q Side.left) := by
        apply Finset.mem_image.mpr
        exact ⟨cubeRoot q,h,cubeRoot_cube hq.1⟩
      simp only [priceBreaks,Finset.mem_insert,Finset.mem_union]
      exact Or.inr (Or.inr (Or.inr (Or.inl hi)))
    apply (((D.cells Side.left).value_continuousAt hne).comp cubeRoot_continuous.continuousAt).congr
    filter_upwards [gt_mem_nhds hl] with t ht
    simp only [cellPrice,cubicSides,ite_eq_left ht.le,Function.comp_apply]
  · have hne : cubeRoot (2-q)∉(D.cells Side.right).endpoints := by
      intro h
      apply he
      have hi : q∈(D.cells Side.right).endpoints.image (Side.q Side.right) := by
        apply Finset.mem_image.mpr
        refine ⟨cubeRoot (2-q),h,?_⟩
        dsimp [Side.q]
        rw [cubeRoot_cube (by linarith [hq.2])]
        ring
      simp only [priceBreaks,Finset.mem_insert,Finset.mem_union]
      exact Or.inr (Or.inr (Or.inr (Or.inr hi)))
    -- Establish continuity hc before using the function at limits or in calculus arguments.
    have hc : ContinuousAt (fun q => cubeRoot (2-q)) q :=
      cubeRoot_continuous.continuousAt.comp (continuousAt_const.sub continuousAt_id)
    apply (((D.cells Side.right).value_continuousAt hne).comp (f := fun q : ℝ => cubeRoot (2-q)) hc).congr
    filter_upwards [lt_mem_nhds hr] with t ht
    simp only [cellPrice,cubicSides,ite_eq_right (not_le.mpr ht),Function.comp_apply]

/--
Defines `cellPriceData` of type `Price` by `Price.ofInterval D.cellPrice D.priceBreaks
((D.cells Side.left).bound+(D.cells Side.right).bound) (add_nonneg (D.cells
Side.left).bound_nonneg (D.cells Side.right).bound_nonneg) (fun _ _ => D.cellPrice_bound _)
(fun _ hq he => (D.cellPrice_continuousAt hq he).continuousWithinAt)`.

Use: `«2610.05164v2».DualCertificate.Data.price` uses this definition in the displayed
construction of `price`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def cellPriceData : Price := Price.ofInterval D.cellPrice D.priceBreaks
  ((D.cells Side.left).bound+(D.cells Side.right).bound)
  (add_nonneg (D.cells Side.left).bound_nonneg (D.cells Side.right).bound_nonneg)
  (fun _ _ => D.cellPrice_bound _) (fun _ hq he => (D.cellPrice_continuousAt hq he).continuousWithinAt)

/--
Exact identity `D.cellPriceData.value q=D.cellPrice q`.

Use: `«2610.05164v2».DualCertificate.Data.price_cost` uses this identity to establish the
precise assertion is `priceCost κ (D.τ:ℝ) (D.price hκ).value= (∫ q in Ioo (0:ℝ)
2,D.calibration.amplitude κ q*D.cellPrice q)/κ+ (D.τ:ℝ)*(1-∫ x,D.calibration.comparisonDensity
hκ x)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem cellPriceData_eq {q : ℝ} (hq : q∈Icc (0:ℝ) 2) : D.cellPriceData.value q=D.cellPrice q :=
  indicator_of_mem hq _

/--
Defines `price` of type `Price` by `D.calibration.regularPriceData hκ (D.τ:ℝ) D.cellPriceData`.

Use: `«2610.05164v2».DualCertificate.Data.price_cost` rewrites with this definition to
establish the precise assertion is `priceCost κ (D.τ:ℝ) (D.price hκ).value= (∫ q in Ioo (0:ℝ)
2,D.calibration.amplitude κ q*D.cellPrice q)/κ+ (D.τ:ℝ)*(1-∫ x,D.calibration.comparisonDensity
hκ x)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def price {κ : ℝ} (hκ : 0<κ) : Price := D.calibration.regularPriceData hκ (D.τ:ℝ) D.cellPriceData

/--
The precise assertion is `(D.price hκ).value q= -(D.τ:ℝ)*«2610.05164v2».Calibration.Q
q/D.calibration.speed κ q+ D.calibration.amplitude κ q*D.cellPrice q`.

Use: `«2610.05164v2».DualCertificate.Data.normalized_residual_of_admissible` rewrites with this
identity to prove the quantified assertion `∀ n : ℝ,0≤n →
0≤D.calibration.stateResidual hκ D.ξ₀ D.ξ₁ D.χ D.τ (D.price hκ) (D.statePotential κ)
(PolynomialPotential.unnormalize κ (side.q t,U,V,θ)) n`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.Data.cellPriceData_eq` with
the arguments shown in the proof.
-/
theorem price_interior {κ q : ℝ} (hκ : 0<κ) (hq : q∈Ioo (0:ℝ) 2) :
    (D.price hκ).value q= -(D.τ:ℝ)*«2610.05164v2».Calibration.Q q/D.calibration.speed κ q+
      D.calibration.amplitude κ q*D.cellPrice q := by
  change D.calibration.regularPrice (κ := κ) (D.τ:ℝ) D.cellPriceData.value q=_
  rw [«2610.05164v2».Calibration.Data.regularPrice,indicator_of_mem hq,D.cellPriceData_eq ⟨hq.1.le,hq.2.le⟩]

/--
The precise assertion is `priceCost κ (D.τ:ℝ) (D.price hκ).value= (∫ q in Ioo (0:ℝ)
2,D.calibration.amplitude κ q*D.cellPrice q)/κ+ (D.τ:ℝ)*(1-∫ x,D.calibration.comparisonDensity
hκ x)`.

Use: `«2610.05164v2».DualCertificate.Data.price_cost_cells` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.regularPriceData_cost`,
`«2610.05164v2».DualCertificate.Data.cellPriceData_eq` with the arguments shown in the proof.
-/
theorem price_cost {κ : ℝ} (hκ : 0<κ) :
    priceCost κ (D.τ:ℝ) (D.price hκ).value=
      (∫ q in Ioo (0:ℝ) 2,D.calibration.amplitude κ q*D.cellPrice q)/κ+
        (D.τ:ℝ)*(1-∫ x,D.calibration.comparisonDensity hκ x) := by
  rw [price,D.calibration.regularPriceData_cost hκ]
  congr 2
  apply setIntegral_congr_fun measurableSet_Ioo
  exact fun q hq => congrArg (fun e => D.calibration.amplitude κ q*e) (D.cellPriceData_eq ⟨hq.1.le,hq.2.le⟩)

end
end «2610.05164v2».DualCertificate.Data
