import «2610.05164v2».DualCertificate.PriceAssembly
import «2610.05164v2».DualCertificate.CellIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Article: 2610.05164v2, Lemma 16.
Exact formula (31) for the constructed price and literal rational cells.
Use: `«2610.05164v2».DualCertificate.Data.price_cost_cells` feeds
`«2610.05164v2».DualCertificate.Data.priceCost_continuous` (price Cost continuous).
Proof chain: `«2610.05164v2».DualCertificate.Data.uniform_finite_lower_bound` — 2610.05164v2,
Theorem 3.6; admissible certificates imply continuum, finite-fiber and gain bounds.
-/
namespace «2610.05164v2».DualCertificate.Data
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Calculus «2610.05164v2».Residual
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (D : «2610.05164v2».DualCertificate.Data)

/--
Exact identity `D.cellPrice (t^3)=(D.cells Side.left).value t`.

Use: `«2610.05164v2».DualCertificate.Data.price_integral_cubic` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.cube_mem` with the
arguments shown in the proof.
-/
theorem cellPrice_left {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    D.cellPrice (t^3)=(D.cells Side.left).value t := by
  unfold cellPrice cubicSides
  rw [ite_eq_left (cube_mem ht).2]
  exact congrArg _ (Real.pow_rpow_inv_natCast ht.1 (by decide : 3≠0))

/--
Exact identity `D.cellPrice (2-t^3)=(D.cells Side.right).value t`.

Use: `«2610.05164v2».DualCertificate.Data.price_integral_cubic` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem cellPrice_right {t : ℝ} (ht : t∈Ico (0:ℝ) 1) :
    D.cellPrice (2-t^3)=(D.cells Side.right).value t := by
  have hc : t^3<1 := pow_lt_one₀ ht.1 ht.2 (by decide : 3≠0)
  unfold cellPrice cubicSides
  rw [ite_eq_right (by linarith : ¬2-t^3≤1),sub_sub_cancel]
  exact congrArg _ (Real.pow_rpow_inv_natCast ht.1 (by decide : 3≠0))

/--
The precise assertion is `(∫ q in Ioo (0:ℝ) 2,D.calibration.amplitude κ q*D.cellPrice q)= (∫ t
in Icc (0:ℝ) 1,3*t^3*D.normalization.root κ t*(D.cells Side.left).value t)+ (∫ t in Icc (0:ℝ)
1,3*t^3*D.normalization.root κ t*(D.cells Side.right).value t)`.

Use: `«2610.05164v2».DualCertificate.Data.price_cost_cells` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem price_integral_cubic {κ : ℝ} (hκ : 0<κ) :
    (∫ q in Ioo (0:ℝ) 2,D.calibration.amplitude κ q*D.cellPrice q)=
      (∫ t in Icc (0:ℝ) 1,3*t^3*D.normalization.root κ t*(D.cells Side.left).value t)+
      (∫ t in Icc (0:ℝ) 1,3*t^3*D.normalization.root κ t*(D.cells Side.right).value t) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let f : ℝ → ℝ := fun q => D.calibration.amplitude κ q*D.cellPrice q
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : IntegrableOn f (Ioo (0:ℝ) 2) := by
    apply (D.calibration.amplitude_mul_price_integrable hκ D.cellPriceData).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    exact congrArg (fun e => D.calibration.amplitude κ q*e) (D.cellPriceData_eq ⟨hq.1.le,hq.2.le⟩)
  have hii : IntervalIntegrable f volume 0 2 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ)≤2)).mpr
      ((integrableOn_Icc_iff_integrableOn_Ioo (μ := volume) (f := f)).mpr hi)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (a := (0:ℝ)) (b := 1) (c := 2)
    (hii.mono_set (by simp only [uIcc_of_le (by norm_num : (0:ℝ)≤1),uIcc_of_le (by norm_num : (0:ℝ)≤2)];intro q hq;exact ⟨hq.1,by linarith [hq.2]⟩))
    (hii.mono_set (by simp only [uIcc_of_le (by norm_num : (1:ℝ)≤2),uIcc_of_le (by norm_num : (0:ℝ)≤2)];intro q hq;exact ⟨by linarith [hq.1],hq.2⟩))
  have hleft := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun t : ℝ => t^3) (f' := fun t => 3*t^2) (g := f) (a := 0) (b := 1)
    (by fun_prop) (fun t _ => by convert! (hasDerivAt_id t).pow 3 using 1;norm_num)
    (fun t _ => by positivity)
  have hright := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (f := fun t : ℝ => 2-t^3) (f' := fun t => -3*t^2) (g := f) (a := 0) (b := 1)
    (by fun_prop) (fun t _ => by convert! ((hasDerivAt_id t).pow 3).const_sub 2 using 1;norm_num)
    (fun t _ => by nlinarith [sq_nonneg t])
  norm_num only [zero_pow (by decide : 3≠0),one_pow,sub_zero,show (2:ℝ)-1=1 by norm_num] at hleft hright
  have hli : (∫ q in (0:ℝ)..1,f q)=
      ∫ t in (0:ℝ)..1,3*t^3*D.normalization.root κ t*(D.cells Side.left).value t := by
    rw [← hleft]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    dsimp [f,Function.comp_def]
    rw [← D.normalization_calibration,D.normalization.root_amplitude hκ ht,D.cellPrice_left ht]
    ring
  have hri : (∫ q in (1:ℝ)..2,f q)=
      ∫ t in (0:ℝ)..1,3*t^3*D.normalization.root κ t*(D.cells Side.right).value t := by
    rw [intervalIntegral.integral_symm (a := 1) (b := 2)] at hright
    have hne : ∀ᵐ t : ℝ,t≠1 := by
      simpa only [mem_singleton_iff] using
        (measure_eq_zero_iff_ae_notMem (μ := volume)).mp (by simp : volume ({(1:ℝ)} : Set ℝ)=0)
    have he : (∫ t in (0:ℝ)..1,f (2-t^3)*(-3*t^2))=
        -(∫ t in (0:ℝ)..1,3*t^3*D.normalization.root κ t*(D.cells Side.right).value t) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hne] with t ht hti
      rw [uIoc_of_le zero_le_one] at hti
      have hclosed : t∈Icc (0:ℝ) 1 := ⟨hti.1.le,hti.2⟩
      dsimp only [f]
      have hamp := D.normalization.side_amplitude (fun _ hq => D.Gamma_symmetric hq) Side.right hκ hclosed
      dsimp only [Side.q] at hamp
      rw [← D.normalization_calibration,hamp,D.cellPrice_right ⟨hti.1.le,lt_of_le_of_ne hti.2 ht⟩]
      ring
    simp only [Function.comp_def] at hright
    rw [he] at hright
    exact neg_injective hright.symm
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤2),
    ← hsplit,hli,hri,intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc,← integral_Icc_eq_integral_Ioc]

 /--
The precise assertion is `priceCost κ (D.τ:ℝ) (D.price hκ).value= ((∑ i,∫ t in Icc ((D.cells
Side.left).lo i:ℝ) ((D.cells Side.left).hi i:ℝ), 3*t^3*D.normalization.root κ t*(D.cells
Side.left).affine i t)+ (∑ i,∫ t in Icc ((D.cells Side.right).lo i:ℝ) ((D.cells Side.right).hi
i:ℝ), 3*t^3*D.normalization.root κ t*(D.cells Side.right).affine i t))/κ+ (D.τ:ℝ)*(1-∫
x,D.calibration.comparisonDensity hκ x)`.

Use: `«2610.05164v2».DualCertificate.Data.priceCost_continuous` uses this identity to establish
continuity of the displayed function: `Continuous (fun κ : Ioi (0:ℝ) => priceCost κ (D.τ:ℝ)
(D.price κ.property).value)`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.Data.price_cost`,
`«2610.05164v2».DualCertificate.Data.price_integral_cubic`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.root_smooth_fixed` with the arguments
shown in the proof.
-/
theorem price_cost_cells {κ : ℝ} (hκ : 0<κ) :
    priceCost κ (D.τ:ℝ) (D.price hκ).value=
      ((∑ i,∫ t in Icc ((D.cells Side.left).lo i:ℝ) ((D.cells Side.left).hi i:ℝ),
        3*t^3*D.normalization.root κ t*(D.cells Side.left).affine i t)+
       (∑ i,∫ t in Icc ((D.cells Side.right).lo i:ℝ) ((D.cells Side.right).hi i:ℝ),
        3*t^3*D.normalization.root κ t*(D.cells Side.right).affine i t))/κ+
      (D.τ:ℝ)*(1-∫ x,D.calibration.comparisonDensity hκ x) := by
  -- Use the identities/estimates `«2610.05164v2».DualCertificate.Data.price_cost`,
  -- `«2610.05164v2».DualCertificate.Data.price_integral_cubic`,
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.root_smooth_fixed` with the
  -- arguments shown in the proof.
  rw [D.price_cost hκ,D.price_integral_cubic hκ]
  -- Establish continuity hw before using the function at limits or in calculus arguments.
  have hw : ContinuousOn (fun t => 3*t^3*D.normalization.root κ t) (Icc (0:ℝ) 1) :=
    (continuousOn_const.mul (continuousOn_id.pow 3)).mul
      (D.normalization.root_smooth_fixed hκ).continuousOn
  rw [(D.cells Side.left).weighted_integral hw,(D.cells Side.right).weighted_integral hw]

end
end «2610.05164v2».DualCertificate.Data
