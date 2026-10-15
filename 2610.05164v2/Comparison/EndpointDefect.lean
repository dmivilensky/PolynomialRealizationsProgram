import «2610.05164v2».Comparison.LeftFilters
import «2610.05164v2».Comparison.ReciprocalContinuity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Article: 2610.05164v2, Theorem 3.6.
The q^(7/3) defect estimate in Lemma 13.
Use: `«2610.05164v2».Comparison.endpoint_defect_bound` feeds
`«2610.05164v2».Calibration.Data.leftLinearDefect_endpoint_bound` (left Linear Defect endpoint
bound).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_stable` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».Comparison
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».Calibration
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `f b-f a ≤ ∫ x in a..b, e x`.

Use: `«2610.05164v2».Comparison.endpoint_defect_bound` uses this bound to establish establishes
the uniform, quantified assertion `∀ q ∈ Icc (0:ℝ) 2, w q ≤ max (K*(1+a)*(3/7)) 2*q^(7/3:ℝ)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem ac_sub_le_integral {f e : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (he : IntervalIntegrable e volume a b)
    (hab : a ≤ b) (hd : ∀ᵐ x, x ∈ Ioo a b → deriv f x ≤ e x) :
    f b-f a ≤ ∫ x in a..b, e x := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  rw [← hf.integral_deriv_eq_sub]
  apply intervalIntegral.integral_mono_ae_restrict hab hf.intervalIntegrable_deriv he
  filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hd,
    ae_restrict_of_ae (show ∀ᵐ x : ℝ, x ≠ a by simp [ae_iff]),
    ae_restrict_of_ae (show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff])] with x hx hder ha hb
  exact hder ⟨lt_of_le_of_ne hx.1 (Ne.symm ha),lt_of_le_of_ne hx.2 hb⟩

/--
A common scalar argument for the nonlinear and linear filter defects.

Establishes the uniform, quantified assertion `∀ q ∈ Icc (0:ℝ) 2, w q ≤ max (K*(1+a)*(3/7))
2*q^(7/3:ℝ)`.

Use: `«2610.05164v2».Calibration.Data.leftDefect_endpoint_bound` uses this bound to establish
the stated quantitative bound `C.leftDefect hκ s q ≤ C.defectConstant κ s*q^(7/3:ℝ)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Separate `q ≤ 1` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem endpoint_defect_bound {w d : ℝ → ℝ} {a K : ℝ}
    (ha : 0 ≤ a) (_hK : 0 ≤ K) (hw : AbsolutelyContinuousOnInterval w 0 2)
    (h0 : w 0=0) (hb : ∀ q ∈ Icc (0:ℝ) 2, w q ∈ Icc (0:ℝ) q)
    (hd : ∀ q ∈ Ioo (0:ℝ) 2, 0 < d q)
    (hrec : ∀ q ∈ Ioo (0:ℝ) 1, (d q)⁻¹ ≤ K*q^(-(2/3:ℝ)))
    (hder : ∀ q ∈ Ioo (0:ℝ) 2, HasDerivAt w
      (((1+a)*q^2-2*(1+a*q)*w q+a*(w q)^2)/d q) q) :
    ∀ q ∈ Icc (0:ℝ) 2, w q ≤ max (K*(1+a)*(3/7)) 2*q^(7/3:ℝ) := by
  -- Separate `q ≤ 1` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  intro q hq
  by_cases hsmall : q ≤ 1
  · have hsub : uIcc (0:ℝ) q ⊆ uIcc (0:ℝ) 2 := by
      rw [uIcc_of_le hq.1,uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)]
      exact Icc_subset_Icc le_rfl hq.2
    have he : IntervalIntegrable (fun t : ℝ => K*(1+a)*t^(4/3:ℝ)) volume 0 q :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
    have hle : ∀ᵐ t, t ∈ Ioo (0:ℝ) q → deriv w t ≤ K*(1+a)*t^(4/3:ℝ) := by
      apply Eventually.of_forall
      intro t ht
      have ht2 : t ∈ Ioo (0:ℝ) 2 := ⟨ht.1,ht.2.trans_le hq.2⟩
      have ht1 : t ∈ Ioo (0:ℝ) 1 := ⟨ht.1,ht.2.trans_le hsmall⟩
      have hw := hb t ⟨ht.1.le,ht2.2.le⟩
      rw [(hder t ht2).deriv]
      have hn : -2*(1+a*t)*w t+a*(w t)^2 ≤ 0 := by
        have h1 : a*w t*(w t-2*t) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha hw.1) (by linarith [hw.2,ht.1])
        nlinarith [hw.1]
      calc
        _ ≤ (1+a)*t^2/d t := div_le_div_of_nonneg_right (by linarith) (hd t ht2).le
        _ ≤ (1+a)*t^2*(K*t^(-(2/3:ℝ))) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (hrec t ht1) (by positivity)
        _ = K*(1+a)*t^(4/3:ℝ) := by
          have hp : t^2*t^(-(2/3:ℝ))=t^(4/3:ℝ) := by
            rw [← rpow_natCast t 2,← rpow_add ht.1]
            norm_num
          calc
            _ = K*(1+a)*(t^2*t^(-(2/3:ℝ))) := by ring
            _ = _ := by rw [hp]
    have h := ac_sub_le_integral (hw.mono hsub) he hq.1 hle
    rw [h0,sub_zero,intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num : (-1:ℝ) < 4/3))] at h
    norm_num at h
    have hpow : 0 ≤ q^(7/3:ℝ) := rpow_nonneg hq.1 _
    calc
      _ ≤ K*(1+a)*(3/7)*q^(7/3:ℝ) := by convert h using 1; ring
      _ ≤ max (K*(1+a)*(3/7)) 2*q^(7/3:ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
  · have hlarge : 1 ≤ q := (not_le.mp hsmall).le
    have hp : 1 ≤ q^(7/3:ℝ) := one_le_rpow hlarge (by norm_num)
    have hM : 2 ≤ max (K*(1+a)*(3/7)) 2 := le_max_right _ _
    exact ((hb q hq).2.trans hq.2).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ max (K*(1+a)*(3/7)) 2 by positivity)])

end
end «2610.05164v2».Comparison
