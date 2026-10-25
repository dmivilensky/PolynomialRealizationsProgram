import chebyshev2.Residual.LevelSets
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
Article: chebyshev2, Lemma 11.
A contraction estimate for scalar absolutely continuous damped flows.
Use: `chebyshev2.Comparison.abs_le_integral_forcing` feeds
`chebyshev2.Calibration.Data.leftFilter_parameter_bound` (left Filter parameter bound).
Proof chain: `chebyshev2.DualCertificate.Data.admissible_stable` — chebyshev2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.Comparison
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.Residual
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `|f q| ≤ ∫ x in a..q, |e x|`.

Use: `chebyshev2.Calibration.Data.leftFilter_parameter_bound` uses this bound to establish
the stated quantitative bound `|C.leftFilter hκ s q-C.leftFilter hk s q| ≤ C.filterError κ k
s`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Separate `f x=0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Use the proved fundamental theorem of calculus with its explicit
integrability and endpoint hypotheses. Intersect the eventual or almost-everywhere hypotheses,
then prove the asserted relation at an arbitrary point in that intersection.
-/
theorem abs_le_integral_forcing {f c e : ℝ → ℝ} {a b q : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (he : IntervalIntegrable e volume a b)
    (h0 : f a=0) (hc : ∀ x ∈ Ioo a b, 0 ≤ c x)
    (hd : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt f (-c x*f x+e x) x)
    (hq : q ∈ Icc a b) : |f q| ≤ ∫ x in a..q, |e x| := by
  -- Separate `f x=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have hab : a ≤ b := hq.1.trans hq.2
  have hF : AbsolutelyContinuousOnInterval (fun x => |f x|) a b := by
    convert! lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hf using 1
  have hsub : uIcc a q ⊆ uIcc a b := by
    rw [uIcc_of_le hq.1,uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hq.2
  have hFa := hF.mono hsub
  have hqint : IntervalIntegrable (fun x => |e x|) volume a q :=
    by simpa only [Real.norm_eq_abs] using (he.norm.mono_set hsub)
  have hz : ∀ᵐ x, x ≠ a ∧ x ≠ b := by
    filter_upwards [show ∀ᵐ x : ℝ, x ≠ a by simp [ae_iff],show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff]] with x ha hb
    exact ⟨ha,hb⟩
  have hle : (fun x => deriv (fun t => |f t|) x) ≤ᵐ[volume.restrict (Icc a q)]
      (fun x => |e x|) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hz,ae_restrict_of_ae hd,
      ae_restrict_of_ae hF.ae_differentiableAt,
      ae_restrict_of_ae (derivative_zero_on_level_ae (fun x => |f x|) 0)]
      with x hx hne hder hdiff hzero
    have hxi : x ∈ Ioo a b :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hne.1),lt_of_le_of_ne (hx.2.trans hq.2) hne.2⟩
    have hxf : x ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨hx.1,hx.2.trans hq.2⟩
    by_cases hfx : f x=0
    · have h := hzero (by simp only [hfx,abs_zero]) _ (hdiff hxf).hasDerivAt
      rw [h]
      exact abs_nonneg _
    · rcases lt_or_gt_of_ne hfx with hn | hp
      · have h := (hasDerivAt_abs_neg hn).comp x (hder hxi)
        have heq : deriv (fun t => |f t|) x=_ := h.deriv
        rw [heq]
        have hdamp : c x*f x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hc x hxi) hn.le
        simpa only [neg_one_mul] using (show -(-c x*f x+e x) ≤ |e x| by
          linarith [neg_le_abs (e x)])
      · have h := (hasDerivAt_abs_pos hp).comp x (hder hxi)
        have heq : deriv (fun t => |f t|) x=_ := h.deriv
        rw [heq]
        have hdamp : 0 ≤ c x*f x := mul_nonneg (hc x hxi) hp.le
        simpa only [one_mul] using (show -c x*f x+e x ≤ |e x| by linarith [le_abs_self (e x)])
  have h := intervalIntegral.integral_mono_ae_restrict hq.1 hFa.intervalIntegrable_deriv hqint hle
  rw [hFa.integral_deriv_eq_sub,h0,abs_zero,sub_zero] at h
  exact h

end
end chebyshev2.Comparison
