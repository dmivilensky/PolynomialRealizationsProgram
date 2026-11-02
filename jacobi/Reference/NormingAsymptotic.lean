import jacobi.Reference.NormingFirstOrder
import jacobi.Reference.NormingLogLinearization

/-!
Article: jacobi, Appendix C.2 (norming ratios).
The original infinite-product norming ratio has its full strengthened
asymptotic, with the genuine displacement sum as leading coefficient
and the printed inverse-cubic logarithmic remainder. No asymptotic
spectral-weight or regularity hypothesis is supplied by the caller.
Use: normingRatio_log_refined and normingRatio_asymptotic absorb the genuine logarithm and exponential quadratic remainders.
-/
namespace jacobi.Reference
noncomputable section
open Real Filter Asymptotics
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A nonnegative inverse-fourth error is absorbed by the common logarithmic inverse-cubic majorant at every original positive index.
Use: normingRatio_log_refined and normingRatio_asymptotic absorb the genuine logarithm and exponential quadratic remainders.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: 1/(k+1)<=1 and log(2*(k+1))>=0, so multiply the inverse-cubic scale by the resulting larger nonnegative factor. -/
theorem inverse_fourth_log_bound {T : ℝ} (hT : 0≤T) (k : ℕ) :
    T/(k+1:ℝ)^4≤T*(1+Real.log (2*(k+1:ℝ)))/(k+1:ℝ)^3 := by
  -- The bound includes every small original index, with no limiting convention at log(0).
  have hk : 1≤(k+1:ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hlog : 0≤Real.log (2*(k+1:ℝ)) := Real.log_nonneg (by linarith)
  have hi : 1/(k+1:ℝ)≤1+Real.log (2*(k+1:ℝ)) := by
    have h := one_div_le_one_div_of_le zero_lt_one hk
    norm_num only [div_one] at h
    linarith
  calc
    _ = (T/(k+1:ℝ)^3)*(1/(k+1:ℝ)) := by field_simp
    _ ≤ (T/(k+1:ℝ)^3)*(1+Real.log (2*(k+1:ℝ))) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

/-- The logarithm of the original norming ratio has the exact displacement-mass leading term and the logarithmic inverse-cubic error.
Use: normingRatio_asymptotic returns to the actual positive product through the proved quadratic exponential bound.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: subtract the actual first-order mass identity from the true product-logarithm linearization, then absorb its inverse-fourth error into the common logarithmic scale. -/
theorem normingRatio_log_refined {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∃ M : ℕ,∀ k : ℕ,M≤k →
      |Real.log (normingRatio a ha k)-displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2|≤
        C*(1+Real.log (2*(k+1:ℝ)))/(k+1:ℝ)^3 := by
  -- Both estimates concern the same original complete epsilon row, so its sum cancels exactly.
  obtain ⟨L,hL,M,hlog⟩ := norming_log_linearization ha
  obtain ⟨Q,hQ,hfirst⟩ := norming_first_order_bound ha
  refine ⟨L+Q,by positivity,M,fun k hk => ?_⟩
  have he : Real.log (normingRatio a ha k)-displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2=
      (Real.log (normingRatio a ha k)+(∑' l : ℕ,spectralPerturbation a ha k l))-
        ((∑' l : ℕ,spectralPerturbation a ha k l)+displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2) := by ring
  rw [he]
  exact ((abs_sub _ _).trans (add_le_add (hlog k hk) (hfirst k))).trans
    ((add_le_add (inverse_fourth_log_bound hL.le k) le_rfl).trans_eq (by ring))

/-- The difference between the actual positive norming ratio and one plus its own logarithm is uniformly inverse-fourth in the original index.
Use: normingRatio_asymptotic transfers the refined logarithmic expansion to the original infinite-product weights in F.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the actual logarithm is bounded by H/(k+1)^2 and hence by H. Apply the true exponential remainder, use exp(log(rho))=rho from positivity, and square the genuine logarithm bound. -/
theorem normingRatio_exponential_error {a : ℝ} (ha : -1<a) :
    ∃ B : ℝ,0<B ∧ ∀ k : ℕ,
      |normingRatio a ha k-1-Real.log (normingRatio a ha k)|≤B/(k+1:ℝ)^4 := by
  -- Positivity comes from convergence of the actual original product, before its logarithm is exponentiated.
  obtain ⟨H,hH,hlog⟩ := normingRatio_log_bound ha
  refine ⟨H^2*Real.exp H,by positivity,fun k => ?_⟩
  have hkpos : 0<(k+1:ℝ) := by positivity
  have hK : 1≤(k+1:ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have habs := (hlog k).trans (div_le_self hH.le hK)
  have hs := (sq_le_sq₀ (abs_nonneg (Real.log (normingRatio a ha k))) (by positivity : 0≤H/(k+1:ℝ)^2)).mpr (hlog k)
  rw [sq_abs] at hs
  have h := exp_sub_one_sub_self_bound (Real.log (normingRatio a ha k))
  rw [Real.exp_log (normingRatio_properties ha k).2] at h
  exact h.trans ((mul_le_mul hs (Real.exp_le_exp.mpr habs) (Real.exp_pos _).le (by positivity)).trans_eq (by field_simp [hkpos.ne']))

/-- The auxiliary harmonic logarithm is bounded by a fixed positive multiple of log(k+2), uniformly over the original indices.
Use: normingRatio_asymptotic gives the literal O(k^-3 log k) scale and regularized-kernel bounds can use the same summable logarithmic majorant.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: log(2*(k+1))=log(2)+log(k+1), both terms are at most log(k+2), and log(k+2)>=log(2)>0 absorbs the constant one. -/
theorem harmonic_log_comparison (k : ℕ) :
    1+Real.log (2*(k+1:ℝ))≤(2+1/Real.log 2)*Real.log (k+2:ℝ) := by
  -- The shifted positive logarithm avoids a spurious zero at the first original index.
  have hk : 0<(k+1:ℝ) := by positivity
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h₁ : Real.log 2≤Real.log (k+2:ℝ) := Real.log_le_log (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  have h₂ : Real.log (k+1:ℝ)≤Real.log (k+2:ℝ) := Real.log_le_log hk (by linarith)
  have hone : 1≤Real.log (k+2:ℝ)/Real.log 2 := (le_div_iff₀ h2).mpr (by simpa using h₁)
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hk.ne']
  exact (add_le_add hone (add_le_add h₁ h₂)).trans_eq (by ring)

/-- The original norming ratios have the full article asymptotic with the genuine complete spectral displacement mass and the printed logarithmic inverse-cubic remainder.
Use: regularized-kernel derivative summability in Structure of F (c), differentiability of the actual GL kernel K, and the differential/operator construction in Proposition C.2.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: add the proved quadratic exponential error to the refined true logarithm estimate. Absorb the inverse-fourth term and convert the harmonic logarithm to log(k+2); every coefficient and threshold is proved for the original actual infinite product. -/
theorem normingRatio_asymptotic {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∃ M : ℕ,∀ k : ℕ,M≤k →
      |normingRatio a ha k-1-displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2|≤
        C*Real.log (k+2:ℝ)/(k+1:ℝ)^3 := by
  -- No norming asymptotic or regularized-kernel hypothesis is assumed: the original product has been controlled directly.
  obtain ⟨B,hB,herror⟩ := normingRatio_exponential_error ha
  obtain ⟨L,hL,M,hlog⟩ := normingRatio_log_refined ha
  have hconst : 0<(2:ℝ)+1/Real.log 2 := by positivity [Real.log_pos (by norm_num : (1:ℝ)<2)]
  refine ⟨(B+L)*(2+1/Real.log 2),mul_pos (by positivity) hconst,M,fun k hk => ?_⟩
  have he : normingRatio a ha k-1-displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2=
      (normingRatio a ha k-1-Real.log (normingRatio a ha k))+
        (Real.log (normingRatio a ha k)-displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2) := by ring
  rw [he]
  calc
    _ ≤ |normingRatio a ha k-1-Real.log (normingRatio a ha k)|+
        |Real.log (normingRatio a ha k)-displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2| := abs_add_le _ _
    _ ≤ B/(k+1:ℝ)^4+L*(1+Real.log (2*(k+1:ℝ)))/(k+1:ℝ)^3 := add_le_add (herror k) (hlog k hk)
    _ ≤ (B+L)*(1+Real.log (2*(k+1:ℝ)))/(k+1:ℝ)^3 := (add_le_add (inverse_fourth_log_bound hB.le k) le_rfl).trans_eq (by ring)
    _ ≤ _ := (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (harmonic_log_comparison k) (by positivity)) (by positivity)).trans_eq (by ring)

end
end jacobi.Reference
