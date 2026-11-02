import Mathlib.Analysis.InnerProductSpace.Positive

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Real-part coercivity on a complex Hilbert space gives an actual bounded
inverse with the reciprocal coercivity bound. A perturbation by at most
half the original coercivity constant preserves the required estimate.
Source: the standard Hilbert-space coercive operator argument.
Use: proves the physical GL inverse estimate from the actual original complex quadratic form.
-/
namespace jacobi.Analytic
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Real-part coercivity gives genuine complex Hilbert operator invertibility and the sharp reciprocal inverse norm bound.
Use: proves the physical GL inverse estimate from the actual original complex quadratic form.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Source: mathlib, ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map.
Proof: real part is bounded by the modulus of the same inner product, so the community Hilbert inverse theorem gives an actual unit. Cauchy--Schwarz and coercivity bound each input norm by the image norm divided by c; apply this to the genuine inverse image. -/
theorem complex_coercive_inverse (A : E →L[ℂ] E) {c : ℝ} (hc : 0<c)
    (h : ∀ v:E,c*‖v‖^2≤(inner ℂ v (A v)).re) :
    IsUnit A ∧ ‖Ring.inverse A‖≤1/c := by
  -- Existence is obtained on the full Hilbert space, not just on a dense class of continuous inputs.
  have hu : IsUnit A := by
    apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map A
      (c := ⟨c,hc.le⟩) (by exact_mod_cast hc)
    intro v
    have hr := (h v).trans (_root_.Complex.re_le_norm (inner ℂ v (A v)))
    rw [norm_inner_symm] at hr
    change ‖v‖^2*c≤_
    nlinarith
  have hlower (v:E) : c*‖v‖≤‖A v‖ := by
    by_cases hv : v=0
    · simp only [hv,norm_zero,mul_zero,map_zero,le_refl]
    · have hn := norm_pos_iff.mpr hv
      have hh := (h v).trans ((_root_.Complex.re_le_norm _).trans
        (norm_inner_le_norm (𝕜 := ℂ) v (A v)))
      apply (mul_le_mul_iff_right₀ hn).mp
      nlinarith
  refine ⟨hu,(Ring.inverse A).opNorm_le_bound (by positivity) (fun v => ?_)⟩
  have he := congrArg (fun T:E →L[ℂ] E => T v) (Ring.mul_inverse_cancel A hu)
  change A (Ring.inverse A v)=v at he
  have hh := hlower (Ring.inverse A v)
  rw [he] at hh
  exact (show ‖Ring.inverse A v‖≤‖v‖/c from (le_div_iff₀ hc).mpr (by nlinarith)).trans_eq (by ring)

/-- A complex Hilbert operator within half the genuine coercivity gap has inverse norm at most twice the original reciprocal gap.
Use: applies one uniform kernel perturbation neighborhood to every actual GL interval operator.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the real part of the perturbation pairing is bounded in absolute value by its modulus, Cauchy--Schwarz and the actual operator norm difference. Subtract this error from the original coercivity form and invoke the proved genuine inverse theorem. -/
theorem complex_coercive_perturbation (A B : E →L[ℂ] E) {κ : ℝ} (hκ : 0<κ)
    (hA : ∀ v:E,κ*‖v‖^2≤(inner ℂ v (A v)).re) (hBA : ‖B-A‖≤κ/2) :
    IsUnit B ∧ ‖Ring.inverse B‖≤2/κ := by
  -- The same actual input is used in both forms, so the error estimate is uniform on the full unit sphere.
  have hb (v:E) : (κ/2)*‖v‖^2≤(inner ℂ v (B v)).re := by
    have hn := (B-A).le_of_opNorm_le hBA v
    have hi := (norm_inner_le_norm (𝕜 := ℂ) v ((B-A) v)).trans
      (mul_le_mul_of_nonneg_left hn (norm_nonneg v))
    have hr : -‖inner ℂ v ((B-A) v)‖≤(inner ℂ v ((B-A) v)).re := by
      have hh := _root_.Complex.re_le_norm (-inner ℂ v ((B-A) v))
      simpa only [_root_.Complex.neg_re,norm_neg,neg_neg] using neg_le_neg hh
    have he : (inner ℂ v ((B-A) v)).re=(inner ℂ v (B v)).re-(inner ℂ v (A v)).re := by
      change (inner ℂ v (B v-A v)).re=_
      rw [inner_sub_right,_root_.Complex.sub_re]
    rw [he] at hr
    nlinarith [hA v]
  obtain ⟨hu,hn⟩ := complex_coercive_inverse B (half_pos hκ) hb
  exact ⟨hu,hn.trans_eq (by ring)⟩

end
end jacobi.Analytic
