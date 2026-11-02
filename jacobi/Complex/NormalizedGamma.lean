import jacobi.Complex.GammaModulus
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: Euler's beta integral and the Gamma recurrence.
Use: the half-plane maximum argument bounds this function and its reciprocal to obtain matching Gamma power bounds on the parity contours.
-/
namespace jacobi.Complex
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The actual Gamma quotient normalized by its expected power, with the base shifted away from zero.
Use: the half-plane maximum argument bounds this function and its reciprocal to obtain matching Gamma power bounds on the parity contours.
Article: jacobi, Appendix C.2 (exact parity splitting).
-/
def normalizedGammaRatio (a b : ℝ) (z : ℂ) : ℂ :=
  Gamma (z+(a:ℂ))/Gamma (z+(b:ℂ))*(1+z)^((b-a:ℝ):ℂ)

/-- A positive shift of any point in the closed right half-plane avoids all Gamma poles.
Use: normalizedGammaRatio_differentiable applies the community Gamma derivative and justifies all quotient cancellations in the contour estimate.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: each prohibited nonpositive integer has nonpositive real part, whereas the shifted point has strictly positive real part. -/
theorem gamma_shift_avoids_poles {a : ℝ} (ha : 0<a) {z : ℂ} (hz : 0≤z.re) (n : ℕ) :
    z+(a:ℂ)≠-(n:ℂ) := by
  intro h
  have hr := congrArg Complex.re h
  simp only [add_re,ofReal_re,neg_re,natCast_re] at hr
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- The actual power-normalized Gamma quotient is complex differentiable at every point of the closed right half-plane.
Use: supplies the holomorphicity and boundary continuity premises of halfPlane_bound for the original contour Gamma estimate.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: positive shifts avoid Gamma poles, the denominator Gamma is nonzero, and 1+z lies in the slit plane of the principal complex power. -/
theorem normalizedGammaRatio_differentiable {a b : ℝ} (ha : 0<a) (hb : 0<b)
    {z : ℂ} (hz : 0≤z.re) : DifferentiableAt ℂ (normalizedGammaRatio a b) z := by
  -- Every boundary point also has a genuine open holomorphic neighborhood.
  have hGa := (Complex.differentiableAt_Gamma _ (gamma_shift_avoids_poles ha hz)).comp z
    (differentiableAt_id.add_const (a:ℂ))
  have hGb := (Complex.differentiableAt_Gamma _ (gamma_shift_avoids_poles hb hz)).comp z
    (differentiableAt_id.add_const (b:ℂ))
  have hden : Gamma (z+(b:ℂ))≠0 := Gamma_ne_zero_of_re_pos (by simp only [add_re,ofReal_re]; linarith)
  have hbase : (1+z)∈Complex.slitPlane := Or.inl (by simp only [add_re,one_re]; linarith)
  exact (hGa.div hGb hden).mul ((differentiableAt_id.const_add (1:ℂ)).cpow_const hbase)

/-- The actual normalized Gamma quotient still has only polynomial growth on the closed right half-plane.
Use: halfPlane_bound combines this crude growth with the proved vertical boundary bound to recover the sharp Gamma power law in the contour estimate.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the beta-integral bound controls the unnormalized quotient. Since norm(1+z)>=1, its fixed real power is bounded by an integer power of 1+norm(z). -/
theorem normalizedGammaRatio_polynomial_bound {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    ∃ C : ℝ,0<C ∧ ∃ n : ℕ,∀ z : ℂ,0≤z.re →
      ‖normalizedGammaRatio a b z‖≤C*(1+‖z‖)^n := by
  -- The integer power majorizes either sign of the genuine normalization exponent.
  obtain ⟨C,hC,n,hbound⟩ := gammaRatio_polynomial_bound ha hb
  obtain ⟨m,hm⟩ := exists_nat_gt (b-a)
  refine ⟨C,hC,n+m,fun z hz => ?_⟩
  have hbase : 1≤‖(1:ℂ)+z‖ := by
    have h := Complex.re_le_norm ((1:ℂ)+z)
    simp only [add_re,one_re] at h
    linarith
  have hpow : ‖(1:ℂ)+z‖^(b-a)≤(1+‖z‖)^m := by
    calc
      _ ≤ ‖(1:ℂ)+z‖^(m:ℝ) := Real.rpow_le_rpow_of_exponent_le hbase hm.le
      _ = ‖(1:ℂ)+z‖^m := Real.rpow_natCast _ _
      _ ≤ (1+‖z‖)^m := pow_le_pow_left₀ (norm_nonneg _) (by simpa using norm_add_le (1:ℂ) z) _
  rw [normalizedGammaRatio,norm_mul,Complex.norm_cpow_real]
  exact (mul_le_mul (hbound z hz) hpow (by positivity) (by positivity)).trans_eq (by rw [pow_add]; ring)

end
end jacobi.Complex
