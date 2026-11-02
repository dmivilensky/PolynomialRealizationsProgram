import jacobi.Reference.GammaVertical
import jacobi.Complex.NormalizedGamma

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
Use: gamma_vertical_normalized_limit replaces the pure frequency power in the actual Gamma asymptotic by the nonsingular normalization base 1+z.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology ComplexConjugate
set_option backward.isDefEq.respectTransparency false

/-- The modulus of 1+i*y divided by y tends to one on the positive imaginary ray.
Use: gamma_vertical_normalized_limit replaces the pure frequency power in the actual Gamma asymptotic by the nonsingular normalization base 1+z.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: after division by positive y, the complex number is 1/y+i, which tends to i and has limiting norm one. -/
theorem vertical_base_norm_limit :
    Tendsto (fun y : ℝ => ‖(1:ℂ)+Complex.I*(y:ℂ)‖/y) atTop (𝓝 1) := by
  -- This elementary normalization keeps the half-plane analytic function regular at zero.
  have hi : Tendsto (fun y : ℝ => (1:ℝ)/y) atTop (𝓝 0) := tendsto_id.const_div_atTop 1
  have hc := ((Complex.continuous_ofReal.continuousAt.tendsto.comp hi).add_const Complex.I).norm
  simp only [Complex.ofReal_zero,zero_add,Complex.norm_I] at hc
  apply hc.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  have he : (((1/y:ℝ):ℂ)+Complex.I)*(y:ℂ)=(1:ℂ)+Complex.I*(y:ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hy.ne']
  rw [← he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy]
  exact (mul_div_cancel_right₀ _ hy.ne').symm

/-- The squared modulus of the actual normalized Gamma quotient has a finite positive vertical limit.
Use: gamma_vertical_normalized_bound adds the compact middle part of the imaginary axis, giving the boundary input for the half-plane maximum principle.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: divide the two proved reciprocal-Gamma asymptotics, cancel the common exponential, and multiply by the harmless base-modulus correction tending to one. -/
theorem gamma_vertical_normalized_limit {a b : ℝ} (ha : 1/4<a) (hb : 1/4<b) :
    ∃ L : ℝ,0<L ∧ Tendsto (fun y : ℝ =>
      ‖jacobi.Complex.normalizedGammaRatio a b (Complex.I*(y:ℂ))‖^2) atTop (𝓝 L) := by
  -- Both asymptotic weights are conclusions about the original characteristic, not independent Gamma assumptions.
  obtain ⟨A,hA,hlimA⟩ := gamma_vertical_weight_limit ha
  obtain ⟨B,hB,hlimB⟩ := gamma_vertical_weight_limit hb
  refine ⟨B/A,div_pos hB hA,?_⟩
  have hp := vertical_base_norm_limit.rpow_const (p := 2*(b-a)) (Or.inl one_ne_zero)
  simp only [Real.one_rpow] at hp
  have hh := (hlimB.div hlimA hA.ne').mul hp
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  have hGa : Complex.Gamma ((a:ℂ)+Complex.I*(y:ℂ))≠0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hGb : Complex.Gamma ((b:ℂ)+Complex.I*(y:ℂ))≠0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hna : ‖Complex.Gamma ((a:ℂ)+Complex.I*(y:ℂ))‖≠0 := norm_ne_zero_iff.mpr hGa
  have hnb : ‖Complex.Gamma ((b:ℂ)+Complex.I*(y:ℂ))‖≠0 := norm_ne_zero_iff.mpr hGb
  have hpower : y^(2*b-1)=y^(2*a-1)*y^(2*(b-a)) := by
    rw [← Real.rpow_add hy,show 2*a-1+2*(b-a)=2*b-1 by ring]
  have hbase : ‖(1:ℂ)+Complex.I*(y:ℂ)‖^(2*(b-a))=
      (‖(1:ℂ)+Complex.I*(y:ℂ)‖^(b-a))^2 := by
    rw [show 2*(b-a)=(b-a)*2 by ring,Real.rpow_mul (norm_nonneg _),Real.rpow_two]
  dsimp only [jacobi.Complex.normalizedGammaRatio,Pi.div_apply]
  rw [add_comm (Complex.I*(y:ℂ)) (a:ℂ),add_comm (Complex.I*(y:ℂ)) (b:ℂ)]
  rw [norm_mul,norm_div,Complex.norm_cpow_real,
    Real.div_rpow (norm_nonneg _) hy.le,hbase,hpower]
  field_simp [hy.ne',hna,hnb,Real.rpow_ne_zero hy.le hy.ne',Real.exp_ne_zero]

end
end jacobi.Reference
