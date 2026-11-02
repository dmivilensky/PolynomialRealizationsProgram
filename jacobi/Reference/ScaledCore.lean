import jacobi.Reference.FrequencyScaling

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
The true hypergeometric reference core and its genuine spatial-argument
derivative have uniform bounds at |x|=O(|omega|^-2). A fixed convergent
community 2F1 majorant controls the actual series, and a scaled Cauchy
circle controls its actual derivative. No high-frequency solution bound
is assumed in either proof.
Use: controls the original reference wave at t of order |omega|^-1 before its true ODE energy is propagated.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual original reference hypergeometric core is uniformly bounded throughout its genuine inverse-square frequency scale.
Use: controls the original reference wave at t of order |omega|^-1 before its true ODE energy is propagated.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the genuine scaled coefficients are bounded by one fixed
positive-parameter 2F1 series at argument one quarter. Every true term
is dominated by its norm series. That series genuinely converges, so
its full sum bounds the original hypergeometric function. -/
theorem waveCore_scaled_bound (a : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ omega:ℂ,1≤‖omega‖ → ∀ x:ℂ,‖omega‖^2*‖x‖≤1/4 →
      ‖waveCore a omega x‖≤C := by
  -- A single actual summable series is used for all arbitrarily large complex frequencies.
  let M := fun n => ‖ordinaryHypergeometricCoefficient (frequencyMajorant a:ℂ)
    (frequencyMajorant a:ℂ) ((gamma a:ℂ)+1/2) n‖*(1/4:ℝ)^n
  have hM : Summable M := by
    have hh := Hypergeometric.summable_norm (u := (frequencyMajorant a:ℂ))
      (v := (frequencyMajorant a:ℂ)) (c := ((gamma a:ℂ)+1/2)) (x := (1/4:ℂ)) (by norm_num)
    convert hh using 1
    funext n
    dsimp only [M]
    rw [norm_mul (ordinaryHypergeometricCoefficient (frequencyMajorant a:ℂ)
      (frequencyMajorant a:ℂ) ((gamma a:ℂ)+1/2) n),norm_pow]
    norm_num
  refine ⟨(∑' n,M n)+1,by
    have hh : 0≤∑' n,M n := tsum_nonneg (fun n => by dsimp [M]; positivity)
    linarith,fun omega homega x hx => ?_⟩
  have ht (n : ℕ) : ‖frequencyCoefficient a n omega*x^n‖≤M n := by
    rw [norm_mul,norm_pow]
    calc
      _ ≤ (‖omega‖^(2*n)*‖ordinaryHypergeometricCoefficient (frequencyMajorant a:ℂ)
          (frequencyMajorant a:ℂ) ((gamma a:ℂ)+1/2) n‖)*‖x‖^n :=
        mul_le_mul_of_nonneg_right (frequencyCoefficient_scaled a homega n) (by positivity)
      _ = ‖ordinaryHypergeometricCoefficient (frequencyMajorant a:ℂ)
          (frequencyMajorant a:ℂ) ((gamma a:ℂ)+1/2) n‖*(‖omega‖^2*‖x‖)^n := by
        rw [mul_pow,pow_mul]
        ring
      _ ≤ M n := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hx n) (norm_nonneg _)
  have hs : Summable (fun n => ‖frequencyCoefficient a n omega*x^n‖) :=
    hM.of_nonneg_of_le (fun _ => norm_nonneg _) ht
  have he : waveCore a omega x=∑' n,frequencyCoefficient a n omega*x^n := by
    rw [waveCore,ordinaryHypergeometric_eq_tsum]
    rfl
  rw [he]
  exact (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum ht hM).trans (by linarith))

/-- The actual original core derivative is bounded by a constant times the squared frequency on the genuine initial spatial scale.
Use: controls the true initial reference slope divided by |omega| in the high-frequency ODE energy.
Article: jacobi, Lemma C.1.
Proof: a Cauchy circle of radius 1/(8*|omega|^2) remains in the proved
quarter-scale core region. The actual analytic derivative equals that
community Cauchy derivative. Its true norm is bounded by the uniform
core bound divided by the scaled radius. -/
theorem waveCore_scaled_deriv_bound (a : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ omega:ℂ,1≤‖omega‖ → ∀ x:ℂ,‖omega‖^2*‖x‖≤1/8 →
      ‖deriv (waveCore a omega) x‖≤C*‖omega‖^2 := by
  -- The shrinking Cauchy circle is explicit and every original disk-containment premise is proved.
  obtain ⟨B,hB,hbound⟩ := waveCore_scaled_bound a
  refine ⟨8*B,by positivity,fun omega homega x hx => ?_⟩
  have hRp : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one homega
  have hR2 : 1≤‖omega‖^2 := by nlinarith
  let r : ℝ := 1/(8*‖omega‖^2)
  have hr : 0<r := by dsimp [r]; positivity
  have hrad : ‖omega‖^2*r=1/8 := by dsimp [r]; field_simp
  have hclosed (w : ℂ) (hw : w∈Metric.closedBall x r) : ‖omega‖^2*‖w‖≤1/4 := by
    have hh : ‖w-x‖≤r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
    have htriangle := norm_add_le (w-x) x
    rw [sub_add_cancel] at htriangle
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖omega‖)
    have hm' := mul_le_mul_of_nonneg_left htriangle (sq_nonneg ‖omega‖)
    nlinarith
  have hd : DifferentiableOn ℂ (waveCore a omega) (Metric.ball 0 1) := by
    intro w hw
    exact (Hypergeometric.analytic (by simpa only [Metric.mem_ball,dist_zero_right] using hw)).differentiableAt.differentiableWithinAt
  rw [← Complex.cderiv_eq_deriv Metric.isOpen_ball hd hr (fun w hw => by
    have hh := hclosed w hw
    have hm := mul_le_mul_of_nonneg_right hR2 (norm_nonneg w)
    simp only [Metric.mem_ball,dist_zero_right]
    nlinarith)]
  have hh := Complex.norm_cderiv_le hr (fun w hw => hbound omega homega w
    (hclosed w (Metric.sphere_subset_closedBall hw)))
  apply hh.trans_eq
  dsimp [r]
  field_simp

end
end jacobi.Reference
