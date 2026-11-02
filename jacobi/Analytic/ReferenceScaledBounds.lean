import jacobi.Analytic.ReferenceWave
import jacobi.Reference.InitialScale

/-!
Article: jacobi, Lemma C.1.
Uniform bounds for the original complex-order Gauss core and its actual
spatial derivative at the initial inverse-frequency scale. Both constants
are independent of the varying complex order and large frequency.
These provide initial data for the remaining high-frequency propagation.
Use: controls the reference initial state uniformly in order before high-frequency ODE propagation.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set Polynomial
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The original complex-order Gauss coefficients have a common scaled positive-parameter majorant.
Use: controls the reference initial state uniformly in order before high-frequency ODE propagation.
Article: jacobi, Lemma C.1.
Proof: the two numerator parameter norms are at most a fixed positive
constant times the frequency norm. Apply the earlier exact scaled
Pochhammer estimate, then the moving-denominator lower bound to replace
its actual denominator by the fixed positive real margin. -/
theorem coefficient_scaled_bound {G δ : ℝ} (hG : 0<G) (hδ : 0<δ)
    {a omega : ℂ} (ha : ‖gamma a‖≤G) (hc : δ≤(gamma a+1/2).re)
    (homega : 1≤‖omega‖) (n : ℕ) :
    ‖ordinaryHypergeometricCoefficient (gamma a-omega/(Real.pi:ℂ))
      (gamma a+omega/(Real.pi:ℂ)) (gamma a+1/2) n‖≤
    ‖omega‖^(2*n)*‖ordinaryHypergeometricCoefficient
      ((G+1/Real.pi+1:ℝ):ℂ) ((G+1/Real.pi+1:ℝ):ℂ) (δ:ℂ) n‖ := by
  -- The denominator margin and numerator norm bounds hold on the same genuine order set.
  let K : ℝ := G+1/Real.pi+1
  have hK : 0<K := by dsimp [K]; positivity
  have hdiv : ‖omega/(Real.pi:ℂ)‖=‖omega‖/Real.pi := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have hKR : G+‖omega‖/Real.pi≤K*‖omega‖ := by
    have hh := mul_le_mul_of_nonneg_left homega hG.le
    have hGR : G≤G*‖omega‖ := by simpa only [mul_one] using hh
    calc
      G+‖omega‖/Real.pi ≤ G*‖omega‖+‖omega‖/Real.pi := by linarith
      _ ≤ G*‖omega‖+‖omega‖/Real.pi+‖omega‖ := by linarith [norm_nonneg omega]
      _ = K*‖omega‖ := by dsimp [K]; ring
  have hm := (norm_sub_le (gamma a) (omega/(Real.pi:ℂ))).trans
    (by rw [hdiv]; linarith : ‖gamma a‖+‖omega/(Real.pi:ℂ)‖≤K*‖omega‖)
  have hp := (norm_add_le (gamma a) (omega/(Real.pi:ℂ))).trans
    (by rw [hdiv]; linarith : ‖gamma a‖+‖omega/(Real.pi:ℂ)‖≤K*‖omega‖)
  have hnorm : ‖(K:ℂ)‖≤K := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hK]
  exact (jacobi.Reference.hypergeometric_coefficient_scaled hK homega hm hp n).trans
    (mul_le_mul_of_nonneg_left
      (jacobi.Reference.Hypergeometric.coefficient_parameters_bound hK hδ hnorm hnorm hc n) (by positivity))

/-- The actual reference Gauss core is uniformly bounded on its quarter inverse-square frequency disk for a bounded set of complex orders with positive denominator margin.
Use: supplies actual uniformly bounded initial reference values, with no compact-parameter or oscillatory estimate assumed.
Article: jacobi, Lemma C.1.
Proof: the original scaled coefficients are dominated by one fixed
positive-parameter Gauss series at argument one quarter. That actual
series converges, so its norm sum bounds every original core uniformly. -/
theorem waveCore_scaled_bound {G δ : ℝ} (hG : 0<G) (hδ : 0<δ) :
    ∃ C : ℝ,0<C ∧ ∀ a omega : ℂ,‖gamma a‖≤G → δ≤(gamma a+1/2).re →
      1≤‖omega‖ → ∀ x : ℂ,‖omega‖^2*‖x‖≤1/4 → ‖waveCore a omega x‖≤C := by
  -- One genuinely convergent majorant covers both complex-order and frequency variation.
  let K : ℝ := G+1/Real.pi+1
  let M := fun n => ‖ordinaryHypergeometricCoefficient (K:ℂ) (K:ℂ) (δ:ℂ) n‖*(1/4:ℝ)^n
  have hM : Summable M := by
    have hh := jacobi.Reference.Hypergeometric.summable_norm
      (u := (K:ℂ)) (v := (K:ℂ)) (c := (δ:ℂ)) (x := (1/4:ℂ)) (by norm_num)
    convert! hh using 1
    ext n
    simp only [M,norm_mul,norm_pow]
    norm_num
  refine ⟨(∑' n,M n)+1,by
    have hh : 0≤∑' n,M n := tsum_nonneg (fun n => by dsimp [M]; positivity)
    linarith,fun a omega ha hc homega x hx => ?_⟩
  have hterms (n : ℕ) :
      ‖ordinaryHypergeometricCoefficient (gamma a-omega/(Real.pi:ℂ))
        (gamma a+omega/(Real.pi:ℂ)) (gamma a+1/2) n*x^n‖≤M n := by
    rw [norm_mul,norm_pow]
    calc
      _ ≤ (‖omega‖^(2*n)*‖ordinaryHypergeometricCoefficient (K:ℂ) (K:ℂ) (δ:ℂ) n‖)*‖x‖^n :=
        mul_le_mul_of_nonneg_right (coefficient_scaled_bound hG hδ ha hc homega n) (by positivity)
      _ = ‖ordinaryHypergeometricCoefficient (K:ℂ) (K:ℂ) (δ:ℂ) n‖*(‖omega‖^2*‖x‖)^n := by
        rw [mul_pow,pow_mul]
        ring
      _ ≤ M n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hx n) (norm_nonneg _)
  have hs := hM.of_nonneg_of_le (fun _ => norm_nonneg _) hterms
  rw [waveCore,ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  exact (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum hterms hM).trans (by linarith))

/-- The genuine spatial-argument derivative of the original complex-order Gauss core is uniformly bounded by the squared frequency at the initial scale.
Use: supplies the second initial state coordinate in the complex-order reference energy estimate.
Article: jacobi, Lemma C.1.
Proof: the Cauchy circle of radius 1/(8|omega|^2) remains in the proved
quarter-scale core disk. The actual analytic derivative equals the
community Cauchy derivative, whose norm is bounded by the proved core
bound divided by that explicit radius. -/
theorem waveCore_scaled_deriv_bound {G δ : ℝ} (hG : 0<G) (hδ : 0<δ) :
    ∃ C : ℝ,0<C ∧ ∀ a omega : ℂ,‖gamma a‖≤G → δ≤(gamma a+1/2).re →
      1≤‖omega‖ → ∀ x : ℂ,‖omega‖^2*‖x‖≤1/8 → ‖deriv (waveCore a omega) x‖≤C*‖omega‖^2 := by
  -- The Cauchy radius depends only on the genuine frequency, not on the varying complex order.
  obtain ⟨B,hB,hbound⟩ := waveCore_scaled_bound hG hδ
  refine ⟨8*B,by positivity,fun a omega ha hc homega x hx => ?_⟩
  have hRp : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one homega
  have hR2 : 1≤‖omega‖^2 := by nlinarith
  let r : ℝ := 1/(8*‖omega‖^2)
  have hr : 0<r := by dsimp [r]; positivity
  have hrad : ‖omega‖^2*r=1/8 := by dsimp [r]; field_simp
  have hclosed (w : ℂ) (hw : w∈Metric.closedBall x r) : ‖omega‖^2*‖w‖≤1/4 := by
    have hh : ‖w-x‖≤r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
    have ht := norm_add_le (w-x) x
    rw [sub_add_cancel] at ht
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖omega‖)
    have hm' := mul_le_mul_of_nonneg_left ht (sq_nonneg ‖omega‖)
    nlinarith
  have hd : DifferentiableOn ℂ (waveCore a omega) (Metric.ball 0 1) := by
    intro w hw
    exact (jacobi.Reference.Hypergeometric.analytic
      (by simpa only [Metric.mem_ball,dist_zero_right] using hw)).differentiableAt.differentiableWithinAt
  rw [← Complex.cderiv_eq_deriv Metric.isOpen_ball hd hr (fun w hw => by
    have hh := hclosed w hw
    have hm := mul_le_mul_of_nonneg_right hR2 (norm_nonneg w)
    simp only [Metric.mem_ball,dist_zero_right]
    nlinarith)]
  exact (Complex.norm_cderiv_le hr (fun w hw => hbound a omega ha hc homega w
    (hclosed w (Metric.sphere_subset_closedBall hw)))).trans_eq (by dsimp [r]; field_simp)

/-- The actual normalized complex-order reference wave has its uniform endpoint-power bound throughout the initial inverse-frequency scale.
Use: supplies the genuine first initial state component for proving the
uniform high-frequency bound in analytic GL; the propagation past this
initial region is a separate remaining estimate.
Article: jacobi, Lemma C.1.
Proof: the physical cosine coordinate lies in the proved shrinking core
disk. The actual sine prefactor has norm equal to its real-part power,
and sin(pi*t)/pi is at most t. Multiply these two genuine bounds. -/
theorem wave_initial_scale_bound {G δ : ℝ} (hG : 0<G) (hδ : 0<δ) :
    ∃ C : ℝ,0<C ∧ ∀ a omega : ℂ,0<(gamma a).re → ‖gamma a‖≤G →
      δ≤(gamma a+1/2).re → 1≤‖omega‖ → ∀ t∈Ioc (0:ℝ) (1/2),
        Real.pi*‖omega‖*t≤1/4 → ‖wave a omega t‖≤C*t^(gamma a).re := by
  -- These are the original reference values with their actual complex endpoint normalization.
  obtain ⟨C,hC,hcore⟩ := waveCore_scaled_bound hG hδ
  refine ⟨C,hC,fun a omega hag ha hc homega t ht hsmall => ?_⟩
  have htI : t∈Ico (0:ℝ) 1 := ⟨ht.1.le,by linarith [ht.2]⟩
  have hx := jacobi.Reference.small_scale_coordinate ht.1 hsmall
  have hH := hcore a omega ha hc homega (jacobi.Reference.coordinate t:ℂ) (by linarith)
  have hb : Real.sin (Real.pi*t)/Real.pi≤t :=
    (div_le_iff₀ Real.pi_pos).mpr (by simpa only [mul_comm] using Real.sin_le (mul_nonneg Real.pi_pos.le ht.1.le))
  have hw : ‖weight a t‖≤t^(gamma a).re := by
    rw [weight_norm hag htI]
    exact Real.rpow_le_rpow (sineBase_nonneg htI) hb hag.le
  rw [wave,norm_mul]
  exact (mul_le_mul hw hH (norm_nonneg _) (Real.rpow_pos_of_pos ht.1 _).le).trans_eq (by ring)

end
end jacobi.ComplexReference
