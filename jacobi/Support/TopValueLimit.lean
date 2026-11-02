import jacobi.Support.TopScaleLimit
import jacobi.Support.TopNormalization

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The actual original finite top-node polynomial has the precise printed
normalized continuum limit along every moving positive mesh ratio.
Its three original sine products and linear factor converge with their
exact Gamma constants, fixing the genuine positive source profile U.
Use: topValue_limit takes the actual positive square root; TopUniformLimit extends this genuine limit uniformly down to the original zero endpoint.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The squared genuine normalized support top-node wave has exactly the printed continuum profile limit along every moving positive interior mesh index.
Use: topValue_limit takes the actual positive square root; TopUniformLimit extends this genuine limit uniformly down to the original zero endpoint.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: multiply the genuine first sine-factor limit and all three original sine-product limits. Their exact real-power identity gives the true finite degree normalization, and their exact Gamma constants give the square of the original U profile. -/
theorem topValue_square_limit {a b : ℝ} (ha:-1<a) (hb:-1<b)
    {ι : Type*} {l : Filter ι} {n m : ι→ℕ} {t : ℝ} (ht:t∈Ioo (0:ℝ) 1)
    (hn:Tendsto n l atTop) (hm:Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) l (𝓝 t)) :
    Tendsto (fun i => ((n i:ℝ)^(-gamma a)*topValue a b ha hb (n i) (m i))^2) l
      (𝓝 ((topProfile a b t)^2)) := by
  -- The actual n+1 polynomial dimension is converted only through the exact original unchanged-step identity.
  have hg := parameter_pos ha hb
  have hS := topScale_limit ha hb hn hm
  have hA := support_sineProduct_limit (a+2) b (show 0<gamma a+1/2 by linarith [hg.1]) ht hn hm
  have hB := support_sineProduct_limit (a+2) b (show 0<gamma b+1/2 by linarith [hg.2.1]) ht hn hm
  have hD := support_sineProduct_limit (a+2) b (show 0<2*averageGamma a b by linarith [hg.2.2]) ht hn hm
  simp only [step_darboux] at hA hB hD
  have hsin : 0<sin (π*t) := sin_pos_of_pos_of_lt_pi (mul_pos pi_pos ht.1) (by nlinarith [pi_pos,ht.2])
  let x : ℝ := sin (π*t)/π
  have hx : 0<x := div_pos hsin pi_pos
  have hB0 : (Gamma (gamma b+1/2))⁻¹*x^(gamma b+1/2-1)≠0 :=
    (mul_pos (inv_pos.mpr (Gamma_pos_of_pos (by linarith [hg.2.1]))) (rpow_pos_of_pos hx _)).ne'
  rw [show sin (π*t)/(π*averageGamma a b)=x/averageGamma a b by dsimp [x]; ring] at hS
  have hlim := (hS.mul (hA.div hB hB0)).mul hD
  rw [top_limit_constant a b hx,← topProfile_sq ha hb hsin.le] at hlim
  apply (tendsto_congr' ?_).mpr hlim
  filter_upwards [hn.eventually (eventually_gt_atTop (0:ℕ)),hm.eventually (Iio_mem_nhds ht.2)] with i hni hmi
  have hniR : (0:ℝ)<n i := by exact_mod_cast hni
  have hmn : m i≤n i := by
    have hh : (m i:ℝ)<n i := (div_lt_one hniR).mp hmi
    exact_mod_cast hh.le
  have hpow : ((n i:ℝ)^(-gamma a))^2=(n i:ℝ)^(-2*gamma a) := by
    rw [pow_two,← rpow_add hniR]
    congr 1
    ring
  rw [mul_pow,hpow]
  change (n i:ℝ)^(-2*gamma a)*
    ((naturalPolynomial a b ha hb (n i) (m i)).eval (cos (gamma a*step a b (n i+1))))^2= _
  rw [naturalPolynomial_top_sineProducts ha hb hmn]
  exact (top_finite_normalization a b hniR _ _ _ _).symm

/-- The actual normalized positive support top-node polynomial converges to precisely the original printed U profile along every moving positive interior mesh sequence.
Use: TopUniformLimit combines this genuine positive-mesh limit with the proved original small-index bounds to obtain the full-half-chain uniform limit.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: the actual normalized squares have the proved exact U-square limit. Genuine top-node positivity fixes the finite square-root branch, and the original positive Gamma and sine factors fix the same branch of U. -/
theorem topValue_limit {a b : ℝ} (ha:-1<a) (hb:-1<b)
    {ι : Type*} {l : Filter ι} {n m : ι→ℕ} {t : ℝ} (ht:t∈Ioo (0:ℝ) 1)
    (hn:Tendsto n l atTop) (hm:Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) l (𝓝 t)) :
    Tendsto (fun i => (n i:ℝ)^(-gamma a)*topValue a b ha hb (n i) (m i)) l
      (𝓝 (topProfile a b t)) := by
  -- The source's genuine positive normalization excludes an arbitrary sign in the continuum profile.
  have hsin : 0<sin (π*t) := sin_pos_of_pos_of_lt_pi (mul_pos pi_pos ht.1) (by nlinarith [pi_pos,ht.2])
  have hU : 0<topProfile a b t := mul_pos (topConstant_pos ha hb) (rpow_pos_of_pos hsin _)
  have h := continuous_sqrt.continuousAt.tendsto.comp (topValue_square_limit ha hb ht hn hm)
  simp only [Real.sqrt_sq_eq_abs,abs_of_pos hU] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [hn.eventually (eventually_gt_atTop (0:ℕ)),hm.eventually (Iio_mem_nhds ht.2)] with i hni hmi
  have hniR : (0:ℝ)<n i := by exact_mod_cast hni
  have hmn : m i≤n i := by
    have hh : (m i:ℝ)<n i := (div_lt_one hniR).mp hmi
    exact_mod_cast hh.le
  symm
  change Real.sqrt (((n i:ℝ)^(-gamma a)*topValue a b ha hb (n i) (m i))^2)=_
  apply Real.sqrt_sq
  exact mul_nonneg (rpow_pos_of_pos hniR _).le (naturalPolynomial_top_pos ha hb hmn).le

end
end jacobi.Support
