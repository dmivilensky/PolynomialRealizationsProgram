import jacobi.GelfandLevitan.MidpointProductQuotient
import jacobi.GelfandLevitan.MidpointGrowth
import jacobi.Reference.ContourLower
import jacobi.Reference.ContourProduct

/-!
Article: jacobi, Proposition C.2.
The actual separated characteristic product has the original full
exponential type. On the proved pole-free expanding energy circles,
the genuine Delta_sigma lower bound cancels that exponential. The
actual entire quotient therefore has a polynomial circle bound.
Use: separatedProduct_growth transfers the already proved true midpoint exponential type to the actual separated product.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Each original separated characteristic is bounded by its actual fixed first boundary state times the original midpoint value and slope norms.
Use: separatedProduct_growth transfers the already proved true midpoint exponential type to the actual separated product.
Article: jacobi, Proposition C.2.
Proof: expand the original two-term determinant, use the triangle and product norm bounds, and enlarge its fixed genuine coefficient norm by one. -/
theorem separatedCharacteristic_norm_le (a : ℝ) (ha : -1<a) (p : Fin 2) (z : ℂ) :
    ‖separatedCharacteristic a ha p z‖≤
      (1+‖midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex p 0):ℂ)‖+
        ‖midpointSlope a ha (jacobi.Bessel.sigma a ha (parityIndex p 0):ℂ)‖)*
      (‖midpointValue a ha z‖+‖midpointSlope a ha z‖) := by
  unfold separatedCharacteristic
  apply (norm_sub_le _ _).trans
  rw [norm_mul,norm_mul]
  nlinarith [norm_nonneg (midpointValue a ha z),norm_nonneg (midpointSlope a ha z),
    norm_nonneg (midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex p 0):ℂ)),
    norm_nonneg (midpointSlope a ha (jacobi.Bessel.sigma a ha (parityIndex p 0):ℂ))]

/-- The actual product of the two separated original midpoint characteristics has full reference exponential type with a quadratic frequency prefactor.
Use: midpointProductQuotient_circle_bound cancels this genuine exponential against the already proved original Delta_sigma contour lower bound.
Article: jacobi, Proposition C.2.
Proof: both fixed boundary determinants inherit the proved original a,b growth bound. Multiply their genuine bounds and combine the two half-interval exponentials into the full interval exponential. -/
theorem separatedProduct_growth (a : ℝ) (ha : -1<a) :
    ∃ D:ℝ,0<D ∧ ∀ w:ℂ,
      ‖separatedProduct a ha ((jacobi.Jacobi.endpointCorrection a:ℂ)+w^2)‖≤
        D*(1+‖w‖)^2*Real.exp |w.im| := by
  -- All fixed constants are norms of the original constructed midpoint states and the proved original growth constant.
  obtain ⟨C,hC,hbound⟩ := midpoint_growth ha
  let B := fun p:Fin 2 => 1+‖midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex p 0):ℂ)‖+
    ‖midpointSlope a ha (jacobi.Bessel.sigma a ha (parityIndex p 0):ℂ)‖
  have hB (p : Fin 2) : 0<B p := by dsimp [B]; positivity
  refine ⟨B 0*B 1*C^2,by positivity,fun w => ?_⟩
  have hp (p : Fin 2) : ‖separatedCharacteristic a ha p ((jacobi.Jacobi.endpointCorrection a:ℂ)+w^2)‖≤
      B p*(C*(1+‖w‖)*Real.exp (|w.im|/2)) :=
    (separatedCharacteristic_norm_le a ha p _).trans (mul_le_mul_of_nonneg_left (hbound w) (hB p).le)
  rw [separatedProduct,norm_mul]
  apply (mul_le_mul (hp 0) (hp 1) (norm_nonneg _) (by positivity)).trans_eq
  have he : Real.exp (|w.im|/2)*Real.exp (|w.im|/2)=Real.exp |w.im| := by
    rw [← Real.exp_add,add_halves]
  calc
    _ = (B 0*B 1*C^2)*(1+‖w‖)^2*(Real.exp (|w.im|/2)*Real.exp (|w.im|/2)) := by ring
    _ = _ := by rw [he]

/-- The actual entire separated-product quotient has one genuine polynomial bound on all sufficiently large original expanding energy circles.
Use: midpointProductQuotient_constant applies Cauchy estimates and the fundamental theorem of algebra to the original quotient, discharging the growth step in the characteristic factorization.
Article: jacobi, Proposition C.2.
Proof: the actual quotient numerator has the proved full exponential type. The original Delta_sigma contour lower bound cancels this exponential and leaves at most R^(2*gamma+1). A larger natural power bounds it on R>=1, hence also in the original energy radius R^2. -/
theorem midpointProductQuotient_circle_bound (a : ℝ) (ha : -1<a) :
    ∃ C:ℝ,0<C ∧ ∃ N:ℕ,∀ᶠ m:ℕ in atTop,
      ∀ z∈Metric.sphere (jacobi.Jacobi.endpointCorrection a:ℂ) ((contourRadius a m)^2),
        ‖midpointProductQuotient a ha z‖≤C*((contourRadius a m)^2)^N := by
  -- The pole exclusion and denominator lower bound are both established for these original contours before any quotient cancellation.
  obtain ⟨D,hD,hnum⟩ := separatedProduct_growth a ha
  obtain ⟨c,hc,M₁,hlower⟩ := contour_characteristicTau_lower ha
  obtain ⟨_,_,M₂,hrelative⟩ := contour_characteristic_bound ha
  obtain ⟨N,hN⟩ := exists_nat_ge (2*gamma a+1)
  refine ⟨8*D/c,by positivity,N,?_⟩
  filter_upwards [eventually_ge_atTop (max M₁ M₂)] with m hm z hz
  let R := contourRadius a m
  let w := Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))
  have hw : w^2=z-(jacobi.Jacobi.endpointCorrection a:ℂ) := frequency_square _
  have hR : 0<R := contourRadius_pos ha m
  have hR1 : 1≤R := (contourRadius_one_lt ha m).le
  have hz' : ‖z-(jacobi.Jacobi.endpointCorrection a:ℂ)‖=R^2 := by
    simpa only [Metric.mem_sphere,dist_eq_norm] using hz
  have hn : ‖w‖=R := by
    have h := congrArg norm hw
    rw [norm_pow,hz'] at h
    nlinarith [norm_nonneg w]
  have he : (jacobi.Jacobi.endpointCorrection a:ℂ)+w^2=z := by rw [hw]; ring
  obtain ⟨hσ,_,hcompare⟩ := hrelative m ((le_max_right _ _).trans hm) z hz'
  have hl := hlower m ((le_max_left _ _).trans hm) w hn
  rw [he] at hl
  have hden : (c/2)*R^(1-2*gamma a)*Real.exp |w.im|≤‖characteristicSigma a z‖ := by linarith
  have hpositive : 0<(c/2)*R^(1-2*gamma a)*Real.exp |w.im| := by positivity
  have hupper := hnum w
  rw [he,hn] at hupper
  rw [midpointProductQuotient,jacobi.Complex.simpleZeroQuotient,ite_eq_right hσ,norm_div]
  have hb := div_le_div₀ (by positivity : 0≤D*(1+R)^2*Real.exp |w.im|) hupper hpositive hden
  have hpower : R^2/R^(1-2*gamma a)=R^(2*gamma a+1) := by
    rw [← Real.rpow_natCast R 2,← Real.rpow_sub hR]
    congr 1
    norm_num
    ring
  have hnat : R^(2*gamma a+1)≤(R^2)^N := by
    calc
      _ ≤ R^(N:ℝ) := Real.rpow_le_rpow_of_exponent_le hR1 hN
      _ = R^N := Real.rpow_natCast _ _
      _ ≤ (R^2)^N := pow_le_pow_left₀ hR.le (by nlinarith) N
  apply hb.trans
  have he' : (D*(1+R)^2*Real.exp |w.im|)/((c/2)*R^(1-2*gamma a)*Real.exp |w.im|)=
      (2*D/c)*((1+R)^2/R^(1-2*gamma a)) := by
    field_simp [(Real.exp_pos |w.im|).ne',hc.ne',(Real.rpow_pos_of_pos hR (1-2*gamma a)).ne']
  rw [he']
  calc
    _ ≤ (2*D/c)*((4*R^2)/R^(1-2*gamma a)) := by
      gcongr
      nlinarith
    _ = (8*D/c)*R^(2*gamma a+1) := by
      rw [show 4*R^2/R^(1-2*gamma a)=4*(R^2/R^(1-2*gamma a)) by ring,hpower]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnat (by positivity)

end
end jacobi.GelfandLevitan
