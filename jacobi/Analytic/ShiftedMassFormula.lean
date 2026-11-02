import jacobi.Analytic.ShiftedMoments
import jacobi.Bessel.OrderShift
import jacobi.Bessel.Determinant

/-!
Article: jacobi, Appendix E.1.
The actual convergent mass equals the logarithmic derivative of the
original normalized Bessel function throughout w>-sigma_1, and hence
its adjacent-order quotient. This is the printed modified-Bessel
quotient in the entire spectral normalization F_alpha(-w); unlike a
square-root expression this normalization also covers negative w and
w=0 directly. The proof differentiates the genuine positive canonical
product, with a proved local summable derivative bound.
Use: shiftedLogDet_value and shiftedLogDet_hasDerivAt identify the actual shifted spectral mass with the logarithmic derivative of the same original Bessel determinant.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter
open scoped Topology

/-- The actual logarithm series of the shifted Bessel canonical determinant.
Use: shiftedLogDet_value and shiftedLogDet_hasDerivAt identify the actual shifted spectral mass with the logarithmic derivative of the same original Bessel determinant.
Article: jacobi, Appendix E.1.
-/
def shiftedLogDet (a:ℝ) (ha:-1<a) (w:ℝ) : ℝ :=
  ∑'k,log (1+w/ jacobi.Bessel.sigma a ha k)

/-- The original shifted canonical factors are strictly positive above the true first negative pole.
Use: the genuine logarithm series, its derivative and exponentiation all use the actual positive branch, including for negative admissible shifts.
Article: jacobi, Appendix E.1.
Proof: the original numerator sigma_k+w is positive and sigma_k itself is positive; their quotient is the original factor. -/
theorem shiftedLogFactor_pos (a:ℝ) (ha:-1<a) {w:ℝ}
    (hw: - jacobi.Bessel.sigma a ha 0<w) (k:ℕ) : 0<1+w/ jacobi.Bessel.sigma a ha k := by
  have hs := jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k)
  rw [one_add_div hs.ne']
  exact div_pos (realShifted_denominator_pos a ha hw k) hs

/-- The original shifted determinant logarithm series is genuinely summable.
Use: shiftedLogDet_value exponentiates an actual convergent series and shiftedLogDet_hasDerivAt differentiates that same sum.
Article: jacobi, Appendix E.1.
Proof: the original first Rayleigh spectrum is summable. Multiply it by w/2 to obtain the exact perturbations w/sigma_k, and apply the community logarithmic summability theorem. -/
theorem shiftedLogFactor_summable (a:ℝ) (ha:-1<a) (w:ℝ) :
    Summable (fun k => log (1+w/ jacobi.Bessel.sigma a ha k)) := by
  have hs := (jacobi.Bessel.edgeValue_summable ha).mul_left (w/2)
  have he (k:ℕ) : (w/2)* jacobi.Bessel.edgeValue a ha k=w/ jacobi.Bessel.sigma a ha k := by
    unfold jacobi.Bessel.edgeValue
    ring
  simp_rw [he] at hs
  exact Real.summable_log_one_add_of_summable hs

/-- The exponential of the genuine shifted logarithm series is the actual original normalized Bessel determinant on the full real shifted domain.
Use: shiftedMass_logDerivative identifies the same actual mass series with the original determinant's ordinary logarithmic derivative, without a product differentiation assumption.
Article: jacobi, Appendix E.1.
Proof: the positive original factors and the proved convergent logarithm series give their actual infinite product by the community exponential-product theorem. The independently proved original Bessel canonical product evaluates that same product at -w. -/
theorem shiftedLogDet_value (a:ℝ) (ha:-1<a) {w:ℝ}
    (hw: - jacobi.Bessel.sigma a ha 0<w) :
    exp (shiftedLogDet a ha w)= jacobi.Bessel.realNormalized a (-w) := by
  -- The canonical product is the already proved original Bessel product, not a new determinant definition.
  rw [shiftedLogDet,Real.rexp_tsum_eq_tprod (shiftedLogFactor_pos a ha hw) (shiftedLogFactor_summable a ha w)]
  calc
    _ = ∏'k,(1-(-w/2)* jacobi.Bessel.edgeValue a ha k) := by
      apply tprod_congr
      intro k
      unfold jacobi.Bessel.edgeValue
      ring
    _ = jacobi.Bessel.realNormalized a (2*(-w/2)) := jacobi.Bessel.real_canonical_product ha (-w/2)
    _ = _ := by congr 1; ring

/-- The actual shifted logarithmic determinant has derivative equal to half the original shifted mass throughout the full admissible real range.
Use: shiftedMass_logDerivative derives the source mass quotient from the actual convergent spectral series, including negative admissible shifts.
Article: jacobi, Appendix E.1.
Proof: retain half the true first-pole margin on a real neighborhood. Each logarithmic derivative is exactly 1/(sigma_k+x), at most the original center's shifted eigenvalue. That genuine center spectrum is summable. The community dominated-series differentiation theorem applies to the actual logarithm sum; factor the exact common 1/2 from its derivative series. -/
theorem shiftedLogDet_hasDerivAt (a:ℝ) (ha:-1<a) {w:ℝ}
    (hw: - jacobi.Bessel.sigma a ha 0<w) :
    HasDerivAt (shiftedLogDet a ha) (shiftedMass a ha w/2) w := by
  -- The first original spectral pole supplies one neighborhood for every summand simultaneously.
  let ε : ℝ := (jacobi.Bessel.sigma a ha 0+w)/2
  have hε : 0<ε := by dsimp [ε]; linarith
  have hwithin (x:ℝ) (hx:x∈Ioo (w-ε) (w+ε)) : - jacobi.Bessel.sigma a ha 0<x := by dsimp [ε] at hx; linarith [hx.1]
  have hd (k:ℕ) (x:ℝ) (hx:x∈Ioo (w-ε) (w+ε)) :
      HasDerivAt (fun v:ℝ => log (1+v/ jacobi.Bessel.sigma a ha k)) (1/(jacobi.Bessel.sigma a ha k+x)) x := by
    have hσ := jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k)
    have ht := (((hasDerivAt_id x).div_const (jacobi.Bessel.sigma a ha k)).const_add 1).log
      (shiftedLogFactor_pos a ha (hwithin x hx) k).ne'
    simp only [id_eq] at ht
    convert ht using 1
    field_simp [hσ.ne',(realShifted_denominator_pos a ha (hwithin x hx) k).ne']
  have hb (k:ℕ) (x:ℝ) (hx:x∈Ioo (w-ε) (w+ε)) :
      ‖1/(jacobi.Bessel.sigma a ha k+x)‖≤realShiftedEdge a ha w k := by
    have hσ := realShifted_denominator_pos a ha hw k
    have hxσ := realShifted_denominator_pos a ha (hwithin x hx) k
    have hmono := (jacobi.Bessel.sigma_strictMono ha).monotone (Nat.zero_le k)
    have hhalf : (jacobi.Bessel.sigma a ha k+w)/2≤ jacobi.Bessel.sigma a ha k+x := by dsimp [ε] at hx; linarith [hx.1]
    rw [Real.norm_eq_abs,abs_of_pos (by positivity : 0<1/(jacobi.Bessel.sigma a ha k+x))]
    calc
      _ ≤ 1/((jacobi.Bessel.sigma a ha k+w)/2) := one_div_le_one_div_of_le (by positivity) hhalf
      _ = _ := by unfold realShiftedEdge; field_simp
  have hwI : w∈Ioo (w-ε) (w+ε) := by constructor <;> linarith
  have ht := hasDerivAt_tsum_of_isPreconnected (realShiftedEdge_summable a ha hw)
    isOpen_Ioo isPreconnected_Ioo hd hb hwI (shiftedLogFactor_summable a ha w) hwI
  have he : (∑'k,1/(jacobi.Bessel.sigma a ha k+w))=shiftedMass a ha w/2 := by
    rw [shiftedMass,← tsum_div_const]
    apply tsum_congr
    intro k
    unfold realShiftedEdge
    ring
  rw [he] at ht
  exact ht

/-- The genuine shifted mass is exactly the logarithmic derivative of the original Bessel determinant on the full admissible real-shift interval.
Use: shiftedMass_quotient gives the printed adjacent-order modified-Bessel mass formula while preserving the actual spectral series and its full real domain.
Article: jacobi, Appendix E.1.
Proof: exponentiate the actual logarithm series with its proved derivative. Its value is locally the original determinant. Uniqueness of the genuine derivative identifies its logarithmic derivative with the actual Bessel slope. The determinant is positive by its exact exponential representation, so division is legitimate. -/
theorem shiftedMass_logDerivative (a:ℝ) (ha:-1<a) {w:ℝ}
    (hw: - jacobi.Bessel.sigma a ha 0<w) :
    shiftedMass a ha w= -2* jacobi.Bessel.realSlope a (-w)/ jacobi.Bessel.realNormalized a (-w) := by
  -- The local identity transfers a genuine derivative, rather than merely a pointwise product formula.
  have he : (fun x:ℝ => jacobi.Bessel.realNormalized a (-x))=ᶠ[𝓝 w] (fun x:ℝ => exp (shiftedLogDet a ha x)) := by
    filter_upwards [Ioi_mem_nhds hw] with x hx
    exact (shiftedLogDet_value a ha hx).symm
  have hd := ((shiftedLogDet_hasDerivAt a ha hw).exp).congr_of_eventuallyEq he
  have hB := (jacobi.Bessel.realNormalized_hasDerivAt a (-w)).comp w (hasDerivAt_id w).neg
  have hu := hd.unique hB
  rw [shiftedLogDet_value a ha hw] at hu
  have hpos : 0< jacobi.Bessel.realNormalized a (-w) := (shiftedLogDet_value a ha hw) ▸ exp_pos _
  apply (eq_div_iff hpos.ne').mpr
  nlinarith only [hu]

/-- The actual full shifted spectral mass has the original adjacent-order normalized Bessel quotient throughout w>-sigma_1, including w=0 and negative shifts.
Use: the off-edge variational calibrations can evaluate the genuine shifted mass in the printed special-function form without an assumed spectral-sum identity or a restriction to positive shifts.
Article: jacobi, Appendix E.1.
Source: the Bessel adjacent-order derivative identity, DLMF 10.6.2, already proved in Bessel.OrderShift from the genuine convergent series.
Proof: substitute the independently proved actual logarithmic-derivative formula. The exact genuine adjacent-order identity identifies its slope; its real restriction and elementary scalar cancellation give the displayed original quotient. -/
theorem shiftedMass_quotient (a:ℝ) (ha:-1<a) {w:ℝ}
    (hw: - jacobi.Bessel.sigma a ha 0<w) :
    shiftedMass a ha w= jacobi.Bessel.realNormalized (a+1) (-w)/
      (2*(a+1)* jacobi.Bessel.realNormalized a (-w)) := by
  -- Adjacent-order normalization is fixed by the original convergent Bessel series.
  have hsl : jacobi.Bessel.realSlope a (-w)=(-1/(4*(a+1)))* jacobi.Bessel.realNormalized (a+1) (-w) := by
    unfold jacobi.Bessel.realSlope jacobi.Bessel.realNormalized
    have he : (-1/(4*((a:ℂ)+1)):ℂ)=((-1/(4*(a+1)):ℝ):ℂ) := by push_cast; rfl
    have heA : (a:ℂ)+1=((a+1:ℝ):ℂ) := by push_cast; rfl
    rw [jacobi.Bessel.normalized_derivative_order_shift (by simpa using ha),he,heA]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [shiftedMass_logDerivative a ha hw,hsl]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end
end jacobi.EdgeResolvent
