import jacobi.Analytic.NormingFactors

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The explicit two-series majorant has a row sum bounded by a single
constant times the inverse square of the original index. These are
estimates of the literal continued factors, including every small index.
Use: establishes uniform absolute convergence of the original norming products.
-/
namespace jacobi.Analytic
noncomputable section
open jacobi.Reference

/-- The order-independent summable bound for the actual continued gap perturbations.
Use: establishes uniform absolute convergence of the original norming products.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def OrderDisk.normingMajorant {a0 : ℝ} (D : OrderDisk a0) (k l : ℕ) : ℝ :=
  (D.errorConstant/D.gapConstant)*(2/(l+1:ℝ)^2+3*distanceMajorant k l)/(k+1:ℝ)^2

/-- The explicit perturbation majorant is nonnegative at every pair of indices.
Use: finite products and infinite products have the same exponential row bound.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the spectral constants are positive and both inverse-square summands are nonnegative. -/
theorem OrderDisk.normingMajorant_nonneg {a0 : ℝ} (D : OrderDisk a0) (k l : ℕ) :
    0≤D.normingMajorant k l := by
  have hC := D.error_pos.le
  have hc := D.gap_pos.le
  unfold OrderDisk.normingMajorant distanceMajorant
  positivity

/-- Each actual uniform product majorant has a convergent row sum.
Use: applies the community infinite-product convergence and uniform convergence theorems.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the ordinary positive p-series and its translated counterpart are summable; take their fixed positive linear combination and divide by the row index square. -/
theorem OrderDisk.normingMajorant_summable {a0 : ℝ} (D : OrderDisk a0) (k : ℕ) :
    Summable (D.normingMajorant k) := by
  have hs : Summable (fun l : ℕ => 1/(l+1:ℝ)^2) := by
    simpa only [one_pow] using jacobi.Bessel.inverse_square_majorant_summable 1
  convert!
    (((hs.mul_left 2).add ((distanceMajorant_summable k).mul_left 3)).mul_left
      (D.errorConstant/D.gapConstant)).div_const ((k+1:ℝ)^2) using 1
  ext l
  simp only [OrderDisk.normingMajorant,mul_one_div]

/-- One positive constant bounds every full majorant row by the inverse square of its index.
Use: the actual norming-product error has exactly the required O(k^-2) order uniformly in complex order.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the translated inverse-square sum is at most twice the positive p-series, independently of its center. Summation of the two genuine majorant summands therefore gives the constant eight times their common spectral coefficient and the positive p-series sum. -/
theorem OrderDisk.normingMajorant_sum_bound {a0 : ℝ} (D : OrderDisk a0) :
    ∃ E : ℝ,0<E ∧ ∀ k : ℕ,(∑' l,D.normingMajorant k l)≤E/(k+1:ℝ)^2 := by
  -- The same index calculation as in the real proof controls the entire complex-order disk.
  have hs : Summable (fun l : ℕ => 1/(l+1:ℝ)^2) := by
    simpa only [one_pow] using jacobi.Bessel.inverse_square_majorant_summable 1
  let P : ℝ := ∑' l : ℕ,1/(l+1:ℝ)^2
  have hP : 0<P := by
    have hh := hs.le_tsum 0 (fun l _ => by positivity)
    exact zero_lt_one.trans_le (by simpa only [Nat.cast_zero,zero_add,one_pow,div_one] using hh)
  have hc : 0<D.errorConstant/D.gapConstant := div_pos D.error_pos D.gap_pos
  refine ⟨8*(D.errorConstant/D.gapConstant)*P,by positivity,fun k => ?_⟩
  have he : (∑' l,D.normingMajorant k l)=
      (D.errorConstant/D.gapConstant)*(2*P+3*(∑' l,distanceMajorant k l))/(k+1:ℝ)^2 := by
    change (∑' l : ℕ,(D.errorConstant/D.gapConstant)*
      (2/(l+1:ℝ)^2+3*distanceMajorant k l)/(k+1:ℝ)^2)=_
    simp_rw [← mul_one_div (2:ℝ)]
    rw [tsum_div_const,tsum_mul_left,(hs.mul_left 2).tsum_add ((distanceMajorant_summable k).mul_left 3)]
    simp only [tsum_mul_left,P]
  rw [he]
  have hh := distanceMajorant_tsum_le k
  change (∑' l,distanceMajorant k l)≤2*P at hh
  apply div_le_div_of_nonneg_right _ (sq_nonneg (k+1:ℝ))
  nlinarith [mul_le_mul_of_nonneg_left hh hc.le]

/-- The actual continued product-factor perturbations are absolutely summable at every point of the closed disk.
Use: the infinite product is a genuine limit rather than the default value of a divergent product.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: compare the actual factor norms with the proved summable order-independent majorant. -/
theorem OrderDisk.normingFactor_summable {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (ha : ‖a-(a0:ℂ)‖≤D.radius) (k : ℕ) :
    Summable (fun l => ‖D.normingFactor k l a-1‖) :=
  (D.normingMajorant_summable k).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun l => D.normingFactor_bound ha k l)

end
end jacobi.Analytic
